// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Trait interface for egraph implementations.
//!
//! This trait decouples the solver from a specific egraph implementation,
//! allowing different backends (e.g., the current Sundance egraph or the
//! semi-persistent egraph) to be used interchangeably.

use crate::egraphs::repr::{Pattern, PatternId};
use std::hash::Hash;
use yaspar_ir::ast::Local;

/// A SAT literal: positive means the variable is true, negative means false.
/// Zero means "no decision" when returned from decision methods.
pub type Lit = i32;

/// Conflict explanation: the equalities that were asserted (and their
/// congruence consequences) that together violate a disequality.
/// T is a generic parameter for the Term type that we use
#[derive(Debug, Clone)]
pub struct Conflict<T> {
    /// Equalities forming the proof path that made the two disequal terms equal.
    pub equalities: Vec<(T, T)>,
    /// The disequality that was violated.
    pub disequality: (T, T),
    /// The SAT literal that asserted the disequality (if one exists).
    pub diseq_lit: Option<Lit>,
}

/// Result of a mutating egraph operation (assert_equal, assert_disequal, etc.).
#[derive(Debug, Clone)]
pub struct EgraphResult<T> {
    /// A conflict, if the operation caused a disequality violation.
    pub conflict: Option<Conflict<T>>,
    /// SAT literals to propagate (from watched equalities that became true).
    /// This currently unused, but is useful for future optimizations
    pub propagations: Vec<Lit>,
}

impl<T> EgraphResult<T> {
    pub fn ok() -> Self {
        Self {
            conflict: None,
            propagations: Vec::new(),
        }
    }

    pub fn with_conflict(conflict: Conflict<T>) -> Self {
        Self {
            conflict: Some(conflict),
            propagations: Vec::new(),
        }
    }
}

pub trait EgraphTrait {
    /// Operator key for congruence: two terms are congruent iff they have
    /// the same Op and pairwise-equal children.
    type Op: Clone + Eq + Hash;

    /// Term identifier. Opaque to the egraph, provided by the solver.
    type TermId: Copy + Eq + Hash;

    // --- Registration ---

    /// Register a term with its operator and children.
    /// The egraph assigns and returns the TermId.
    /// If `dynamic` is true, finds and merges with existing congruent terms.
    fn register_term(
        &mut self,
        op: Self::Op,
        children: &[Self::TermId],
        dynamic: bool,
    ) -> Self::TermId;

    /// Register a constant (0-arity term).
    fn register_constant(&mut self, op: Self::Op) -> Self::TermId;

    /// Register an opaque term — participates in union-find but has no
    /// internal structure visible to congruence closure.
    fn register_opaque(&mut self) -> Self::TermId;

    /// Compile a pattern for e-matching and return its PatternId.
    fn compile_pattern(&mut self, pattern: Pattern<Self::TermId>) -> PatternId;

    /// Register an equality `t1 = t2` with its corresponding SAT literal.
    /// Sets up a watch: when `t1` and `t2` become equal, `lit` is propagated.
    /// When they become provably disequal, `-lit` is propagated.
    fn register_eq(&mut self, t1: Self::TermId, t2: Self::TermId, lit: Lit);

    /// Register a boolean non-equality term with its SAT literal.
    /// When the term becomes equal to `true_term`, `lit` is propagated.
    /// When it becomes equal to `false_term`, `-lit` is propagated.
    fn register_boolean_term(
        &mut self,
        op: Self::Op,
        children: &[Self::TermId],
        lit: Lit,
    ) -> Self::TermId;

    /// Tag `term`'s class as arithmetic. When incremental arithmetic is on,
    /// any merge (direct or congruence-derived) where either pre-merge root
    /// is tagged appends the merge to the arithmetic equality queue.
    fn mark_arithmetic(&mut self, term: Self::TermId);

    /// Enable/disable arithmetic equality collection.
    fn incremental_arithmetic(&mut self, enabled: bool);

    /// Drain arithmetic equalities produced by merges since the last drain.
    /// Callers must drain before advancing the decision level.
    fn drain_arithmetic_equalities(&mut self) -> Vec<(Self::TermId, Self::TermId)>;

    // --- Decision level ---

    /// Advance the internal decision level by one.
    fn notify_new_decision_level(&mut self);

    // --- Assertions ---

    /// Assert `t1 = t2` at the current decision level.
    /// Performs congruence closure. Returns a conflict if a disequality is violated.
    fn assert_equal(&mut self, t1: Self::TermId, t2: Self::TermId) -> EgraphResult<Self::TermId>;

    /// Assert `t1 ≠ t2` at the current decision level.
    /// `lit` is the SAT literal that caused this disequality (for conflict reporting).
    /// Returns a conflict if `t1` and `t2` are already in the same equivalence class.
    fn assert_disequal(
        &mut self,
        t1: Self::TermId,
        t2: Self::TermId,
        lit: Lit,
    ) -> EgraphResult<Self::TermId>;

    /// Assert all terms in `terms` are pairwise distinct at the current decision level.
    /// `lit` is the SAT literal for the distinct assertion.
    fn assert_distinct(&mut self, terms: &[Self::TermId], lit: Lit) -> EgraphResult<Self::TermId>;

    // --- Queries ---

    /// Find the canonical representative of a term's equivalence class.
    fn find(&self, term: Self::TermId) -> Self::TermId;

    /// Check if two terms are in the same equivalence class.
    fn are_equal(&self, t1: Self::TermId, t2: Self::TermId) -> bool;

    // --- E-matching ---

    /// Match a multi-trigger pattern.
    ///
    /// `trigger_term_pairs` is a list of (PatternId, optional_ground_term_hint).
    /// - `Some(t)` means the pattern must match in the same equivalence class as `t`
    /// - `None` means the pattern can match any term of the right function
    ///
    /// Returns a list of substitution maps (bound variable `Local` → matched term ID).
    fn match_triggers(
        &mut self,
        trigger_term_pairs: Vec<(PatternId, Option<Self::TermId>)>,
    ) -> Vec<crate::utils::DeterministicHashMap<Local, Self::TermId>>;

    // --- Backtracking ---

    /// Undo all operations performed at levels strictly greater than `level`.
    fn backtrack_to(&mut self, level: usize);

    // --- Decisions ---

    /// Relevancy-restricted branching (Z3 CASE_SPLIT=3 style): suggest an
    /// unassigned atom to decide next, with the phase that helps justify a
    /// relevant, not-yet-satisfied gate, plus the desired polarity resolved
    /// through the Boolean structure. Returns the atom's `TermId` and the
    /// phase (true = assign positive). `None` means no preference — let the
    /// SAT solver's own heuristic decide. Default: no preference.
    ///
    /// The caller maps the returned term to its SAT literal and is
    /// responsible for skipping a suggestion whose atom has no decision
    /// variable or is already assigned.
    fn suggest_decision(&self) -> Option<(Self::TermId, bool)> {
        None
    }

    /// SAT solver asks if the egraph wants to make a branching decision.
    /// Returns 0 if no preference, otherwise a signed literal to assign.
    fn make_decision(&self, assignments: &[i32]) -> i32;

    /// SAT solver has chosen a variable (unsigned), asks the egraph for polarity.
    /// Returns the signed literal (positive or negative).
    fn make_decision_lit(&self, lit: Lit, assignments: &[i32]) -> Lit;

    // --- Proofs ---

    /// Explain why `t1 = t2`. Returns the list of asserted equalities that
    /// form the proof. Returns None if `t1` and `t2` are not equal.
    fn explain_equality(
        &self,
        t1: Self::TermId,
        t2: Self::TermId,
    ) -> Option<Vec<(Self::TermId, Self::TermId)>>;
}
