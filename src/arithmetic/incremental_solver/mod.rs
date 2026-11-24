// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Trait for incremental arithmetic solvers. The propagator translates between
//! egraph ids / solver terms and the abstract VarId namespace defined here.

pub mod lira;
pub mod translation;
#[cfg(feature = "z3-solver")]
pub(crate) mod z3;

use crate::arithmetic::lia::variables::VarType;
use crate::arithmetic::lp::ArithValue;
use crate::utils::{DeterministicHashMap, DeterministicHashSet};
use dashu::Rational;

/// Opaque variable handle assigned by the solver via `register_var`.
pub type VarId = u32;

/// A linear expression: sum of (coeff * var) terms + constant + div/mod terms. Coefficients are
/// rational, as a `Real` expression may scale by a decimal or divide by a constant; `div`/`mod`
/// operands are always `Int` vars.
#[derive(Debug, Clone)]
pub struct ArithExpr {
    pub terms: Vec<(VarId, Rational)>,
    pub constant: Rational,
    pub divs: Vec<(VarId, VarId, Rational)>, // (numerator_var, denominator_var, coeff)
    pub mods: Vec<(VarId, VarId, Rational)>,
}

impl ArithExpr {
    /// A pure-linear expression from terms and a constant (no div/mod).
    pub fn linear<C: Into<Rational>>(
        terms: Vec<(VarId, C)>,
        constant: impl Into<Rational>,
    ) -> Self {
        Self {
            terms: terms.into_iter().map(|(v, c)| (v, c.into())).collect(),
            constant: constant.into(),
            divs: Vec::new(),
            mods: Vec::new(),
        }
    }

    /// A constant expression.
    pub fn constant(c: impl Into<Rational>) -> Self {
        Self::linear(Vec::<(VarId, Rational)>::new(), c)
    }

    /// The single-variable expression `1 * var`.
    pub fn var(var: VarId) -> Self {
        Self::linear(vec![(var, Rational::ONE)], Rational::ZERO)
    }
}

/// A constraint between two linear expressions.
#[derive(Debug, Clone)]
pub enum ArithConstraint {
    Leq(ArithExpr, ArithExpr),
    Lt(ArithExpr, ArithExpr),
    Eq(ArithExpr, ArithExpr),
}

/// Result of `check()`.
#[derive(Debug)]
pub enum ArithCheckResult {
    /// Conflict: negated SAT lits forming a clause.
    Unsat(Vec<i32>),
    /// Model value → set of VarIds assigned that value. The value includes the sort, so `Int`
    /// and `Real` vars never share a set.
    Sat(DeterministicHashMap<ArithValue, DeterministicHashSet<VarId>>),
    /// The solver gave up (e.g. a resource limit); no conflict and no model.
    Unknown,
}

/// Result of `check_partial_trail()`. `Unchanged` = impl skipped the check.
#[derive(Debug)]
pub enum PartialCheckResult {
    Unchanged,
    Sat,
    Unsat(Vec<i32>),
}

/// An incremental arithmetic solver that the propagator drives via
/// push/pop of constraints and equalities, keyed by solver-assigned VarIds.
pub trait IncrementalArithSolver {
    /// Register a fresh variable of sort `sort`. If `definition` is Some, the solver
    /// asserts `new_var == definition` at the current level. If `report_in_model`
    /// is true, this var's value is included in the model buckets on SAT.
    fn register_var(
        &mut self,
        sort: VarType,
        definition: Option<ArithExpr>,
        report_in_model: bool,
    ) -> VarId;

    /// Mark an already-registered var for model reporting. Idempotent.
    fn mark_model_var(&mut self, var: VarId);

    /// SAT solver advanced a decision level.
    fn notify_new_decision_level(&mut self);

    /// SAT solver backtracked to `level`. The solver must undo everything
    /// pushed at levels > `level`.
    fn notify_backtrack(&mut self, level: usize);

    /// Push a constraint (inequality or equality from the SAT trail) tracked
    /// by `lit`. The solver must be able to cite `lit` in its unsat core.
    fn push_constraint(&mut self, constraint: ArithConstraint, lit: i32);

    /// Push an equality `a == b` tracked by `lit`.
    fn push_equality(&mut self, a: VarId, b: VarId, lit: i32);

    /// Check satisfiability of all currently-pushed constraints + definitions.
    /// On SAT, only vars registered with `report_in_model=true` appear in buckets.
    fn check(&mut self) -> ArithCheckResult;

    /// Cheap feasibility check on the current trail — no model, no theory
    /// combination. Impls may return `Unchanged` to skip on their own policy.
    fn check_partial_trail(&mut self) -> PartialCheckResult;

    /// Whether `Sat` models are models of the registered terms. False once the solver has
    /// abstracted a term it does not interpret (e.g. an opaque `div`/`mod`): its conflicts are
    /// still valid, but a model it accepts may not satisfy the input.
    fn is_exact(&self) -> bool {
        true
    }
}
