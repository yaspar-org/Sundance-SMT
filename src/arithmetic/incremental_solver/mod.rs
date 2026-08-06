// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Trait for incremental arithmetic solvers. The propagator translates between
//! egraph ids / solver terms and the abstract VarId namespace defined here.

pub mod translation;
#[cfg(feature = "z3-solver")]
pub mod z3;

use crate::utils::{DeterministicHashMap, DeterministicHashSet};
use dashu::integer::IBig;

/// Opaque variable handle assigned by the solver via `register_var`.
pub type VarId = u32;

/// A linear expression: sum of (coeff * var) terms + constant + div/mod terms.
#[derive(Debug, Clone)]
pub struct ArithExpr {
    pub terms: Vec<(VarId, IBig)>,
    pub constant: IBig,
    pub divs: Vec<(VarId, VarId, IBig)>, // (numerator_var, denominator_var, coeff)
    pub mods: Vec<(VarId, VarId, IBig)>,
}

/// A constraint between two linear expressions.
#[derive(Debug, Clone)]
pub enum ArithConstraint {
    Leq(ArithExpr, ArithExpr),
    Lt(ArithExpr, ArithExpr),
    Eq(ArithExpr, ArithExpr),
}

/// Result of `check()`.
pub enum ArithCheckResult {
    /// Conflict: negated SAT lits forming a clause.
    Unsat(Vec<i32>),
    /// Model-value → set of VarIds assigned that value.
    Sat(DeterministicHashMap<IBig, DeterministicHashSet<VarId>>),
}

/// An incremental arithmetic solver that the propagator drives via
/// push/pop of constraints and equalities, keyed by solver-assigned VarIds.
pub trait IncrementalArithSolver {
    /// Register a fresh integer variable. If `definition` is Some, the solver
    /// asserts `new_var == definition` at the current level. If `report_in_model`
    /// is true, this var's value is included in the model buckets on SAT.
    fn register_var(&mut self, definition: Option<ArithExpr>, report_in_model: bool) -> VarId;

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
}
