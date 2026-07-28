// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Incremental frontend for the internal LRA solver.
//!
//! This module exposes an incremental, push/pop-driven API over the internal
//! [`LRASolver`], operating on an abstract [`VarId`] namespace rather than on
//! egraph ids or [`crate::solver_state::SolverState`]. It is the internal-solver
//! analogue of [`crate::arithmetic::z3incremental::Z3IncrementalState`]: a
//! persistent solver kept in sync with the SAT trail via decision-level push and
//! backtrack, with constraints tracked by SAT literal so they can be cited in an
//! unsat core.
//!
//! The functions here are shaped to eventually back an `IncrementalArithSolver`
//! trait implementation. The trait itself is intentionally *not* defined yet; the
//! data types ([`VarId`], [`ArithExpr`], [`ArithConstraint`], [`ArithCheckResult`])
//! mirror the anticipated trait so they can be lifted into it later.
//!
//! # How it maps onto the incremental [`LRASolver`]
//!
//! - Each registered variable and each pushed constraint's *slack* is an internal
//!   [`Var`]. A constraint `Σ aᵢ xᵢ ⋈ c` becomes a fresh slack row added to the
//!   live tableau via [`LRASolver::add_relation`], plus a bound on that slack
//!   asserted at the current decision level via
//!   [`LRASolver::assert_lower`]/[`LRASolver::assert_upper`].
//! - The tableau only ever grows (one row per pushed constraint). On backtrack the
//!   popped constraint's slack simply has its bound relaxed to `(−∞, +∞)` by the
//!   solver's bound trail — the row is never physically removed.
//! - Decision levels are tracked by capturing an [`LRASolver::set_backtrack`] token
//!   at each level boundary and replaying it via [`LRASolver::backtrack`].
//!
//! # Scope / limitations of this first frontend
//!
//! - **LRA (rational) reasoning only.** Registered variables are integer-sorted, but
//!   integrality is *not* enforced: [`IncrementalLraSolver::check`] may report `Sat`
//!   for a system that has no integer solution. Sound integer reasoning
//!   (branch-and-bound) is a later increment.
//! - **`div`/`mod` are unsupported.** An [`ArithExpr`] carrying `divs`/`mods` is
//!   rejected with an error; Euclidean-constraint lowering is a later increment.
//! - Model values are reported as [`IBig`] by truncating the rational assignment.

use crate::arithmetic::lia::context::ConvContext;
use crate::arithmetic::lia::linear_system::{Mon, Rel};
use crate::arithmetic::lia::lra_solver::LRASolver;
use crate::arithmetic::lia::solver_result::{SolverDecision, SolverError, SolverResult};
use crate::arithmetic::lia::tableau::TableauKind;
use crate::arithmetic::lia::types::Rational;
use crate::arithmetic::lia::variables::{Owner, Var, VarInfo};
use crate::debug_println;
use crate::utils::{DeterministicHashMap, DeterministicHashSet};
use dashu::integer::IBig;

/// Opaque variable handle assigned by the solver via
/// [`IncrementalLraSolver::register_var`].
pub type VarId = u32;

/// Constructor for a [`Rel`] from monomials and a constant (one of `Rel::mk_le`,
/// `mk_lt`, `mk_eq`), selected per [`ArithConstraint`] variant.
type RelMk = fn(Vec<Mon<Rational>>, Rational) -> Rel<Rational>;

/// A linear expression: sum of `coeff * var` terms plus a constant, with optional
/// `div`/`mod` terms (currently unsupported by this frontend).
#[derive(Debug, Clone)]
pub struct ArithExpr {
    /// `(var, coefficient)` pairs.
    pub terms: Vec<(VarId, IBig)>,
    /// Constant addend.
    pub constant: IBig,
    /// `(numerator_var, denominator_var, coeff)` division terms. Unsupported.
    pub divs: Vec<(VarId, VarId, IBig)>,
    /// `(numerator_var, denominator_var, coeff)` modulo terms. Unsupported.
    pub mods: Vec<(VarId, VarId, IBig)>,
}

impl ArithExpr {
    /// Construct a pure-linear expression from terms and a constant (no div/mod).
    pub fn linear(terms: Vec<(VarId, IBig)>, constant: IBig) -> Self {
        Self {
            terms,
            constant,
            divs: Vec::new(),
            mods: Vec::new(),
        }
    }

    /// Construct a constant expression.
    pub fn constant(c: impl Into<IBig>) -> Self {
        Self::linear(Vec::new(), c.into())
    }

    /// Return true if this expression uses div/mod terms (unsupported here).
    fn has_div_mod(&self) -> bool {
        !self.divs.is_empty() || !self.mods.is_empty()
    }
}

/// A constraint between two linear expressions.
#[derive(Debug, Clone)]
pub enum ArithConstraint {
    /// `lhs <= rhs`
    Leq(ArithExpr, ArithExpr),
    /// `lhs < rhs`
    Lt(ArithExpr, ArithExpr),
    /// `lhs == rhs`
    Eq(ArithExpr, ArithExpr),
}

/// Result of [`IncrementalLraSolver::check`].
#[derive(Debug)]
pub enum ArithCheckResult {
    /// Conflict: the conflict clause (negated asserted SAT literals), matching the
    /// shape expected by the propagator's existing unsat-core handling.
    Unsat(Vec<i32>),
    /// Satisfiable: model-value → the set of `report_in_model` [`VarId`]s assigned
    /// that (truncated integer) value.
    Sat(DeterministicHashMap<IBig, DeterministicHashSet<VarId>>),
}

/// Incremental LRA frontend: a persistent [`LRASolver`] driven by push/pop of
/// constraints keyed by SAT literal. See the module docs for the mapping onto the
/// incremental solver and the current limitations.
#[derive(Debug)]
pub struct IncrementalLraSolver {
    /// The persistent underlying solver. Seeded with one inert dummy row so the
    /// (sparse) tableau always exists and can be grown via `add_relation`.
    solver: LRASolver,
    /// Next fresh internal [`Var`] id (shared by registered vars and slacks).
    next_internal_id: usize,
    /// Next fresh [`VarId`] handed to callers.
    next_var_id: VarId,
    /// `VarId` → internal solver [`Var`].
    var_of: DeterministicHashMap<VarId, Var>,
    /// `VarId`s to include in the model buckets on `check` SAT.
    model_vars: DeterministicHashSet<VarId>,
    /// Constraint slack [`Var`] → the (negated) SAT literals to cite if that slack
    /// appears in a conflict. Definition rows are tautological and carry no lits.
    slack_to_lits: DeterministicHashMap<Var, Vec<i32>>,
    /// Current SAT decision level.
    sat_level: usize,
    /// `lra_tokens[l]` is the [`LRASolver::set_backtrack`] token captured at the
    /// `l → l+1` decision-level boundary; replayed by `notify_backtrack`.
    lra_tokens: Vec<usize>,
}

impl IncrementalLraSolver {
    /// Create a fresh incremental solver.
    pub fn new() -> Self {
        // Seed the solver with a single inert dummy relation `s = d` over two
        // unbounded variables, so the sparse tableau exists (a 0×0 tableau cannot be
        // constructed) and every real relation is added via `add_relation`. The dummy
        // slack/variable are unbounded, appear only in the dummy row, are never mapped
        // to a `VarId`, and so never affect feasibility or the reported model.
        let dummy_nonbasic = Var::int(0);
        let dummy_slack = Var::int(1);
        let basic = vec![VarInfo::new(dummy_slack, Owner::Basic(0))];
        let non_basic = vec![VarInfo::new(dummy_nonbasic, Owner::NonBasic(0))];
        let equations = vec![vec![Rational::ONE]];
        let solver = LRASolver::from_eqs(
            basic,
            non_basic,
            equations,
            ConvContext::new(),
            TableauKind::Sparse,
        )
        .expect("failed to build seed LRA solver");

        Self {
            solver,
            next_internal_id: 2, // ids 0 and 1 reserved for the dummy seed
            next_var_id: 0,
            var_of: DeterministicHashMap::new(),
            model_vars: DeterministicHashSet::default(),
            slack_to_lits: DeterministicHashMap::new(),
            sat_level: 0,
            lra_tokens: Vec::new(),
        }
    }

    /// Allocate a fresh internal integer [`Var`].
    fn fresh_var(&mut self) -> Var {
        let v = Var::int(self.next_internal_id);
        self.next_internal_id += 1;
        v
    }

    /// Register a fresh integer variable. If `definition` is `Some`, the equality
    /// `new_var == definition` is asserted at the current decision level. If
    /// `report_in_model` is true, the variable's value is included in the model
    /// buckets returned by [`Self::check`] on SAT.
    ///
    /// Returns an error if `definition` uses unsupported `div`/`mod` terms or refers
    /// to an unregistered variable.
    pub fn register_var(
        &mut self,
        definition: Option<ArithExpr>,
        report_in_model: bool,
    ) -> SolverResult<VarId> {
        let var_id = self.next_var_id;
        self.next_var_id += 1;
        let var = self.fresh_var();
        self.var_of.insert(var_id, var);
        if report_in_model {
            self.model_vars.insert(var_id);
        }

        if let Some(def) = definition {
            // Assert `new_var == def`, i.e. `new_var - def == 0`, as a fresh row. This
            // is tautological (new_var is fresh), so it is never needed in a conflict
            // core and is tracked with no literals.
            self.push_relation(
                ArithConstraint::Eq(
                    ArithExpr::linear(vec![(var_id, IBig::from(1))], IBig::from(0)),
                    def,
                ),
                None,
            )?;
        }

        Ok(var_id)
    }

    /// Mark an already-registered variable for model reporting. Idempotent.
    pub fn mark_model_var(&mut self, var: VarId) {
        self.model_vars.insert(var);
    }

    /// The SAT solver advanced to a new decision level.
    pub fn notify_new_decision_level(&mut self) {
        // If the previous `check` ended `Unsat`, clear it first: `set_backtrack` is a no-op
        // while `Unsat`, which would capture a stale token and skip the assignment backup.
        self.solver.clear_unsat_state();
        // Capture a backtrack token for the level we are leaving so a later
        // `notify_backtrack` can relax everything asserted above it.
        let token = self.solver.set_backtrack();
        self.lra_tokens.push(token);
        self.sat_level += 1;
        debug_println!(21, 0, "[lra-inc] new decision level {}", self.sat_level);
    }

    /// The SAT solver backtracked to `level`; undo everything pushed above it. The
    /// popped constraints' slacks are relaxed to `(−∞, +∞)` by the bound trail; the
    /// rows themselves persist (they are inert once unbounded).
    pub fn notify_backtrack(&mut self, level: usize) {
        if level >= self.sat_level {
            return;
        }
        // `lra_tokens[level]` is the token captured at the `level → level+1` boundary;
        // replaying it relaxes all bounds asserted at levels > `level`.
        let token = self.lra_tokens[level];
        self.solver.backtrack(token);
        self.lra_tokens.truncate(level);
        self.sat_level = level;
        debug_println!(21, 0, "[lra-inc] backtrack to level {}", level);
    }

    /// Push a constraint tracked by SAT literal `lit`. On conflict, `lit` (negated)
    /// is citable in the unsat core.
    ///
    /// Returns an error if either expression uses unsupported `div`/`mod` terms or
    /// refers to an unregistered variable.
    pub fn push_constraint(&mut self, constraint: ArithConstraint, lit: i32) -> SolverResult<()> {
        self.push_relation(constraint, Some(lit))
    }

    /// Push an equality `a == b` tracked by SAT literal `lit`.
    pub fn push_equality(&mut self, a: VarId, b: VarId, lit: i32) -> SolverResult<()> {
        let constraint = ArithConstraint::Eq(
            ArithExpr::linear(vec![(a, IBig::from(1))], IBig::from(0)),
            ArithExpr::linear(vec![(b, IBig::from(1))], IBig::from(0)),
        );
        self.push_relation(constraint, Some(lit))
    }

    /// Check satisfiability of all currently-pushed constraints and definitions.
    ///
    /// On `Sat`, only variables registered with `report_in_model` (or marked via
    /// [`Self::mark_model_var`]) appear in the buckets, keyed by their truncated
    /// integer model value. Variables that are unconstrained (never referenced by any
    /// pushed row) default to `0`.
    pub fn check(&mut self) -> ArithCheckResult {
        let decision = self
            .solver
            .solve()
            .expect("lra-inc: unexpected solver error")
            .decision;
        match decision {
            SolverDecision::FEASIBLE(assignment) => {
                let mut buckets: DeterministicHashMap<IBig, DeterministicHashSet<VarId>> =
                    DeterministicHashMap::new();
                for var_id in self.model_vars.iter() {
                    let var = self.var_of[var_id];
                    let value = assignment.get(&var).cloned().unwrap_or(Rational::ZERO);
                    let ibig = value.to_int().value().clone();
                    buckets.entry(ibig).or_default().insert(*var_id);
                }
                debug_println!(21, 0, "[lra-inc] SAT buckets={:?}", buckets);
                ArithCheckResult::Sat(buckets)
            }
            SolverDecision::INFEASIBLE(conflict) => {
                let lits: DeterministicHashSet<i32> = conflict
                    .iter()
                    .flat_map(|var| self.slack_to_lits.get(var).into_iter().flatten().copied())
                    .collect();
                debug_println!(21, 0, "[lra-inc] UNSAT core lits={:?}", lits);
                ArithCheckResult::Unsat(lits.into_iter().collect())
            }
            SolverDecision::UNKNOWN => {
                // Pure LRA `solve` terminates in FEASIBLE/INFEASIBLE; treat an
                // (unexpected) UNKNOWN conservatively as satisfiable, bucketing the
                // current best-effort assignment.
                let model = self.solver.get_rational_model().unwrap_or_default();
                let mut buckets: DeterministicHashMap<IBig, DeterministicHashSet<VarId>> =
                    DeterministicHashMap::new();
                for var_id in self.model_vars.iter() {
                    let var = self.var_of[var_id];
                    let value = model.get(&var).cloned().unwrap_or(Rational::ZERO);
                    let ibig = value.to_int().value().clone();
                    buckets.entry(ibig).or_default().insert(*var_id);
                }
                ArithCheckResult::Sat(buckets)
            }
        }
    }

    /// Look up the internal [`Var`] for a `VarId`, erroring if it was never registered.
    fn resolve(&self, var_id: VarId) -> SolverResult<Var> {
        self.var_of
            .get(&var_id)
            .copied()
            .ok_or_else(|| SolverError(format!("unregistered VarId {var_id}")))
    }

    /// Convert an [`ArithExpr`] to monomials with the given sign, erroring on
    /// unsupported div/mod terms or unregistered variables.
    fn expr_to_monomials(
        &self,
        expr: &ArithExpr,
        negate: bool,
    ) -> SolverResult<Vec<Mon<Rational>>> {
        if expr.has_div_mod() {
            return Err(SolverError(
                "div/mod terms are not supported by the incremental LRA frontend".to_string(),
            ));
        }
        let mut monomials = Vec::with_capacity(expr.terms.len());
        for (var_id, coeff) in &expr.terms {
            let var = self.resolve(*var_id)?;
            let mut c = Rational::from(coeff.clone());
            if negate {
                c = -c;
            }
            monomials.push(Mon::new(c, var));
        }
        Ok(monomials)
    }

    /// Core of `push_constraint`/`push_equality`/definitions: lower a constraint
    /// `lhs ⋈ rhs` to a fresh slack row `Σ aᵢ xᵢ ⋈ c` and assert the implied bound(s)
    /// at the current decision level. `lit` is `None` for tautological definitions.
    fn push_relation(&mut self, constraint: ArithConstraint, lit: Option<i32>) -> SolverResult<()> {
        // Normalize `lhs ⋈ rhs` to `(lhs.linear - rhs.linear) ⋈ (rhs.const - lhs.const)`.
        let (lhs, rhs, mk): (&ArithExpr, &ArithExpr, RelMk) = match &constraint {
            ArithConstraint::Leq(l, r) => (l, r, Rel::mk_le),
            ArithConstraint::Lt(l, r) => (l, r, Rel::mk_lt),
            ArithConstraint::Eq(l, r) => (l, r, Rel::mk_eq),
        };

        let mut terms = self.expr_to_monomials(lhs, false)?;
        terms.extend(self.expr_to_monomials(rhs, true)?);
        let rel_constant =
            Rational::from(rhs.constant.clone()) - Rational::from(lhs.constant.clone());
        let rel = mk(terms, rel_constant);

        // Derive the QDelta bound(s) (handles strict-inequality δ adjustment) before
        // the relation is moved into `add_relation`.
        let bounds = rel.to_qdelta_bounds();

        let slack = self.fresh_var();
        self.solver.add_relation(rel, slack)?;

        if let Some(lower) = bounds.lower {
            self.solver.assert_lower(&slack, &lower)?;
        }
        if let Some(upper) = bounds.upper {
            self.solver.assert_upper(&slack, &upper)?;
        }

        // Record the justification so the slack can be cited in a conflict. Constraints
        // store the (negated) tracking lit, matching the existing unsat-core convention;
        // definitions are tautological and store nothing.
        if let Some(lit) = lit {
            self.slack_to_lits.insert(slack, vec![-lit]);
        }
        Ok(())
    }
}

impl Default for IncrementalLraSolver {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: linear expr `coeff * var`.
    fn term(var: VarId, coeff: i32) -> ArithExpr {
        ArithExpr::linear(vec![(var, IBig::from(coeff))], IBig::from(0))
    }

    fn is_sat(r: &ArithCheckResult) -> bool {
        matches!(r, ArithCheckResult::Sat(_))
    }

    #[test]
    fn empty_system_is_sat() {
        let mut s = IncrementalLraSolver::new();
        assert!(is_sat(&s.check()));
    }

    #[test]
    fn single_feasible_constraint() {
        let mut s = IncrementalLraSolver::new();
        let x = s.register_var(None, true).unwrap();
        // x <= 5
        s.push_constraint(ArithConstraint::Leq(term(x, 1), ArithExpr::constant(5)), 10)
            .unwrap();
        assert!(is_sat(&s.check()));
    }

    #[test]
    fn conflicting_constraints_are_unsat_with_core() {
        let mut s = IncrementalLraSolver::new();
        let x = s.register_var(None, true).unwrap();
        // x >= 5 (encoded as 5 <= x), lit 10
        s.push_constraint(ArithConstraint::Leq(ArithExpr::constant(5), term(x, 1)), 10)
            .unwrap();
        // x <= 1, lit 20
        s.push_constraint(ArithConstraint::Leq(term(x, 1), ArithExpr::constant(1)), 20)
            .unwrap();
        match s.check() {
            ArithCheckResult::Unsat(core) => {
                // Both tracking lits (negated) should appear in the conflict clause.
                assert!(core.contains(&-10), "core {core:?} missing -10");
                assert!(core.contains(&-20), "core {core:?} missing -20");
            }
            ArithCheckResult::Sat(_) => panic!("expected UNSAT"),
        }
    }

    #[test]
    fn backtrack_recovers_from_conflict() {
        let mut s = IncrementalLraSolver::new();
        let x = s.register_var(None, true).unwrap();
        // Level 0: x >= 5.
        s.push_constraint(ArithConstraint::Leq(ArithExpr::constant(5), term(x, 1)), 10)
            .unwrap();
        assert!(is_sat(&s.check()));

        // Level 1: add x <= 1, making the system infeasible.
        s.notify_new_decision_level();
        s.push_constraint(ArithConstraint::Leq(term(x, 1), ArithExpr::constant(1)), 20)
            .unwrap();
        assert!(matches!(s.check(), ArithCheckResult::Unsat(_)));

        // Backtrack to level 0: the x <= 1 bound is relaxed and the system is feasible.
        s.notify_backtrack(0);
        assert!(is_sat(&s.check()));
    }

    #[test]
    fn definition_is_enforced_in_model() {
        let mut s = IncrementalLraSolver::new();
        let x = s.register_var(None, true).unwrap();
        // y := x + 3
        let y = s
            .register_var(
                Some(ArithExpr::linear(vec![(x, IBig::from(1))], IBig::from(3))),
                true,
            )
            .unwrap();
        // Pin x == 4, so y must be 7.
        s.push_constraint(ArithConstraint::Eq(term(x, 1), ArithExpr::constant(4)), 10)
            .unwrap();
        match s.check() {
            ArithCheckResult::Sat(buckets) => {
                // x is 4, y is 7.
                assert!(buckets.get(&IBig::from(4)).unwrap().contains(&x));
                assert!(buckets.get(&IBig::from(7)).unwrap().contains(&y));
            }
            ArithCheckResult::Unsat(_) => panic!("expected SAT"),
        }
    }

    #[test]
    fn equality_constraint_ties_two_vars() {
        let mut s = IncrementalLraSolver::new();
        let x = s.register_var(None, true).unwrap();
        let y = s.register_var(None, true).unwrap();
        // x == y (via push_equality), and x == 9.
        s.push_equality(x, y, 10).unwrap();
        s.push_constraint(ArithConstraint::Eq(term(x, 1), ArithExpr::constant(9)), 20)
            .unwrap();
        match s.check() {
            ArithCheckResult::Sat(buckets) => {
                let nine = buckets.get(&IBig::from(9)).unwrap();
                assert!(nine.contains(&x) && nine.contains(&y));
            }
            ArithCheckResult::Unsat(_) => panic!("expected SAT"),
        }
    }

    #[test]
    fn strict_inequality_conflict() {
        let mut s = IncrementalLraSolver::new();
        let x = s.register_var(None, true).unwrap();
        // x < 3 and x > 3 (encoded as 3 < x): infeasible.
        s.push_constraint(ArithConstraint::Lt(term(x, 1), ArithExpr::constant(3)), 10)
            .unwrap();
        s.push_constraint(ArithConstraint::Lt(ArithExpr::constant(3), term(x, 1)), 20)
            .unwrap();
        assert!(matches!(s.check(), ArithCheckResult::Unsat(_)));
    }

    #[test]
    fn model_only_reports_marked_vars() {
        let mut s = IncrementalLraSolver::new();
        let reported = s.register_var(None, true).unwrap();
        let hidden = s.register_var(None, false).unwrap();
        s.push_constraint(
            ArithConstraint::Eq(term(reported, 1), ArithExpr::constant(1)),
            10,
        )
        .unwrap();
        s.push_constraint(
            ArithConstraint::Eq(term(hidden, 1), ArithExpr::constant(2)),
            20,
        )
        .unwrap();
        match s.check() {
            ArithCheckResult::Sat(buckets) => {
                let all_reported: DeterministicHashSet<VarId> =
                    buckets.values().flatten().copied().collect();
                assert!(all_reported.contains(&reported));
                assert!(!all_reported.contains(&hidden));
            }
            ArithCheckResult::Unsat(_) => panic!("expected SAT"),
        }
        // mark_model_var makes the hidden var appear.
        s.mark_model_var(hidden);
        match s.check() {
            ArithCheckResult::Sat(buckets) => {
                assert!(buckets.get(&IBig::from(2)).unwrap().contains(&hidden));
            }
            ArithCheckResult::Unsat(_) => panic!("expected SAT"),
        }
    }

    #[test]
    fn nested_levels_backtrack_partially() {
        let mut s = IncrementalLraSolver::new();
        let x = s.register_var(None, true).unwrap();
        // L0: x >= 0.
        s.push_constraint(ArithConstraint::Leq(ArithExpr::constant(0), term(x, 1)), 10)
            .unwrap();
        // L1: x <= 10.
        s.notify_new_decision_level();
        s.push_constraint(
            ArithConstraint::Leq(term(x, 1), ArithExpr::constant(10)),
            20,
        )
        .unwrap();
        assert!(is_sat(&s.check()));
        // L2: x <= -1, contradicts x >= 0.
        s.notify_new_decision_level();
        s.push_constraint(
            ArithConstraint::Leq(term(x, 1), ArithExpr::constant(-1)),
            30,
        )
        .unwrap();
        assert!(matches!(s.check(), ArithCheckResult::Unsat(_)));
        // Backtrack to L1: x <= -1 relaxed, but x <= 10 still active. Feasible.
        s.notify_backtrack(1);
        assert!(is_sat(&s.check()));
    }

    #[test]
    fn div_mod_expr_is_rejected() {
        let mut s = IncrementalLraSolver::new();
        let x = s.register_var(None, true).unwrap();
        let d = s.register_var(None, false).unwrap();
        let expr = ArithExpr {
            terms: vec![],
            constant: IBig::from(0),
            divs: vec![(x, d, IBig::from(1))],
            mods: vec![],
        };
        assert!(
            s.push_constraint(ArithConstraint::Leq(expr, ArithExpr::constant(0)), 10)
                .is_err()
        );
    }

    #[test]
    fn unregistered_var_is_rejected() {
        let mut s = IncrementalLraSolver::new();
        // VarId 99 was never registered.
        assert!(
            s.push_constraint(
                ArithConstraint::Leq(term(99, 1), ArithExpr::constant(0)),
                10
            )
            .is_err()
        );
    }
}
