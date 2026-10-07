// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Internal-solver implementation of [`IncrementalArithSolver`].
//!
//! A persistent [`LIRASolver`] kept in sync with the SAT trail via decision-level push and
//! backtrack, with constraints tracked by SAT literal so they can be cited in an unsat core. It
//! is the internal-solver analogue of [`crate::arithmetic::incremental_solver`]'s Z3 backend.
//!
//! How it maps onto the incremental [`LRASolver`]
//!
//! - Each [`VarId`] denotes an affine form over internal [`Var`]s. A free variable is a fresh
//!   internal var; a variable registered with a definition *is* its (substituted) definition.
//!   Definitions therefore add no rows or bounds and hold at every decision level. This matters
//!   because [`crate::arithmetic::incremental_solver::translation::ArithTranslator`] registers a
//!   term's `VarId` once and never re-registers it after a backtrack.
//! - A pushed constraint `Σ aᵢ xᵢ ⋈ c` becomes a fresh slack row added to the live tableau via
//!   [`LRASolver::add_relation`], plus a bound on that slack asserted at the current decision
//!   level. The tableau only ever grows; on backtrack the slack's bound is relaxed to
//!   `(−∞, +∞)` by the solver's bound trail and the row stays (inert once unbounded).
//! - Decision levels are tracked by capturing an [`LRASolver::set_backtrack`] token at each level
//!   boundary and replaying it via [`LRASolver::backtrack`].
//! - **`div`/`mod` require a constant divisor**, resolved from the denominator's affine form.
//!   `div(a, n)` is a quotient var `q`, shared per `(a, n)`, constrained by the single row
//!   `0 ≤ a − n·q ≤ |n| − 1`; `mod(a, n) = a − n·q`. That row is definitional, so its bounds are
//!   *permanent*: they cite no literal and are re-asserted whenever a backtrack relaxes them.
//! - **Integer reasoning is enforced** via the [`LIRASolver`]'s branch-and-bound;
//!   [`IncrementalArithSolver::check_partial_trail`] only checks the rational relaxation, which is
//!   sound for conflicts.

use crate::arithmetic::incremental_solver::{
    ArithCheckResult, ArithConstraint, ArithExpr, IncrementalArithSolver, PartialCheckResult, VarId,
};
use crate::arithmetic::lia::bounds::Bounds;
use crate::arithmetic::lia::config::SolverConfig;
use crate::arithmetic::lia::context::ConvContext;
use crate::arithmetic::lia::linear_system::{Mon, Rel};
use crate::arithmetic::lia::lira_solver::LIRASolver;
use crate::arithmetic::lia::lra_solver::LRASolver;
use crate::arithmetic::lia::qdelta::QDelta;
use crate::arithmetic::lia::solver_result::{Conflict, SolverDecision, SolverError, SolverResult};
use crate::arithmetic::lia::tableau::TableauKind;
use crate::arithmetic::lia::types::Rational;
use crate::arithmetic::lia::variables::{Owner, Var, VarInfo};
use crate::debug_println;
use crate::utils::{DeterministicHashMap, DeterministicHashSet};
use dashu::integer::IBig;

/// Min new constraints before `check_partial_trail` actually runs simplex.
const PARTIAL_CHECK_ASSERTION_BATCH: usize = 32;

/// Constructor for a [`Rel`] from monomials and a constant (one of `Rel::mk_le`, `mk_lt`,
/// `mk_eq`), selected per [`ArithConstraint`] variant.
type RelMk = fn(Vec<Mon<Rational>>, Rational) -> Rel<Rational>;

/// An affine form `Σ cᵢ vᵢ + constant` over internal [`Var`]s, kept combined (no zero
/// coefficients).
#[derive(Debug, Clone)]
struct Affine {
    terms: DeterministicHashMap<Var, IBig>,
    constant: IBig,
}

impl Affine {
    fn constant(c: IBig) -> Self {
        Self {
            terms: DeterministicHashMap::new(),
            constant: c,
        }
    }

    fn var(v: Var) -> Self {
        let mut a = Self::constant(IBig::ZERO);
        a.add_term(v, &IBig::ONE);
        a
    }

    /// `self += k * v`.
    fn add_term(&mut self, v: Var, k: &IBig) {
        let c = self.terms.entry(v).or_insert(IBig::ZERO);
        *c += k;
        if *c == IBig::ZERO {
            self.terms.remove(&v);
        }
    }

    /// `self += k * other`.
    fn add_scaled(&mut self, other: &Affine, k: &IBig) {
        for (v, c) in &other.terms {
            self.add_term(*v, &(k * c));
        }
        self.constant += k * &other.constant;
    }

    fn as_constant(&self) -> Option<&IBig> {
        self.terms.is_empty().then_some(&self.constant)
    }

    fn monomials(&self) -> Vec<Mon<Rational>> {
        self.terms
            .iter()
            .map(|(v, c)| Mon::new(Rational::from(c.clone()), *v))
            .collect()
    }

    fn eval(&self, value: impl Fn(&Var) -> Rational) -> Rational {
        let mut acc = Rational::from(self.constant.clone());
        for (v, c) in &self.terms {
            acc += Rational::from(c.clone()) * value(v);
        }
        acc
    }
}

/// Incremental LIRA backend: a persistent [`LIRASolver`] driven by push/pop of constraints keyed
/// by SAT literal. See the module docs for the mapping onto the inner LIRA solver.
#[derive(Debug)]
pub struct LiraIncrementalState {
    /// The persistent underlying solver
    solver: LIRASolver,
    /// Next fresh internal [`Var`] id (shared by free vars, quotients and slacks).
    next_internal_id: usize,
    /// `VarId` → its affine form over internal vars.
    defs: Vec<Affine>,
    /// `VarId`s to include in the model buckets on `check` SAT.
    model_vars: DeterministicHashSet<VarId>,
    /// `(numerator, divisor)` → quotient var of `div(numerator, divisor)`.
    quotients: DeterministicHashMap<(VarId, IBig), Var>,
    /// Constraint slack → the negated SAT literal to cite if that slack appears in a conflict.
    /// Permanent (definitional) slacks carry no literal.
    slack_to_lit: DeterministicHashMap<Var, i32>,
    /// Literals whose constraint is currently asserted (re-pushes are no-ops).
    active_lits: DeterministicHashSet<i32>,
    /// `lits_by_level[l]`: literals pushed at decision level `l`.
    lits_by_level: Vec<Vec<i32>>,
    /// `permanent_by_level[l]`: permanent bounds whose trail entry lives at level `l`; re-asserted
    /// at the surviving level when a backtrack relaxes them.
    permanent_by_level: Vec<Vec<(Var, Bounds<QDelta>)>>,
    /// Current SAT decision level.
    sat_level: usize,
    /// `lra_tokens[l]` is the [`LRASolver::set_backtrack`] token captured at the `l → l+1`
    /// decision-level boundary; replayed by `notify_backtrack`.
    lra_tokens: Vec<usize>,
    /// Constraints pushed since the last (partial or full) check.
    pending_partial: usize,
}

impl LiraIncrementalState {
    /// Create a fresh incremental solver with the default [`SolverConfig`].
    pub fn new() -> Self {
        Self::with_config(SolverConfig::default())
    }

    /// Create a fresh incremental solver, using `config` for the underlying [`LIRASolver`]
    /// (e.g. to bound `max_branch_depth` / `max_lra_solve_calls`).
    pub fn with_config(config: SolverConfig) -> Self {
        // Seed the solver with a single inert dummy relation `s = d` over two unbounded
        // variables, so the sparse tableau exists (a 0×0 tableau cannot be constructed) and every
        // real relation is added via `add_relation`. The dummy slack/variable are unbounded,
        // appear only in the dummy row, are never mapped to a `VarId`, and so never affect
        // feasibility or the reported model.
        let dummy_nonbasic = Var::int(0);
        let dummy_slack = Var::int(1);
        let basic = vec![VarInfo::new(dummy_slack, Owner::Basic(0))];
        let non_basic = vec![VarInfo::new(dummy_nonbasic, Owner::NonBasic(0))];
        let equations = vec![vec![Rational::ONE]];
        let lra_solver = LRASolver::from_eqs(
            basic,
            non_basic,
            equations,
            ConvContext::new(),
            TableauKind::Sparse,
        )
        .expect("failed to build seed LRA solver");
        let solver = LIRASolver::new(lra_solver, config);

        Self {
            solver,
            next_internal_id: 2, // ids 0 and 1 reserved for the dummy seed
            defs: Vec::new(),
            model_vars: DeterministicHashSet::default(),
            quotients: DeterministicHashMap::new(),
            slack_to_lit: DeterministicHashMap::new(),
            active_lits: DeterministicHashSet::default(),
            lits_by_level: vec![Vec::new()],
            permanent_by_level: vec![Vec::new()],
            sat_level: 0,
            lra_tokens: Vec::new(),
            pending_partial: 0,
        }
    }

    /// Allocate a fresh internal integer [`Var`].
    fn fresh_var(&mut self) -> Var {
        let v = Var::int(self.next_internal_id);
        self.next_internal_id += 1;
        v
    }

    /// The affine form of a `VarId`, erroring if it was never registered.
    fn def(&self, var_id: VarId) -> SolverResult<&Affine> {
        self.defs
            .get(var_id as usize)
            .ok_or_else(|| SolverError(format!("unregistered VarId {var_id}")))
    }

    /// Resolve a `div`/`mod` denominator to its constant, erroring if it is not constant or zero.
    fn resolve_divisor(&self, denom: VarId) -> SolverResult<IBig> {
        match self.def(denom)?.as_constant() {
            Some(n) if *n != IBig::ZERO => Ok(n.clone()),
            Some(_) => Err(SolverError("div/mod by zero".to_string())),
            None => Err(SolverError(format!(
                "div/mod divisor VarId {denom} is not a constant"
            ))),
        }
    }

    /// The quotient var `q = div(a, n)`, created on first use together with its permanent
    /// Euclidean row `0 ≤ a − n·q ≤ |n| − 1`.
    fn quotient(&mut self, a: VarId, n: &IBig) -> SolverResult<Var> {
        if let Some(q) = self.quotients.get(&(a, n.clone())) {
            return Ok(*q);
        }
        let q = self.fresh_var();
        // r = a − n·q, as an affine form; the row's slack is r minus its constant part.
        let mut r = self.def(a)?.clone();
        r.add_term(q, &-n);
        let abs_n = if *n < IBig::ZERO { -n } else { n.clone() };
        let lower = Rational::from(-&r.constant);
        let upper = Rational::from(abs_n - IBig::ONE - &r.constant);
        let bounds = Bounds::new(Some(lower.into()), Some(upper.into()));
        self.add_row(r.monomials(), bounds, None)?;
        self.quotients.insert((a, n.clone()), q);
        Ok(q)
    }

    /// Convert an [`ArithExpr`] to an affine form, substituting variable definitions and
    /// converting `div`/`mod` terms to quotient vars.
    fn expr_to_affine(&mut self, expr: &ArithExpr) -> SolverResult<Affine> {
        let mut out = Affine::constant(expr.constant.clone());
        for (var_id, coeff) in &expr.terms {
            let def = self.def(*var_id)?.clone();
            out.add_scaled(&def, coeff);
        }
        for (a, b, coeff) in &expr.divs {
            let n = self.resolve_divisor(*b)?;
            let q = self.quotient(*a, &n)?;
            // div(a, n) = q
            out.add_term(q, coeff);
        }
        for (a, b, coeff) in &expr.mods {
            let n = self.resolve_divisor(*b)?;
            let q = self.quotient(*a, &n)?;
            // mod(a, n) = a − n·q
            let def = self.def(*a)?.clone();
            out.add_scaled(&def, coeff);
            out.add_term(q, &-(coeff * &n));
        }
        Ok(out)
    }

    /// Assert `bounds` on `slack` at the current decision level.
    fn assert_bounds(&mut self, slack: Var, bounds: &Bounds<QDelta>) -> SolverResult<()> {
        let lra = self.solver.lra_solver_mut();
        // `Some(false)` (crossing an existing opposite bound) cannot happen: every slack is
        // fresh, carries exactly one constraint's bounds, and those are consistent.
        if let Some(lower) = &bounds.lower {
            let r = lra.assert_lower(&slack, lower)?;
            debug_assert_ne!(r, Some(false), "lower bound crossed on fresh slack");
        }
        if let Some(upper) = &bounds.upper {
            let r = lra.assert_upper(&slack, upper)?;
            debug_assert_ne!(r, Some(false), "upper bound crossed on fresh slack");
        }
        Ok(())
    }

    /// Add a fresh slack row `slack = Σ terms` to the tableau and assert `bounds` on it at the
    /// current level. With `lit` the slack is citable in a conflict; without, the bounds are
    /// permanent (re-asserted after any backtrack that relaxes them).
    fn add_row(
        &mut self,
        terms: Vec<Mon<Rational>>,
        bounds: Bounds<QDelta>,
        lit: Option<i32>,
    ) -> SolverResult<()> {
        let slack = self.fresh_var();
        // `add_relation` only reads the relation's terms; the bounds are asserted separately.
        self.solver
            .lra_solver_mut()
            .add_relation(Rel::mk_eq(terms, Rational::ZERO), slack)?;
        self.assert_bounds(slack, &bounds)?;
        match lit {
            Some(lit) => {
                self.slack_to_lit.insert(slack, -lit);
            }
            None => self.permanent_by_level[self.sat_level].push((slack, bounds)),
        }
        Ok(())
    }

    /// Register a fresh integer variable; see [`IncrementalArithSolver::register_var`]. Errors if
    /// `definition` refers to an unregistered variable or a non-constant/zero `div`/`mod` divisor.
    pub fn try_register_var(
        &mut self,
        definition: Option<ArithExpr>,
        report_in_model: bool,
    ) -> SolverResult<VarId> {
        let affine = match definition {
            Some(def) => self.expr_to_affine(&def)?,
            None => {
                let v = self.fresh_var();
                Affine::var(v)
            }
        };
        let var_id = self.defs.len() as VarId;
        self.defs.push(affine);
        if report_in_model {
            self.model_vars.insert(var_id);
        }
        Ok(var_id)
    }

    /// Push a constraint tracked by SAT literal `lit`; see
    /// [`IncrementalArithSolver::push_constraint`]. Errors if either side refers to an
    /// unregistered variable or a non-constant/zero `div`/`mod` divisor.
    pub fn try_push_constraint(
        &mut self,
        constraint: ArithConstraint,
        lit: i32,
    ) -> SolverResult<()> {
        if self.active_lits.contains(&lit) {
            return Ok(());
        }
        // Normalize `lhs ⋈ rhs` to `(lhs − rhs).terms ⋈ −(lhs − rhs).constant`.
        let (lhs, rhs, mk): (&ArithExpr, &ArithExpr, RelMk) = match &constraint {
            ArithConstraint::Leq(l, r) => (l, r, Rel::mk_le),
            ArithConstraint::Lt(l, r) => (l, r, Rel::mk_lt),
            ArithConstraint::Eq(l, r) => (l, r, Rel::mk_eq),
        };
        let mut diff = self.expr_to_affine(lhs)?;
        let rhs = self.expr_to_affine(rhs)?;
        diff.add_scaled(&rhs, &-IBig::ONE);
        let c = Rational::from(-&diff.constant);

        self.active_lits.insert(lit);
        self.lits_by_level[self.sat_level].push(lit);

        // A constraint with no variables left is decided by its constant. A true one needs no
        // row; a false one still gets its (all-zero) row, which simplex reports infeasible
        // citing `lit`.
        if diff.terms.is_empty() {
            let holds = match constraint {
                ArithConstraint::Leq(..) => Rational::ZERO <= c,
                ArithConstraint::Lt(..) => Rational::ZERO < c,
                ArithConstraint::Eq(..) => Rational::ZERO == c,
            };
            if holds {
                return Ok(());
            }
        }

        // Derive the QDelta bound(s) (handles strict-inequality δ adjustment).
        let rel = mk(diff.monomials(), c);
        let bounds = rel.to_qdelta_bounds();
        self.add_row(rel.terms_ref().to_vec(), bounds, Some(lit))?;
        self.pending_partial += 1;
        debug_println!(
            21,
            0,
            "[lira-inc] pushed constraint lit={} at level {}",
            lit,
            self.sat_level
        );
        Ok(())
    }

    /// Model buckets over `model_vars`, reading internal values via `value`.
    fn model_buckets(
        &self,
        value: impl Fn(&Var) -> Rational,
    ) -> DeterministicHashMap<IBig, DeterministicHashSet<VarId>> {
        let mut buckets: DeterministicHashMap<IBig, DeterministicHashSet<VarId>> =
            DeterministicHashMap::new();
        for var_id in &self.model_vars {
            let v = self.defs[*var_id as usize].eval(&value);
            buckets
                .entry(v.to_int().value().clone())
                .or_default()
                .insert(*var_id);
        }
        buckets
    }

    /// The conflict clause (negated tracking lits) for a conflict over internal vars.
    fn conflict_clause(&self, conflict: &Conflict<Var>) -> Vec<i32> {
        let lits: DeterministicHashSet<i32> = conflict
            .iter()
            .filter_map(|var| self.slack_to_lit.get(var).copied())
            .collect();
        assert!(
            !lits.is_empty(),
            "lira-inc: empty unsat core (definitional rows alone are contradictory)"
        );
        lits.into_iter().collect()
    }

    /// Check all currently-pushed constraints; see [`IncrementalArithSolver::check`].
    ///
    /// Variables that are unconstrained (never referenced by any row) default to `0`.
    pub fn try_check(&mut self) -> SolverResult<ArithCheckResult> {
        self.pending_partial = 0;
        let decision = self.solver.solve()?.decision;
        Ok(match decision {
            SolverDecision::FEASIBLE(assignment) => {
                let buckets =
                    self.model_buckets(|v| assignment.get(v).cloned().unwrap_or(Rational::ZERO));
                debug_println!(21, 0, "[lira-inc] SAT buckets={:?}", buckets);
                ArithCheckResult::Sat(buckets)
            }
            SolverDecision::INFEASIBLE(conflict) => {
                let clause = self.conflict_clause(&conflict);
                debug_println!(21, 0, "[lira-inc] UNSAT core={:?}", clause);
                ArithCheckResult::Unsat(clause)
            }
            // Branch-and-bound hit its resource limits (`max_branch_depth` /
            // `max_lra_solve_calls`).
            SolverDecision::UNKNOWN => ArithCheckResult::Unknown,
        })
    }

    /// Check the rational relaxation only; see [`IncrementalArithSolver::check_partial_trail`].
    pub fn try_check_partial_trail(&mut self) -> SolverResult<PartialCheckResult> {
        if self.pending_partial < PARTIAL_CHECK_ASSERTION_BATCH {
            return Ok(PartialCheckResult::Unchanged);
        }
        self.pending_partial = 0;
        let lra = self.solver.lra_solver_mut();
        lra.clear_unsat_state();
        Ok(match lra.solve()?.decision {
            SolverDecision::FEASIBLE(_) => PartialCheckResult::Sat,
            SolverDecision::INFEASIBLE(conflict) => {
                PartialCheckResult::Unsat(self.conflict_clause(&conflict))
            }
            SolverDecision::UNKNOWN => PartialCheckResult::Unchanged,
        })
    }
}

impl Default for LiraIncrementalState {
    fn default() -> Self {
        Self::new()
    }
}

impl IncrementalArithSolver for LiraIncrementalState {
    fn register_var(&mut self, definition: Option<ArithExpr>, report_in_model: bool) -> VarId {
        self.try_register_var(definition, report_in_model)
            .unwrap_or_else(|e| panic!("lira-inc: register_var failed: {}", e.0))
    }

    fn mark_model_var(&mut self, var: VarId) {
        self.model_vars.insert(var);
    }

    fn notify_new_decision_level(&mut self) {
        // If the previous check ended `Unsat`, clear it first: `set_backtrack` is a no-op while
        // `Unsat`, which would capture a stale token and skip the assignment backup.
        let lra = self.solver.lra_solver_mut();
        lra.clear_unsat_state();
        let token = lra.set_backtrack();
        self.lra_tokens.push(token);
        self.sat_level += 1;
        self.lits_by_level.push(Vec::new());
        self.permanent_by_level.push(Vec::new());
        debug_println!(21, 0, "[lira-inc] new decision level {}", self.sat_level);
    }

    fn notify_backtrack(&mut self, level: usize) {
        if level >= self.sat_level {
            return;
        }
        // `lra_tokens[level]` is the token captured at the `level → level+1` boundary;
        // replaying it relaxes all bounds asserted at levels > `level`.
        let token = self.lra_tokens[level];
        let lra = self.solver.lra_solver_mut();
        lra.backtrack(token);
        // Any `Unsat` state refers to bounds that may just have been relaxed.
        lra.clear_unsat_state();
        self.lra_tokens.truncate(level);
        for lit in self.lits_by_level.drain(level + 1..).flatten() {
            self.active_lits.remove(&lit);
        }
        let relaxed: Vec<_> = self
            .permanent_by_level
            .drain(level + 1..)
            .flatten()
            .collect();
        self.sat_level = level;
        // Permanent (definitional) bounds asserted above `level` were just relaxed; re-assert
        // them at the surviving level.
        for (slack, bounds) in relaxed {
            self.assert_bounds(slack, &bounds)
                .unwrap_or_else(|e| panic!("lira-inc: re-asserting bound failed: {}", e.0));
            self.permanent_by_level[level].push((slack, bounds));
        }
        debug_println!(21, 0, "[lira-inc] backtrack to level {}", level);
    }

    fn push_constraint(&mut self, constraint: ArithConstraint, lit: i32) {
        self.try_push_constraint(constraint, lit)
            .unwrap_or_else(|e| panic!("lira-inc: push_constraint failed: {}", e.0))
    }

    fn push_equality(&mut self, a: VarId, b: VarId, lit: i32) {
        self.push_constraint(
            ArithConstraint::Eq(ArithExpr::var(a), ArithExpr::var(b)),
            lit,
        )
    }

    fn check(&mut self) -> ArithCheckResult {
        self.try_check()
            .unwrap_or_else(|e| panic!("lira-inc: check failed: {}", e.0))
    }

    fn check_partial_trail(&mut self) -> PartialCheckResult {
        self.try_check_partial_trail()
            .unwrap_or_else(|e| panic!("lira-inc: partial check failed: {}", e.0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: linear expr `coeff * var`.
    fn term(var: VarId, coeff: i32) -> ArithExpr {
        ArithExpr::linear(vec![(var, IBig::from(coeff))], IBig::from(0))
    }

    /// Helper: `coeff * div(a, b)`.
    fn div_term(a: VarId, b: VarId, coeff: i32) -> ArithExpr {
        ArithExpr {
            terms: vec![],
            constant: IBig::from(0),
            divs: vec![(a, b, IBig::from(coeff))],
            mods: vec![],
        }
    }

    /// Helper: `coeff * mod(a, b)`.
    fn mod_term(a: VarId, b: VarId, coeff: i32) -> ArithExpr {
        ArithExpr {
            terms: vec![],
            constant: IBig::from(0),
            divs: vec![],
            mods: vec![(a, b, IBig::from(coeff))],
        }
    }

    /// Register a hidden variable defined as the constant `c` (usable as a divisor).
    fn const_var(s: &mut LiraIncrementalState, c: i32) -> VarId {
        s.try_register_var(Some(ArithExpr::constant(c)), false)
            .unwrap()
    }

    fn is_sat(r: &ArithCheckResult) -> bool {
        matches!(r, ArithCheckResult::Sat(_))
    }

    #[test]
    fn empty_system_is_sat() {
        let mut s = LiraIncrementalState::new();
        assert!(is_sat(&s.try_check().unwrap()));
    }

    #[test]
    fn single_feasible_constraint() {
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        // x <= 5
        s.try_push_constraint(ArithConstraint::Leq(term(x, 1), ArithExpr::constant(5)), 10)
            .unwrap();
        assert!(is_sat(&s.try_check().unwrap()));
    }

    #[test]
    fn conflicting_constraints_are_unsat_with_core() {
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        // x >= 5 (encoded as 5 <= x), lit 10
        s.try_push_constraint(ArithConstraint::Leq(ArithExpr::constant(5), term(x, 1)), 10)
            .unwrap();
        // x <= 1, lit 20
        s.try_push_constraint(ArithConstraint::Leq(term(x, 1), ArithExpr::constant(1)), 20)
            .unwrap();
        match s.try_check().unwrap() {
            ArithCheckResult::Unsat(core) => {
                // Both tracking lits (negated) should appear in the conflict clause.
                assert!(core.contains(&-10), "core {core:?} missing -10");
                assert!(core.contains(&-20), "core {core:?} missing -20");
            }
            _ => panic!("expected UNSAT"),
        }
    }

    #[test]
    fn backtrack_recovers_from_conflict() {
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        // Level 0: x >= 5.
        s.try_push_constraint(ArithConstraint::Leq(ArithExpr::constant(5), term(x, 1)), 10)
            .unwrap();
        assert!(is_sat(&s.try_check().unwrap()));

        // Level 1: add x <= 1, making the system infeasible.
        s.notify_new_decision_level();
        s.try_push_constraint(ArithConstraint::Leq(term(x, 1), ArithExpr::constant(1)), 20)
            .unwrap();
        assert!(matches!(s.try_check().unwrap(), ArithCheckResult::Unsat(_)));

        // Backtrack to level 0: the x <= 1 bound is relaxed and the system is feasible.
        s.notify_backtrack(0);
        match s.try_check().unwrap() {
            ArithCheckResult::Sat(buckets) => {
                // Verify the popped x <= 1 bound is actually gone: only x >= 5 remains, so x's
                // model value must be >= 5 (i.e. strictly above the relaxed upper bound of 1).
                let x_val = buckets
                    .iter()
                    .find(|(_, vars)| vars.contains(&x))
                    .map(|(val, _)| val.clone())
                    .expect("x should appear in the model");
                assert!(
                    x_val >= IBig::from(5),
                    "x = {x_val} should be >= 5 with the x <= 1 bound relaxed"
                );
            }
            _ => panic!("expected SAT after backtrack"),
        }
    }

    #[test]
    fn assert_backtrack_reassert_constraint() {
        // C: x >= 5 (encoded as 5 <= x). D: x <= 1. C alone is feasible; C && D is not.
        // Exercises assert → backtrack → assert-again of the same constraint D.
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();

        // Assert C at level 0; feasible on its own.
        s.try_push_constraint(ArithConstraint::Leq(ArithExpr::constant(5), term(x, 1)), 10)
            .unwrap();
        assert!(is_sat(&s.try_check().unwrap()));

        // Push a decision level, assert D; C && D is infeasible.
        s.notify_new_decision_level();
        s.try_push_constraint(ArithConstraint::Leq(term(x, 1), ArithExpr::constant(1)), 20)
            .unwrap();
        assert!(matches!(s.try_check().unwrap(), ArithCheckResult::Unsat(_)));

        // Backtrack to where only C is asserted; D's bound is relaxed, so feasible again.
        s.notify_backtrack(0);
        assert!(is_sat(&s.try_check().unwrap()));

        // Assert D again: re-asserting the previously-backtracked constraint must once
        // more render the system infeasible.
        s.try_push_constraint(ArithConstraint::Leq(term(x, 1), ArithExpr::constant(1)), 20)
            .unwrap();
        assert!(matches!(s.try_check().unwrap(), ArithCheckResult::Unsat(_)));
    }

    #[test]
    fn definition_is_enforced_in_model() {
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        // y := x + 3
        let y = s
            .try_register_var(
                Some(ArithExpr::linear(vec![(x, IBig::from(1))], IBig::from(3))),
                true,
            )
            .unwrap();
        // Pin x == 4, so y must be 7.
        s.try_push_constraint(ArithConstraint::Eq(term(x, 1), ArithExpr::constant(4)), 10)
            .unwrap();
        match s.try_check().unwrap() {
            ArithCheckResult::Sat(buckets) => {
                // x is 4, y is 7.
                assert!(buckets.get(&IBig::from(4)).unwrap().contains(&x));
                assert!(buckets.get(&IBig::from(7)).unwrap().contains(&y));
            }
            _ => panic!("expected SAT"),
        }
    }

    #[test]
    fn equality_constraint_ties_two_vars() {
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        let y = s.try_register_var(None, true).unwrap();
        // x == y (via push_equality), and x == 9.
        s.push_equality(x, y, 10);
        s.try_push_constraint(ArithConstraint::Eq(term(x, 1), ArithExpr::constant(9)), 20)
            .unwrap();
        match s.try_check().unwrap() {
            ArithCheckResult::Sat(buckets) => {
                let nine = buckets.get(&IBig::from(9)).unwrap();
                assert!(nine.contains(&x) && nine.contains(&y));
            }
            _ => panic!("expected SAT"),
        }
    }

    #[test]
    fn strict_inequality_conflict() {
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        // x < 3 and x > 3 (encoded as 3 < x): infeasible.
        s.try_push_constraint(ArithConstraint::Lt(term(x, 1), ArithExpr::constant(3)), 10)
            .unwrap();
        s.try_push_constraint(ArithConstraint::Lt(ArithExpr::constant(3), term(x, 1)), 20)
            .unwrap();
        assert!(matches!(s.try_check().unwrap(), ArithCheckResult::Unsat(_)));
    }

    #[test]
    fn model_only_reports_marked_vars() {
        let mut s = LiraIncrementalState::new();
        let reported = s.try_register_var(None, true).unwrap();
        let hidden = s.try_register_var(None, false).unwrap();
        s.try_push_constraint(
            ArithConstraint::Eq(term(reported, 1), ArithExpr::constant(1)),
            10,
        )
        .unwrap();
        s.try_push_constraint(
            ArithConstraint::Eq(term(hidden, 1), ArithExpr::constant(2)),
            20,
        )
        .unwrap();
        match s.try_check().unwrap() {
            ArithCheckResult::Sat(buckets) => {
                let all_reported: DeterministicHashSet<VarId> =
                    buckets.values().flatten().copied().collect();
                assert!(all_reported.contains(&reported));
                assert!(!all_reported.contains(&hidden));
            }
            _ => panic!("expected SAT"),
        }
        // mark_model_var makes the hidden var appear.
        s.mark_model_var(hidden);
        match s.try_check().unwrap() {
            ArithCheckResult::Sat(buckets) => {
                assert!(buckets.get(&IBig::from(2)).unwrap().contains(&hidden));
            }
            _ => panic!("expected SAT"),
        }
    }

    #[test]
    fn nested_levels_backtrack_partially() {
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        // L0: x >= 0.
        s.try_push_constraint(ArithConstraint::Leq(ArithExpr::constant(0), term(x, 1)), 10)
            .unwrap();
        // L1: x <= 10.
        s.notify_new_decision_level();
        s.try_push_constraint(
            ArithConstraint::Leq(term(x, 1), ArithExpr::constant(10)),
            20,
        )
        .unwrap();
        assert!(is_sat(&s.try_check().unwrap()));
        // L2: x <= -1, contradicts x >= 0.
        s.notify_new_decision_level();
        s.try_push_constraint(
            ArithConstraint::Leq(term(x, 1), ArithExpr::constant(-1)),
            30,
        )
        .unwrap();
        assert!(matches!(s.try_check().unwrap(), ArithCheckResult::Unsat(_)));
        // Backtrack to L1: x <= -1 relaxed, but x <= 10 still active. Feasible.
        s.notify_backtrack(1);
        assert!(is_sat(&s.try_check().unwrap()));
    }

    #[test]
    fn integrality_is_enforced() {
        // `3x >= 1 && 3x <= 2` pins x to [1/3, 2/3]: the rational relaxation is feasible but
        // there is no integer in that interval, so branch-and-bound must report UNSAT. A pure
        // LRA frontend would (unsoundly) report SAT here.
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        // 3x >= 1, encoded as 1 <= 3x.
        s.try_push_constraint(ArithConstraint::Leq(ArithExpr::constant(1), term(x, 3)), 10)
            .unwrap();
        // 3x <= 2.
        s.try_push_constraint(ArithConstraint::Leq(term(x, 3), ArithExpr::constant(2)), 20)
            .unwrap();
        assert!(
            matches!(s.try_check().unwrap(), ArithCheckResult::Unsat(_)),
            "x in [1/3, 2/3] has no integer solution; branch-and-bound must report UNSAT"
        );
    }

    #[test]
    fn branch_and_bound_state_is_fresh_across_checks() {
        // A `check` that falls back to branch-and-bound must not leak speculative branch bounds
        // into the persistent solver: the next `check` must see a fresh branch-and-bound state.
        //
        // The classic integer trap `3x >= 1 && 3x <= 2` forces B&B to prune the floor branch
        // (x <= 0) and explore the ceil branch (x >= 1) — that `x >= 1` is exactly the bound that
        // would leak. After backtracking away the trap and pinning x == 0, the system is feasible
        // *only* if no residual `x >= 1` survives from the previous `check`.
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();

        // Level 1: assert the trap, so `check` runs branch-and-bound and reports UNSAT.
        s.notify_new_decision_level();
        s.try_push_constraint(ArithConstraint::Leq(ArithExpr::constant(1), term(x, 3)), 10)
            .unwrap();
        s.try_push_constraint(ArithConstraint::Leq(term(x, 3), ArithExpr::constant(2)), 20)
            .unwrap();
        assert!(matches!(s.try_check().unwrap(), ArithCheckResult::Unsat(_)));

        // Backtrack to level 0: the trap's bounds are relaxed. Pin x == 0, which is feasible
        // *unless* a speculative `x >= 1` from the previous branch-and-bound leaked through.
        s.notify_backtrack(0);
        s.try_push_constraint(ArithConstraint::Eq(term(x, 1), ArithExpr::constant(0)), 30)
            .unwrap();
        match s.try_check().unwrap() {
            ArithCheckResult::Sat(buckets) => {
                assert!(
                    buckets.get(&IBig::from(0)).unwrap().contains(&x),
                    "x should be 0; a leaked x >= 1 branch bound would make this UNSAT"
                );
            }
            _ => {
                panic!(
                    "expected SAT: a residual branch-and-bound bound leaked across check() calls"
                )
            }
        }
    }

    #[test]
    fn div_floor_semantics_sat() {
        // x = 3, div(x, 2) = 1: floor(3/2) = 1 holds under Euclidean division.
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        let two = const_var(&mut s, 2);
        s.try_push_constraint(ArithConstraint::Eq(term(x, 1), ArithExpr::constant(3)), 10)
            .unwrap();
        s.try_push_constraint(
            ArithConstraint::Eq(div_term(x, two, 1), ArithExpr::constant(1)),
            20,
        )
        .unwrap();
        assert!(is_sat(&s.try_check().unwrap()));
    }

    #[test]
    fn div_constant_numerator_floor_sat() {
        // r = div(7, 2), r = 3: Euclidean 7 = 2*3 + 1.
        let mut s = LiraIncrementalState::new();
        let seven = const_var(&mut s, 7);
        let two = const_var(&mut s, 2);
        let r = s.try_register_var(None, true).unwrap();
        s.try_push_constraint(ArithConstraint::Eq(term(r, 1), div_term(seven, two, 1)), 10)
            .unwrap();
        s.try_push_constraint(ArithConstraint::Eq(term(r, 1), ArithExpr::constant(3)), 20)
            .unwrap();
        assert!(is_sat(&s.try_check().unwrap()));
    }

    #[test]
    fn div_wrong_quotient_unsat() {
        // r = div(7, 2), r = 4: 2*4 = 8 > 7 violates the remainder bound.
        let mut s = LiraIncrementalState::new();
        let seven = const_var(&mut s, 7);
        let two = const_var(&mut s, 2);
        let r = s.try_register_var(None, true).unwrap();
        s.try_push_constraint(ArithConstraint::Eq(term(r, 1), div_term(seven, two, 1)), 10)
            .unwrap();
        s.try_push_constraint(ArithConstraint::Eq(term(r, 1), ArithExpr::constant(4)), 20)
            .unwrap();
        assert!(matches!(s.try_check().unwrap(), ArithCheckResult::Unsat(_)));
    }

    #[test]
    fn div_negative_numerator_floors() {
        // div(-1, 2) = -1 under Euclidean semantics (-1 = 2*(-1) + 1).
        let mut s = LiraIncrementalState::new();
        let neg1 = const_var(&mut s, -1);
        let two = const_var(&mut s, 2);
        let r = s.try_register_var(None, true).unwrap();
        s.try_push_constraint(ArithConstraint::Eq(term(r, 1), div_term(neg1, two, 1)), 10)
            .unwrap();
        s.try_push_constraint(ArithConstraint::Eq(term(r, 1), ArithExpr::constant(-1)), 20)
            .unwrap();
        assert!(is_sat(&s.try_check().unwrap()));
    }

    #[test]
    fn div_negative_denominator_floors() {
        // div(9, -2) = -4 under Euclidean semantics (9 = (-2)*(-4) + 1).
        let mut s = LiraIncrementalState::new();
        let nine = const_var(&mut s, 9);
        let neg2 = const_var(&mut s, -2);
        let r = s.try_register_var(None, true).unwrap();
        s.try_push_constraint(ArithConstraint::Eq(term(r, 1), div_term(nine, neg2, 1)), 10)
            .unwrap();
        s.try_push_constraint(ArithConstraint::Eq(term(r, 1), ArithExpr::constant(-4)), 20)
            .unwrap();
        assert!(is_sat(&s.try_check().unwrap()));
    }

    #[test]
    fn mod_matches_euclidean_remainder() {
        // x = 7, mod(x, 3) = 1 (7 = 3*2 + 1).
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        let three = const_var(&mut s, 3);
        s.try_push_constraint(ArithConstraint::Eq(term(x, 1), ArithExpr::constant(7)), 10)
            .unwrap();
        s.try_push_constraint(
            ArithConstraint::Eq(mod_term(x, three, 1), ArithExpr::constant(1)),
            20,
        )
        .unwrap();
        assert!(is_sat(&s.try_check().unwrap()));
    }

    #[test]
    fn mod_out_of_range_unsat() {
        // mod(x, 3) = 5 exceeds the remainder bound (0 <= r <= 2), infeasible even over the reals.
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        let three = const_var(&mut s, 3);
        s.try_push_constraint(
            ArithConstraint::Eq(mod_term(x, three, 1), ArithExpr::constant(5)),
            10,
        )
        .unwrap();
        assert!(matches!(s.try_check().unwrap(), ArithCheckResult::Unsat(_)));
    }

    #[test]
    fn mod_lra_does_not_over_approximate_integrality() {
        // x = 7, mod(x, 3) = 2 has no integer solution (7 mod 3 = 1), but the real quotient
        // q = 5/3 satisfies the Euclidean rows, so the LIRA frontend reports Unsat.
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        let three = const_var(&mut s, 3);
        s.try_push_constraint(ArithConstraint::Eq(term(x, 1), ArithExpr::constant(7)), 10)
            .unwrap();
        s.try_push_constraint(
            ArithConstraint::Eq(mod_term(x, three, 1), ArithExpr::constant(2)),
            20,
        )
        .unwrap();
        assert!(matches!(s.try_check().unwrap(), ArithCheckResult::Unsat(_)));
    }

    #[test]
    fn div_constraint_backtracks() {
        // L0: div(x, 2) = 5 forces 10 <= x <= 11. L1: x <= 3 conflicts; backtrack recovers.
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        let two = const_var(&mut s, 2);
        s.try_push_constraint(
            ArithConstraint::Eq(div_term(x, two, 1), ArithExpr::constant(5)),
            10,
        )
        .unwrap();
        assert!(is_sat(&s.try_check().unwrap()));

        s.notify_new_decision_level();
        s.try_push_constraint(ArithConstraint::Leq(term(x, 1), ArithExpr::constant(3)), 20)
            .unwrap();
        assert!(matches!(s.try_check().unwrap(), ArithCheckResult::Unsat(_)));

        s.notify_backtrack(0);
        assert!(is_sat(&s.try_check().unwrap()));
    }

    #[test]
    fn non_constant_divisor_is_rejected() {
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        let d = s.try_register_var(None, false).unwrap(); // no constant definition
        assert!(
            s.try_push_constraint(
                ArithConstraint::Leq(div_term(x, d, 1), ArithExpr::constant(0)),
                10
            )
            .is_err()
        );
    }

    #[test]
    fn zero_divisor_is_rejected() {
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        let zero = const_var(&mut s, 0);
        assert!(
            s.try_push_constraint(
                ArithConstraint::Leq(div_term(x, zero, 1), ArithExpr::constant(0)),
                10
            )
            .is_err()
        );
    }

    #[test]
    fn constant_divisor_registered_above_backtrack_survives() {
        // A constant registered at level 1 is a substituted definition, not a relaxable row, so
        // it stays usable as a divisor after backtracking below the level it was registered at.
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();

        s.notify_new_decision_level();
        let two = const_var(&mut s, 2);
        s.try_push_constraint(
            ArithConstraint::Eq(div_term(x, two, 1), ArithExpr::constant(5)),
            10,
        )
        .unwrap();
        assert!(is_sat(&s.try_check().unwrap()));

        s.notify_backtrack(0);
        s.try_push_constraint(
            ArithConstraint::Eq(div_term(x, two, 1), ArithExpr::constant(5)),
            20,
        )
        .unwrap();
        // div(x, 2) = 5 still forces 10 <= x <= 11.
        s.try_push_constraint(ArithConstraint::Leq(term(x, 1), ArithExpr::constant(9)), 30)
            .unwrap();
        assert!(matches!(s.try_check().unwrap(), ArithCheckResult::Unsat(_)));
    }

    #[test]
    fn euclidean_row_survives_backtrack() {
        // The quotient for div(x, 2) is created at level 1. Its Euclidean row is definitional, so
        // after backtracking to level 0 the shared quotient must still satisfy it: with x = 7,
        // div(x, 2) = 4 is infeasible. (Were the row relaxed, q would be free and this SAT.)
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        let two = const_var(&mut s, 2);

        s.notify_new_decision_level();
        s.try_push_constraint(
            ArithConstraint::Eq(div_term(x, two, 1), ArithExpr::constant(5)),
            10,
        )
        .unwrap();
        assert!(is_sat(&s.try_check().unwrap()));

        s.notify_backtrack(0);
        s.try_push_constraint(ArithConstraint::Eq(term(x, 1), ArithExpr::constant(7)), 20)
            .unwrap();
        s.try_push_constraint(
            ArithConstraint::Eq(div_term(x, two, 1), ArithExpr::constant(4)),
            30,
        )
        .unwrap();
        match s.try_check().unwrap() {
            ArithCheckResult::Unsat(core) => {
                // The definitional row cites nothing; only the two constraints do.
                assert!(core.contains(&-20) && core.contains(&-30), "core {core:?}");
                assert!(
                    !core.contains(&-10),
                    "core {core:?} cites a relaxed constraint"
                );
            }
            r => panic!("expected UNSAT, got {r:?}"),
        }
    }

    #[test]
    fn constant_divisor_at_level_zero_survives_backtrack() {
        // A constant registered at level 0 stays valid as a divisor across backtracking.
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        let two = const_var(&mut s, 2);

        s.notify_new_decision_level();
        s.try_push_constraint(ArithConstraint::Eq(term(x, 1), ArithExpr::constant(3)), 10)
            .unwrap();
        assert!(is_sat(&s.try_check().unwrap()));

        // Backtrack to level 0: `two` was registered at level 0, so it survives and can
        // still serve as a divisor.
        s.notify_backtrack(0);
        s.try_push_constraint(
            ArithConstraint::Eq(div_term(x, two, 1), ArithExpr::constant(1)),
            20,
        )
        .unwrap();
        s.try_push_constraint(ArithConstraint::Eq(term(x, 1), ArithExpr::constant(3)), 30)
            .unwrap();
        assert!(is_sat(&s.try_check().unwrap()));
    }

    #[test]
    fn definition_at_level_zero_survives_backtrack() {
        // y := x + 3 registered at level 0. A level-1 assert of x is relaxed on backtrack,
        // but the definition equality persists (asserted at level 0), so re-pinning x
        // after backtracking still forces y = x + 3.
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        let y = s
            .try_register_var(
                Some(ArithExpr::linear(vec![(x, IBig::from(1))], IBig::from(3))),
                true,
            )
            .unwrap();

        // Level 1: x == 4 ⇒ y == 7.
        s.notify_new_decision_level();
        s.try_push_constraint(ArithConstraint::Eq(term(x, 1), ArithExpr::constant(4)), 10)
            .unwrap();
        match s.try_check().unwrap() {
            ArithCheckResult::Sat(b) => {
                assert!(b.get(&IBig::from(4)).unwrap().contains(&x));
                assert!(b.get(&IBig::from(7)).unwrap().contains(&y));
            }
            _ => panic!("expected SAT"),
        }

        // Backtrack to level 0: x == 4 relaxed, but y := x + 3 still holds. Re-assert
        // x == 100 ⇒ y == 103.
        s.notify_backtrack(0);
        s.try_push_constraint(
            ArithConstraint::Eq(term(x, 1), ArithExpr::constant(100)),
            20,
        )
        .unwrap();
        match s.try_check().unwrap() {
            ArithCheckResult::Sat(b) => {
                assert!(b.get(&IBig::from(100)).unwrap().contains(&x));
                assert!(b.get(&IBig::from(103)).unwrap().contains(&y));
            }
            _ => panic!("expected SAT"),
        }
    }

    #[test]
    fn definition_above_backtrack_level_persists() {
        // A definition registered above the backtrack target is substituted, so it holds at every
        // level: the translator never re-registers a VarId after backtracking.
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        s.try_push_constraint(ArithConstraint::Eq(term(x, 1), ArithExpr::constant(4)), 10)
            .unwrap();

        // Level 1: introduce y := x + 3 ⇒ y == 7.
        s.notify_new_decision_level();
        let y = s
            .try_register_var(
                Some(ArithExpr::linear(vec![(x, IBig::from(1))], IBig::from(3))),
                true,
            )
            .unwrap();
        match s.try_check().unwrap() {
            ArithCheckResult::Sat(b) => assert!(b.get(&IBig::from(7)).unwrap().contains(&y)),
            _ => panic!("expected SAT"),
        }

        // Backtrack to level 0: y is still x + 3, so y == 0 conflicts with x == 4.
        s.notify_backtrack(0);
        s.try_push_constraint(ArithConstraint::Eq(term(y, 1), ArithExpr::constant(0)), 20)
            .unwrap();
        assert!(matches!(s.try_check().unwrap(), ArithCheckResult::Unsat(_)));
    }

    #[test]
    fn reasserted_definition_recouples_variable() {
        // Full cycle: def → solve → backtrack → solve → assert the (redundant) defining
        // equality explicitly → solve. The definition survives the backtrack throughout.
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        s.try_push_constraint(ArithConstraint::Eq(term(x, 1), ArithExpr::constant(4)), 10)
            .unwrap();

        // Level 1: y := x + 3 ⇒ y == 7.
        s.notify_new_decision_level();
        let y = s
            .try_register_var(
                Some(ArithExpr::linear(vec![(x, IBig::from(1))], IBig::from(3))),
                true,
            )
            .unwrap();
        assert!(is_sat(&s.try_check().unwrap()));

        // Backtrack to level 0: y's definition persists.
        s.notify_backtrack(0);
        assert!(is_sat(&s.try_check().unwrap()));

        // Assert y == x + 3 explicitly. With x == 4 still active this forces y == 7; pinning
        // y == 0 must conflict.
        s.notify_new_decision_level();
        s.try_push_constraint(
            ArithConstraint::Eq(
                term(y, 1),
                ArithExpr::linear(vec![(x, IBig::from(1))], IBig::from(3)),
            ),
            20,
        )
        .unwrap();
        match s.try_check().unwrap() {
            ArithCheckResult::Sat(b) => assert!(b.get(&IBig::from(7)).unwrap().contains(&y)),
            _ => panic!("expected SAT with y == x + 3"),
        }

        s.notify_new_decision_level();
        s.try_push_constraint(ArithConstraint::Eq(term(y, 1), ArithExpr::constant(0)), 30)
            .unwrap();
        assert!(matches!(s.try_check().unwrap(), ArithCheckResult::Unsat(_)));
    }

    #[test]
    fn unregistered_var_is_rejected() {
        let mut s = LiraIncrementalState::new();
        // VarId 99 was never registered.
        assert!(
            s.try_push_constraint(
                ArithConstraint::Leq(term(99, 1), ArithExpr::constant(0)),
                10
            )
            .is_err()
        );
    }

    #[test]
    fn trivial_constraints() {
        // Constraints whose variables cancel are decided by their constant: x <= x + 1 holds
        // (no row), x == x + 1 is UNSAT citing only its own lit.
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        let x_plus_1 = ArithExpr::linear(vec![(x, IBig::from(1))], IBig::from(1));
        s.try_push_constraint(ArithConstraint::Leq(term(x, 1), x_plus_1.clone()), 10)
            .unwrap();
        assert!(is_sat(&s.try_check().unwrap()));
        s.try_push_constraint(ArithConstraint::Eq(term(x, 1), x_plus_1), 20)
            .unwrap();
        match s.try_check().unwrap() {
            ArithCheckResult::Unsat(core) => assert_eq!(core, vec![-20]),
            r => panic!("expected UNSAT, got {r:?}"),
        }
    }

    #[test]
    fn aliased_definition_equality_is_trivial() {
        // y := x substitutes to the same internal var, so x == y has no variables left.
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        let y = s.try_register_var(Some(term(x, 1)), true).unwrap();
        s.push_equality(x, y, 10);
        s.try_push_constraint(ArithConstraint::Eq(term(x, 1), ArithExpr::constant(3)), 20)
            .unwrap();
        match s.try_check().unwrap() {
            ArithCheckResult::Sat(b) => {
                let three = b.get(&IBig::from(3)).unwrap();
                assert!(three.contains(&x) && three.contains(&y));
            }
            r => panic!("expected SAT, got {r:?}"),
        }
    }

    #[test]
    fn repushed_active_lit_is_noop_and_repushable_after_backtrack() {
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        s.try_push_constraint(ArithConstraint::Leq(ArithExpr::constant(5), term(x, 1)), 10)
            .unwrap();
        s.notify_new_decision_level();
        let le1 = ArithConstraint::Leq(term(x, 1), ArithExpr::constant(1));
        s.try_push_constraint(le1.clone(), 20).unwrap();
        // Re-pushing the active lit 20 must not add another row.
        s.try_push_constraint(le1.clone(), 20).unwrap();
        assert!(matches!(s.try_check().unwrap(), ArithCheckResult::Unsat(_)));
        s.notify_backtrack(0);
        assert!(is_sat(&s.try_check().unwrap()));
        // After backtrack, lit 20 is inactive and pushing it again re-asserts it.
        s.try_push_constraint(le1, 20).unwrap();
        assert!(matches!(s.try_check().unwrap(), ArithCheckResult::Unsat(_)));
    }

    #[test]
    fn partial_check_is_batched_and_finds_relaxation_conflicts() {
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        // x >= 5, then x <= 1: infeasible already over the reals.
        s.try_push_constraint(ArithConstraint::Leq(ArithExpr::constant(5), term(x, 1)), 1)
            .unwrap();
        s.try_push_constraint(ArithConstraint::Leq(term(x, 1), ArithExpr::constant(1)), 2)
            .unwrap();
        // Below the batch threshold the check is skipped.
        assert!(matches!(
            s.try_check_partial_trail().unwrap(),
            PartialCheckResult::Unchanged
        ));
        // Pad with redundant constraints up to the threshold.
        for lit in 3..=(PARTIAL_CHECK_ASSERTION_BATCH as i32) {
            s.try_push_constraint(
                ArithConstraint::Leq(term(x, 1), ArithExpr::constant(100)),
                lit,
            )
            .unwrap();
        }
        match s.try_check_partial_trail().unwrap() {
            PartialCheckResult::Unsat(core) => {
                assert!(core.contains(&-1) && core.contains(&-2), "core {core:?}");
            }
            r => panic!("expected partial UNSAT, got {r:?}"),
        }
    }

    #[test]
    fn partial_check_ignores_integrality() {
        // 3x in [1, 2] is feasible over the reals: the partial check reports Sat, while the full
        // check (branch-and-bound) reports Unsat.
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        s.try_push_constraint(ArithConstraint::Leq(ArithExpr::constant(1), term(x, 3)), 1)
            .unwrap();
        s.try_push_constraint(ArithConstraint::Leq(term(x, 3), ArithExpr::constant(2)), 2)
            .unwrap();
        for lit in 3..=(PARTIAL_CHECK_ASSERTION_BATCH as i32) {
            s.try_push_constraint(
                ArithConstraint::Leq(term(x, 1), ArithExpr::constant(100)),
                lit,
            )
            .unwrap();
        }
        let r = s.try_check_partial_trail().unwrap();
        assert!(matches!(r, PartialCheckResult::Sat), "got {r:?}");
        let r = s.try_check().unwrap();
        assert!(matches!(r, ArithCheckResult::Unsat(_)), "got {r:?}");
    }

    #[test]
    fn integrality_is_enforced_after_earlier_pivots() {
        // A first check pivots the persistent tableau. The unit cube test of a later check must
        // not round basic variables independently of their rows (it used to, returning x = 0
        // here even though 3x >= 1).
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        s.try_push_constraint(ArithConstraint::Leq(ArithExpr::constant(1), term(x, 3)), 1)
            .unwrap();
        s.try_push_constraint(ArithConstraint::Leq(term(x, 3), ArithExpr::constant(2)), 2)
            .unwrap();
        s.solver.lra_solver_mut().solve().unwrap();
        let r = s.try_check().unwrap();
        assert!(matches!(r, ArithCheckResult::Unsat(_)), "got {r:?}");
    }

    #[test]
    fn branch_and_bound_budget_exhaustion_is_unknown() {
        let config = SolverConfig {
            max_lra_solve_calls: Some(1),
            ..SolverConfig::default()
        };
        let mut s = LiraIncrementalState::with_config(config);
        let x = s.try_register_var(None, true).unwrap();
        let y = s.try_register_var(None, true).unwrap();
        // 2x + 2y = 1 is feasible over the reals but has no integer solution; showing that needs
        // branching, which the one-solve budget does not allow.
        s.try_push_constraint(
            ArithConstraint::Eq(
                ArithExpr::linear(vec![(x, IBig::from(2)), (y, IBig::from(2))], IBig::from(0)),
                ArithExpr::constant(1),
            ),
            10,
        )
        .unwrap();
        assert!(matches!(s.try_check().unwrap(), ArithCheckResult::Unknown));
    }
}
