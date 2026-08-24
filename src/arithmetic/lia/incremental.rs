// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Incremental frontend for the internal LRA solver.
//!
//! This module exposes an incremental, push/pop-driven API over the internal
//! [`LRASolver`], operating on an abstract [`VarId`] namespace rather than on
//! egraph ids or [`crate::solver_state::SolverState`]. It is the internal-solver
//! analogue of crate::arithmetic::z3incremental::Z3IncrementalState: a
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
//! # Scope / limitations of this frontend
//!
//! - **Not currently wired up to the main solver**
//! - **Integer reasoning is enforced** via the [`LIRASolver`]'s branch-and-bound, so
//!   [`IncrementalLiraSolver::check`] reports `Sat` only for a system with an integer
//!   solution. Each `check` starts from a fresh branch-and-bound state, since
//!   [`LIRASolver::solve`] clears any residual `Unsat` and unwinds every speculative
//!   branch bound before returning.
//! - **`div`/`mod` require a constant divisor.** A `div`/`mod` term is converted to a fresh
//!   quotient `q` plus the Euclidean rows `a − n·q ≥ 0` and `a − n·q ≤ |n| − 1`
//!   (`mod(a, n) = a − n·q`), as in [`crate::arithmetic::lialp`]. The divisor `n` comes from
//!   the denominator variable's constant definition; a non-constant or zero divisor errors.

use crate::arithmetic::lia::config::SolverConfig;
use crate::arithmetic::lia::context::ConvContext;
use crate::arithmetic::lia::linear_system::{Mon, Rel};
use crate::arithmetic::lia::lira_solver::LIRASolver;
use crate::arithmetic::lia::lra_solver::LRASolver;
use crate::arithmetic::lia::solver_result::{SolverDecision, SolverError, SolverResult};
use crate::arithmetic::lia::tableau::TableauKind;
use crate::arithmetic::lia::types::Rational;
use crate::arithmetic::lia::variables::{Owner, Var, VarInfo};
use crate::debug_println;
use crate::utils::{DeterministicHashMap, DeterministicHashSet};
use dashu::integer::IBig;

/// Opaque variable handle assigned by the solver via
/// [`IncrementalLiraSolver::register_var`].
pub type VarId = u32;

/// Constructor for a [`Rel`] from monomials and a constant (one of `Rel::mk_le`,
/// `mk_lt`, `mk_eq`), selected per [`ArithConstraint`] variant.
type RelMk = fn(Vec<Mon<Rational>>, Rational) -> Rel<Rational>;

/// A linear expression: sum of `coeff * var` terms plus a constant, with optional
/// `div`/`mod` terms. The denominator must resolve to a constant (see
/// [`IncrementalLiraSolver::register_var`]).
#[derive(Debug, Clone)]
pub struct ArithExpr {
    /// `(var, coefficient)` pairs.
    pub terms: Vec<(VarId, IBig)>,
    /// Constant addend.
    pub constant: IBig,
    /// `(numerator_var, denominator_var, coeff)` division terms.
    pub divs: Vec<(VarId, VarId, IBig)>,
    /// `(numerator_var, denominator_var, coeff)` modulo terms.
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

    /// If this expression is a bare constant (no terms, div, or mod), return it.
    fn as_constant(&self) -> Option<&IBig> {
        (self.terms.is_empty() && self.divs.is_empty() && self.mods.is_empty())
            .then_some(&self.constant)
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

/// Result of [`IncrementalLiraSolver::check`].
#[derive(Debug)]
pub enum ArithCheckResult {
    /// Conflict: the conflict clause (negated asserted SAT literals), matching the
    /// shape expected by the propagator's existing unsat-core handling.
    Unsat(Vec<i32>),
    /// Satisfiable: model-value → the set of `report_in_model` [`VarId`]s assigned
    /// that (truncated integer) value.
    Sat(DeterministicHashMap<IBig, DeterministicHashSet<VarId>>),
}

/// Incremental LIA frontend: a persistent [`LIRASolver`] driven by push/pop of
/// constraints keyed by SAT literal. See the module docs for the mapping onto the
/// incremental solver and the current limitations.
///
/// Structural operations (`add_relation`, `assert_*`, `set_backtrack`, `backtrack`) go
/// through the inner [`LRASolver`] via [`LIRASolver::lra_solver_mut`], while
/// [`Self::check`] calls [`LIRASolver::solve`] so integrality is enforced by
/// branch-and-bound.
#[derive(Debug)]
pub struct IncrementalLiraSolver {
    /// The persistent underlying solver. Its inner LRA solver is seeded with one inert
    /// dummy row so the (sparse) tableau always exists and can be grown via `add_relation`.
    solver: LIRASolver,
    /// Next fresh internal [`Var`] id (shared by registered vars and slacks).
    next_internal_id: usize,
    /// Next fresh [`VarId`] handed to callers.
    next_var_id: VarId,
    /// `VarId` → internal solver [`Var`].
    var_of: DeterministicHashMap<VarId, Var>,
    /// `VarId`s registered with a constant definition → `(constant, sat_level)`, where
    /// `sat_level` is the decision level at which the defining equality was asserted. Used
    /// to resolve `div`/`mod` divisors. Entries registered above a backtrack target are
    /// invalidated by [`Self::notify_backtrack`], since their defining row is relaxed there.
    const_of: DeterministicHashMap<VarId, (IBig, usize)>,
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

impl IncrementalLiraSolver {
    /// Create a fresh incremental solver with the default [`SolverConfig`].
    pub fn new() -> Self {
        Self::with_config(SolverConfig::default())
    }

    /// Create a fresh incremental solver, using `config` for the underlying
    /// [`LIRASolver`] (e.g. to bound `max_branch_depth` / `max_lra_solve_calls`).
    pub fn with_config(config: SolverConfig) -> Self {
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
            next_var_id: 0,
            var_of: DeterministicHashMap::new(),
            const_of: DeterministicHashMap::new(),
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

    /// Allocate a fresh [`VarId`] backed by an internal [`Var`], excluded from the model.
    /// Used in particular for `div`/`mod` quotients.
    fn fresh_hidden_var(&mut self) -> VarId {
        let var_id = self.next_var_id;
        self.next_var_id += 1;
        let var = self.fresh_var();
        self.var_of.insert(var_id, var);
        var_id
    }

    /// Resolve a `div`/`mod` denominator to its constant, erroring if it is unknown or zero.
    fn resolve_divisor(&self, denom: VarId) -> SolverResult<IBig> {
        match self.const_of.get(&denom).map(|(n, _)| n) {
            Some(n) if *n != IBig::ZERO => Ok(n.clone()),
            Some(_) => Err(SolverError("div/mod by zero".to_string())),
            None => Err(SolverError(format!(
                "div/mod divisor VarId {denom} is not a registered constant"
            ))),
        }
    }

    /// Register a fresh integer variable. If `definition` is `Some`, the equality
    /// `new_var == definition` is asserted at the current decision level. If
    /// `report_in_model` is true, the variable's value is included in the model
    /// buckets returned by [`Self::check`] on SAT.
    ///
    /// A variable defined as a bare constant is recorded so it can serve as a `div`/`mod`
    /// divisor. Returns an error if `definition` refers to an unregistered variable or a
    /// non-constant/zero `div`/`mod` divisor.
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
            if let Some(c) = def.as_constant() {
                // Record the level of the defining equality so it can be invalidated if a
                // later backtrack relaxes that row (see `notify_backtrack`).
                self.const_of.insert(var_id, (c.clone(), self.sat_level));
            }
            // Assert `new_var == def`, i.e. `new_var - def == 0`, as a fresh row tracked with no
            // SAT literal, since `new_var` is fresh and this equality never constrains previously
            // registered variables on its own. This is sound only under the convention that UNSAT
            // cores are reported relative to all active definitions/background equalities, not as a
            // self-contained refutation over SAT literals alone.
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
        self.solver.lra_solver_mut().clear_unsat_state();
        // Capture a backtrack token for the level we are leaving so a later
        // `notify_backtrack` can relax everything asserted above it.
        let token = self.solver.lra_solver_mut().set_backtrack();
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
        self.solver.lra_solver_mut().backtrack(token);
        self.lra_tokens.truncate(level);
        self.sat_level = level;
        // Invalidate constant definitions asserted above the backtrack target: their
        // defining rows were just relaxed, so the variable is no longer pinned to that
        // constant and must not continue to serve as a `div`/`mod` divisor.
        self.const_of
            .retain(|_, (_, def_level)| *def_level <= level);
        debug_println!(21, 0, "[lra-inc] backtrack to level {}", level);
    }

    /// Push a constraint tracked by SAT literal `lit`. On conflict, `lit` (negated)
    /// is citable in the unsat core.
    ///
    /// Returns an error if either expression refers to an unregistered variable or a
    /// non-constant/zero `div`/`mod` divisor.
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
    pub fn check(&mut self) -> SolverResult<ArithCheckResult> {
        let decision = self.solver.solve()?.decision;
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
                Ok(ArithCheckResult::Sat(buckets))
            }
            SolverDecision::INFEASIBLE(conflict) => {
                let lits: DeterministicHashSet<i32> = conflict
                    .iter()
                    .flat_map(|var| self.slack_to_lits.get(var).into_iter().flatten().copied())
                    .collect();
                debug_println!(21, 0, "[lra-inc] UNSAT core lits={:?}", lits);
                Ok(ArithCheckResult::Unsat(lits.into_iter().collect()))
            }
            SolverDecision::UNKNOWN => {
                // `LIRASolver::solve` can return UNKNOWN if it hits its branch-and-bound
                // resource limits (`max_branch_depth` / `max_lra_solve_calls`); treat that
                // conservatively as satisfiable, bucketing the current best-effort assignment.
                let model = self
                    .solver
                    .lra_solver()
                    .get_rational_model()
                    .unwrap_or_default();
                let mut buckets: DeterministicHashMap<IBig, DeterministicHashSet<VarId>> =
                    DeterministicHashMap::new();
                for var_id in self.model_vars.iter() {
                    let var = self.var_of[var_id];
                    let value = model.get(&var).cloned().unwrap_or(Rational::ZERO);
                    let ibig = value.to_int().value().clone();
                    buckets.entry(ibig).or_default().insert(*var_id);
                }
                Ok(ArithCheckResult::Sat(buckets))
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

    /// `coeff` as a [`Rational`], negated when `negate` is set.
    fn signed(coeff: &IBig, negate: bool) -> Rational {
        let c = Rational::from(coeff.clone());
        if negate { -c } else { c }
    }

    /// Convert an [`ArithExpr`] to monomials with the given sign, converting any `div`/`mod` terms
    /// to a fresh quotient plus Euclidean rows tracked under `lit`. Errors on an unregistered
    /// variable or a non-constant/zero divisor.
    fn expr_to_monomials(
        &mut self,
        expr: &ArithExpr,
        negate: bool,
        lit: Option<i32>,
    ) -> SolverResult<Vec<Mon<Rational>>> {
        let mut monomials = Vec::with_capacity(expr.terms.len());
        for (var_id, coeff) in &expr.terms {
            let var = self.resolve(*var_id)?;
            monomials.push(Mon::new(Self::signed(coeff, negate), var));
        }
        for (a_id, b_id, coeff) in &expr.divs {
            let n = self.resolve_divisor(*b_id)?;
            let q = self.fresh_hidden_var();
            self.push_euclidean(*a_id, q, &n, lit)?;
            let q_var = self.resolve(q)?;
            // div(a, n) = q
            monomials.push(Mon::new(Self::signed(coeff, negate), q_var));
        }
        for (a_id, b_id, coeff) in &expr.mods {
            let n = self.resolve_divisor(*b_id)?;
            let q = self.fresh_hidden_var();
            self.push_euclidean(*a_id, q, &n, lit)?;
            let a_var = self.resolve(*a_id)?;
            let q_var = self.resolve(q)?;
            // mod(a, n) = a - n*q
            let c = Self::signed(coeff, negate);
            monomials.push(Mon::new(c.clone(), a_var));
            monomials.push(Mon::new(-(&c * &Rational::from(n)), q_var));
        }
        Ok(monomials)
    }

    /// Push the Euclidean rows defining quotient `q` for `a / n` (constant `n`):
    /// `a − n·q ≥ 0` and `a − n·q ≤ |n| − 1`, both tracked under `lit`.
    fn push_euclidean(
        &mut self,
        a: VarId,
        q: VarId,
        n: &IBig,
        lit: Option<i32>,
    ) -> SolverResult<()> {
        let zero = IBig::from(0);
        let abs_n = if *n < zero { -n.clone() } else { n.clone() };
        // n·q ≤ a  (⇔ a − n·q ≥ 0)
        self.push_relation(
            ArithConstraint::Leq(
                ArithExpr::linear(vec![(q, n.clone())], zero.clone()),
                ArithExpr::linear(vec![(a, IBig::from(1))], zero.clone()),
            ),
            lit,
        )?;
        // a − n·q ≤ |n| − 1
        self.push_relation(
            ArithConstraint::Leq(
                ArithExpr::linear(vec![(a, IBig::from(1)), (q, -n.clone())], zero),
                ArithExpr::constant(abs_n - IBig::from(1)),
            ),
            lit,
        )
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

        let mut terms = self.expr_to_monomials(lhs, false, lit)?;
        terms.extend(self.expr_to_monomials(rhs, true, lit)?);
        let rel_constant =
            Rational::from(rhs.constant.clone()) - Rational::from(lhs.constant.clone());
        let rel = mk(terms, rel_constant);

        // Derive the QDelta bound(s) (handles strict-inequality δ adjustment) before
        // the relation is moved into `add_relation`.
        let bounds = rel.to_qdelta_bounds();

        let slack = self.fresh_var();
        self.solver.lra_solver_mut().add_relation(rel, slack)?;

        if let Some(lower) = bounds.lower {
            self.solver.lra_solver_mut().assert_lower(&slack, &lower)?;
        }
        if let Some(upper) = bounds.upper {
            self.solver.lra_solver_mut().assert_upper(&slack, &upper)?;
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

impl Default for IncrementalLiraSolver {
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
    fn const_var(s: &mut IncrementalLiraSolver, c: i32) -> VarId {
        s.register_var(Some(ArithExpr::constant(c)), false).unwrap()
    }

    fn is_sat(r: &ArithCheckResult) -> bool {
        matches!(r, ArithCheckResult::Sat(_))
    }

    #[test]
    fn empty_system_is_sat() {
        let mut s = IncrementalLiraSolver::new();
        assert!(is_sat(&s.check().unwrap()));
    }

    #[test]
    fn single_feasible_constraint() {
        let mut s = IncrementalLiraSolver::new();
        let x = s.register_var(None, true).unwrap();
        // x <= 5
        s.push_constraint(ArithConstraint::Leq(term(x, 1), ArithExpr::constant(5)), 10)
            .unwrap();
        assert!(is_sat(&s.check().unwrap()));
    }

    #[test]
    fn conflicting_constraints_are_unsat_with_core() {
        let mut s = IncrementalLiraSolver::new();
        let x = s.register_var(None, true).unwrap();
        // x >= 5 (encoded as 5 <= x), lit 10
        s.push_constraint(ArithConstraint::Leq(ArithExpr::constant(5), term(x, 1)), 10)
            .unwrap();
        // x <= 1, lit 20
        s.push_constraint(ArithConstraint::Leq(term(x, 1), ArithExpr::constant(1)), 20)
            .unwrap();
        match s.check().unwrap() {
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
        let mut s = IncrementalLiraSolver::new();
        let x = s.register_var(None, true).unwrap();
        // Level 0: x >= 5.
        s.push_constraint(ArithConstraint::Leq(ArithExpr::constant(5), term(x, 1)), 10)
            .unwrap();
        assert!(is_sat(&s.check().unwrap()));

        // Level 1: add x <= 1, making the system infeasible.
        s.notify_new_decision_level();
        s.push_constraint(ArithConstraint::Leq(term(x, 1), ArithExpr::constant(1)), 20)
            .unwrap();
        assert!(matches!(s.check().unwrap(), ArithCheckResult::Unsat(_)));

        // Backtrack to level 0: the x <= 1 bound is relaxed and the system is feasible.
        s.notify_backtrack(0);
        match s.check().unwrap() {
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
            ArithCheckResult::Unsat(_) => panic!("expected SAT after backtrack"),
        }
    }

    #[test]
    fn assert_backtrack_reassert_constraint() {
        // C: x >= 5 (encoded as 5 <= x). D: x <= 1. C alone is feasible; C && D is not.
        // Exercises assert → backtrack → assert-again of the same constraint D.
        let mut s = IncrementalLiraSolver::new();
        let x = s.register_var(None, true).unwrap();

        // Assert C at level 0; feasible on its own.
        s.push_constraint(ArithConstraint::Leq(ArithExpr::constant(5), term(x, 1)), 10)
            .unwrap();
        assert!(is_sat(&s.check().unwrap()));

        // Push a decision level, assert D; C && D is infeasible.
        s.notify_new_decision_level();
        s.push_constraint(ArithConstraint::Leq(term(x, 1), ArithExpr::constant(1)), 20)
            .unwrap();
        assert!(matches!(s.check().unwrap(), ArithCheckResult::Unsat(_)));

        // Backtrack to where only C is asserted; D's bound is relaxed, so feasible again.
        s.notify_backtrack(0);
        assert!(is_sat(&s.check().unwrap()));

        // Assert D again: re-asserting the previously-backtracked constraint must once
        // more render the system infeasible.
        s.push_constraint(ArithConstraint::Leq(term(x, 1), ArithExpr::constant(1)), 20)
            .unwrap();
        assert!(matches!(s.check().unwrap(), ArithCheckResult::Unsat(_)));
    }

    #[test]
    fn definition_is_enforced_in_model() {
        let mut s = IncrementalLiraSolver::new();
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
        match s.check().unwrap() {
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
        let mut s = IncrementalLiraSolver::new();
        let x = s.register_var(None, true).unwrap();
        let y = s.register_var(None, true).unwrap();
        // x == y (via push_equality), and x == 9.
        s.push_equality(x, y, 10).unwrap();
        s.push_constraint(ArithConstraint::Eq(term(x, 1), ArithExpr::constant(9)), 20)
            .unwrap();
        match s.check().unwrap() {
            ArithCheckResult::Sat(buckets) => {
                let nine = buckets.get(&IBig::from(9)).unwrap();
                assert!(nine.contains(&x) && nine.contains(&y));
            }
            ArithCheckResult::Unsat(_) => panic!("expected SAT"),
        }
    }

    #[test]
    fn strict_inequality_conflict() {
        let mut s = IncrementalLiraSolver::new();
        let x = s.register_var(None, true).unwrap();
        // x < 3 and x > 3 (encoded as 3 < x): infeasible.
        s.push_constraint(ArithConstraint::Lt(term(x, 1), ArithExpr::constant(3)), 10)
            .unwrap();
        s.push_constraint(ArithConstraint::Lt(ArithExpr::constant(3), term(x, 1)), 20)
            .unwrap();
        assert!(matches!(s.check().unwrap(), ArithCheckResult::Unsat(_)));
    }

    #[test]
    fn model_only_reports_marked_vars() {
        let mut s = IncrementalLiraSolver::new();
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
        match s.check().unwrap() {
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
        match s.check().unwrap() {
            ArithCheckResult::Sat(buckets) => {
                assert!(buckets.get(&IBig::from(2)).unwrap().contains(&hidden));
            }
            ArithCheckResult::Unsat(_) => panic!("expected SAT"),
        }
    }

    #[test]
    fn nested_levels_backtrack_partially() {
        let mut s = IncrementalLiraSolver::new();
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
        assert!(is_sat(&s.check().unwrap()));
        // L2: x <= -1, contradicts x >= 0.
        s.notify_new_decision_level();
        s.push_constraint(
            ArithConstraint::Leq(term(x, 1), ArithExpr::constant(-1)),
            30,
        )
        .unwrap();
        assert!(matches!(s.check().unwrap(), ArithCheckResult::Unsat(_)));
        // Backtrack to L1: x <= -1 relaxed, but x <= 10 still active. Feasible.
        s.notify_backtrack(1);
        assert!(is_sat(&s.check().unwrap()));
    }

    #[test]
    fn integrality_is_enforced() {
        // `3x >= 1 && 3x <= 2` pins x to [1/3, 2/3]: the rational relaxation is feasible but
        // there is no integer in that interval, so branch-and-bound must report UNSAT. A pure
        // LRA frontend would (unsoundly) report SAT here.
        let mut s = IncrementalLiraSolver::new();
        let x = s.register_var(None, true).unwrap();
        // 3x >= 1, encoded as 1 <= 3x.
        s.push_constraint(ArithConstraint::Leq(ArithExpr::constant(1), term(x, 3)), 10)
            .unwrap();
        // 3x <= 2.
        s.push_constraint(ArithConstraint::Leq(term(x, 3), ArithExpr::constant(2)), 20)
            .unwrap();
        assert!(
            matches!(s.check().unwrap(), ArithCheckResult::Unsat(_)),
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
        let mut s = IncrementalLiraSolver::new();
        let x = s.register_var(None, true).unwrap();

        // Level 1: assert the trap, so `check` runs branch-and-bound and reports UNSAT.
        s.notify_new_decision_level();
        s.push_constraint(ArithConstraint::Leq(ArithExpr::constant(1), term(x, 3)), 10)
            .unwrap();
        s.push_constraint(ArithConstraint::Leq(term(x, 3), ArithExpr::constant(2)), 20)
            .unwrap();
        assert!(matches!(s.check().unwrap(), ArithCheckResult::Unsat(_)));

        // Backtrack to level 0: the trap's bounds are relaxed. Pin x == 0, which is feasible
        // *unless* a speculative `x >= 1` from the previous branch-and-bound leaked through.
        s.notify_backtrack(0);
        s.push_constraint(ArithConstraint::Eq(term(x, 1), ArithExpr::constant(0)), 30)
            .unwrap();
        match s.check().unwrap() {
            ArithCheckResult::Sat(buckets) => {
                assert!(
                    buckets.get(&IBig::from(0)).unwrap().contains(&x),
                    "x should be 0; a leaked x >= 1 branch bound would make this UNSAT"
                );
            }
            ArithCheckResult::Unsat(_) => {
                panic!(
                    "expected SAT: a residual branch-and-bound bound leaked across check() calls"
                )
            }
        }
    }

    #[test]
    fn div_floor_semantics_sat() {
        // x = 3, div(x, 2) = 1: floor(3/2) = 1 holds under Euclidean division.
        let mut s = IncrementalLiraSolver::new();
        let x = s.register_var(None, true).unwrap();
        let two = const_var(&mut s, 2);
        s.push_constraint(ArithConstraint::Eq(term(x, 1), ArithExpr::constant(3)), 10)
            .unwrap();
        s.push_constraint(
            ArithConstraint::Eq(div_term(x, two, 1), ArithExpr::constant(1)),
            20,
        )
        .unwrap();
        assert!(is_sat(&s.check().unwrap()));
    }

    #[test]
    fn div_constant_numerator_floor_sat() {
        // r = div(7, 2), r = 3: Euclidean 7 = 2*3 + 1.
        let mut s = IncrementalLiraSolver::new();
        let seven = const_var(&mut s, 7);
        let two = const_var(&mut s, 2);
        let r = s.register_var(None, true).unwrap();
        s.push_constraint(ArithConstraint::Eq(term(r, 1), div_term(seven, two, 1)), 10)
            .unwrap();
        s.push_constraint(ArithConstraint::Eq(term(r, 1), ArithExpr::constant(3)), 20)
            .unwrap();
        assert!(is_sat(&s.check().unwrap()));
    }

    #[test]
    fn div_wrong_quotient_unsat() {
        // r = div(7, 2), r = 4: 2*4 = 8 > 7 violates the remainder bound.
        let mut s = IncrementalLiraSolver::new();
        let seven = const_var(&mut s, 7);
        let two = const_var(&mut s, 2);
        let r = s.register_var(None, true).unwrap();
        s.push_constraint(ArithConstraint::Eq(term(r, 1), div_term(seven, two, 1)), 10)
            .unwrap();
        s.push_constraint(ArithConstraint::Eq(term(r, 1), ArithExpr::constant(4)), 20)
            .unwrap();
        assert!(matches!(s.check().unwrap(), ArithCheckResult::Unsat(_)));
    }

    #[test]
    fn div_negative_numerator_floors() {
        // div(-1, 2) = -1 under Euclidean semantics (-1 = 2*(-1) + 1).
        let mut s = IncrementalLiraSolver::new();
        let neg1 = const_var(&mut s, -1);
        let two = const_var(&mut s, 2);
        let r = s.register_var(None, true).unwrap();
        s.push_constraint(ArithConstraint::Eq(term(r, 1), div_term(neg1, two, 1)), 10)
            .unwrap();
        s.push_constraint(ArithConstraint::Eq(term(r, 1), ArithExpr::constant(-1)), 20)
            .unwrap();
        assert!(is_sat(&s.check().unwrap()));
    }

    #[test]
    fn div_negative_denominator_floors() {
        // div(9, -2) = -4 under Euclidean semantics (9 = (-2)*(-4) + 1).
        let mut s = IncrementalLiraSolver::new();
        let nine = const_var(&mut s, 9);
        let neg2 = const_var(&mut s, -2);
        let r = s.register_var(None, true).unwrap();
        s.push_constraint(ArithConstraint::Eq(term(r, 1), div_term(nine, neg2, 1)), 10)
            .unwrap();
        s.push_constraint(ArithConstraint::Eq(term(r, 1), ArithExpr::constant(-4)), 20)
            .unwrap();
        assert!(is_sat(&s.check().unwrap()));
    }

    #[test]
    fn mod_matches_euclidean_remainder() {
        // x = 7, mod(x, 3) = 1 (7 = 3*2 + 1).
        let mut s = IncrementalLiraSolver::new();
        let x = s.register_var(None, true).unwrap();
        let three = const_var(&mut s, 3);
        s.push_constraint(ArithConstraint::Eq(term(x, 1), ArithExpr::constant(7)), 10)
            .unwrap();
        s.push_constraint(
            ArithConstraint::Eq(mod_term(x, three, 1), ArithExpr::constant(1)),
            20,
        )
        .unwrap();
        assert!(is_sat(&s.check().unwrap()));
    }

    #[test]
    fn mod_out_of_range_unsat() {
        // mod(x, 3) = 5 exceeds the remainder bound (0 <= r <= 2), infeasible even over the reals.
        let mut s = IncrementalLiraSolver::new();
        let x = s.register_var(None, true).unwrap();
        let three = const_var(&mut s, 3);
        s.push_constraint(
            ArithConstraint::Eq(mod_term(x, three, 1), ArithExpr::constant(5)),
            10,
        )
        .unwrap();
        assert!(matches!(s.check().unwrap(), ArithCheckResult::Unsat(_)));
    }

    #[test]
    fn mod_lra_does_not_over_approximate_integrality() {
        // x = 7, mod(x, 3) = 2 has no integer solution (7 mod 3 = 1), but the real quotient
        // q = 5/3 satisfies the Euclidean rows, so the LIRA frontend reports Unsat.
        let mut s = IncrementalLiraSolver::new();
        let x = s.register_var(None, true).unwrap();
        let three = const_var(&mut s, 3);
        s.push_constraint(ArithConstraint::Eq(term(x, 1), ArithExpr::constant(7)), 10)
            .unwrap();
        s.push_constraint(
            ArithConstraint::Eq(mod_term(x, three, 1), ArithExpr::constant(2)),
            20,
        )
        .unwrap();
        assert!(matches!(s.check().unwrap(), ArithCheckResult::Unsat(_)));
    }

    #[test]
    fn div_constraint_backtracks() {
        // L0: div(x, 2) = 5 forces 10 <= x <= 11. L1: x <= 3 conflicts; backtrack recovers.
        let mut s = IncrementalLiraSolver::new();
        let x = s.register_var(None, true).unwrap();
        let two = const_var(&mut s, 2);
        s.push_constraint(
            ArithConstraint::Eq(div_term(x, two, 1), ArithExpr::constant(5)),
            10,
        )
        .unwrap();
        assert!(is_sat(&s.check().unwrap()));

        s.notify_new_decision_level();
        s.push_constraint(ArithConstraint::Leq(term(x, 1), ArithExpr::constant(3)), 20)
            .unwrap();
        assert!(matches!(s.check().unwrap(), ArithCheckResult::Unsat(_)));

        s.notify_backtrack(0);
        assert!(is_sat(&s.check().unwrap()));
    }

    #[test]
    fn non_constant_divisor_is_rejected() {
        let mut s = IncrementalLiraSolver::new();
        let x = s.register_var(None, true).unwrap();
        let d = s.register_var(None, false).unwrap(); // no constant definition
        assert!(
            s.push_constraint(
                ArithConstraint::Leq(div_term(x, d, 1), ArithExpr::constant(0)),
                10
            )
            .is_err()
        );
    }

    #[test]
    fn zero_divisor_is_rejected() {
        let mut s = IncrementalLiraSolver::new();
        let x = s.register_var(None, true).unwrap();
        let zero = const_var(&mut s, 0);
        assert!(
            s.push_constraint(
                ArithConstraint::Leq(div_term(x, zero, 1), ArithExpr::constant(0)),
                10
            )
            .is_err()
        );
    }

    #[test]
    fn constant_divisor_invalidated_after_backtrack() {
        // A constant divisor registered above the backtrack target has its defining
        // equality relaxed on backtrack, so it must no longer resolve as a constant.
        let mut s = IncrementalLiraSolver::new();
        let x = s.register_var(None, true).unwrap();

        // Level 1: register `two := 2`, usable as a constant divisor while its definition holds.
        s.notify_new_decision_level();
        let two = const_var(&mut s, 2);
        s.push_constraint(
            ArithConstraint::Eq(div_term(x, two, 1), ArithExpr::constant(5)),
            10,
        )
        .unwrap();
        assert!(is_sat(&s.check().unwrap()));

        // Backtrack to level 0: `two`'s defining equality is relaxed, so it is no longer
        // pinned to 2 and must be rejected as a divisor.
        s.notify_backtrack(0);
        assert!(
            s.push_constraint(
                ArithConstraint::Eq(div_term(x, two, 1), ArithExpr::constant(5)),
                20,
            )
            .is_err(),
            "divisor whose constant definition was relaxed must be rejected"
        );
    }

    #[test]
    fn constant_divisor_at_level_zero_survives_backtrack() {
        // A constant registered at level 0 stays valid as a divisor across backtracking.
        let mut s = IncrementalLiraSolver::new();
        let x = s.register_var(None, true).unwrap();
        let two = const_var(&mut s, 2);

        s.notify_new_decision_level();
        s.push_constraint(ArithConstraint::Eq(term(x, 1), ArithExpr::constant(3)), 10)
            .unwrap();
        assert!(is_sat(&s.check().unwrap()));

        // Backtrack to level 0: `two` was registered at level 0, so it survives and can
        // still serve as a divisor.
        s.notify_backtrack(0);
        s.push_constraint(
            ArithConstraint::Eq(div_term(x, two, 1), ArithExpr::constant(1)),
            20,
        )
        .unwrap();
        s.push_constraint(ArithConstraint::Eq(term(x, 1), ArithExpr::constant(3)), 30)
            .unwrap();
        assert!(is_sat(&s.check().unwrap()));
    }

    #[test]
    fn definition_at_level_zero_survives_backtrack() {
        // y := x + 3 registered at level 0. A level-1 assert of x is relaxed on backtrack,
        // but the definition equality persists (asserted at level 0), so re-pinning x
        // after backtracking still forces y = x + 3.
        let mut s = IncrementalLiraSolver::new();
        let x = s.register_var(None, true).unwrap();
        let y = s
            .register_var(
                Some(ArithExpr::linear(vec![(x, IBig::from(1))], IBig::from(3))),
                true,
            )
            .unwrap();

        // Level 1: x == 4 ⇒ y == 7.
        s.notify_new_decision_level();
        s.push_constraint(ArithConstraint::Eq(term(x, 1), ArithExpr::constant(4)), 10)
            .unwrap();
        match s.check().unwrap() {
            ArithCheckResult::Sat(b) => {
                assert!(b.get(&IBig::from(4)).unwrap().contains(&x));
                assert!(b.get(&IBig::from(7)).unwrap().contains(&y));
            }
            ArithCheckResult::Unsat(_) => panic!("expected SAT"),
        }

        // Backtrack to level 0: x == 4 relaxed, but y := x + 3 still holds. Re-assert
        // x == 100 ⇒ y == 103.
        s.notify_backtrack(0);
        s.push_constraint(
            ArithConstraint::Eq(term(x, 1), ArithExpr::constant(100)),
            20,
        )
        .unwrap();
        match s.check().unwrap() {
            ArithCheckResult::Sat(b) => {
                assert!(b.get(&IBig::from(100)).unwrap().contains(&x));
                assert!(b.get(&IBig::from(103)).unwrap().contains(&y));
            }
            ArithCheckResult::Unsat(_) => panic!("expected SAT"),
        }
    }

    #[test]
    fn definition_above_backtrack_level_is_relaxed() {
        // A definition registered above the backtrack target is relaxed like any other
        // constraint: its `VarId` stays valid, but the defined variable goes free.
        let mut s = IncrementalLiraSolver::new();
        let x = s.register_var(None, true).unwrap();
        s.push_constraint(ArithConstraint::Eq(term(x, 1), ArithExpr::constant(4)), 10)
            .unwrap();

        // Level 1: introduce y := x + 3 ⇒ y == 7.
        s.notify_new_decision_level();
        let y = s
            .register_var(
                Some(ArithExpr::linear(vec![(x, IBig::from(1))], IBig::from(3))),
                true,
            )
            .unwrap();
        match s.check().unwrap() {
            ArithCheckResult::Sat(b) => assert!(b.get(&IBig::from(7)).unwrap().contains(&y)),
            ArithCheckResult::Unsat(_) => panic!("expected SAT"),
        }

        // Backtrack to level 0: y's definition is relaxed, so y is no longer tied to
        // x + 3. Pinning y == 0 alongside the surviving x == 4 is now feasible.
        s.notify_backtrack(0);
        s.push_constraint(ArithConstraint::Eq(term(y, 1), ArithExpr::constant(0)), 20)
            .unwrap();
        match s.check().unwrap() {
            ArithCheckResult::Sat(b) => {
                assert!(b.get(&IBig::from(4)).unwrap().contains(&x));
                assert!(b.get(&IBig::from(0)).unwrap().contains(&y));
            }
            ArithCheckResult::Unsat(_) => {
                panic!("expected SAT: y should be free once its definition is relaxed")
            }
        }
    }

    #[test]
    fn reasserted_definition_recouples_variable() {
        // Full cycle: assert def → solve → backtrack (relaxing it) → solve → re-assert
        // def → solve. Re-asserting the equality must re-establish the relation.
        let mut s = IncrementalLiraSolver::new();
        let x = s.register_var(None, true).unwrap();
        s.push_constraint(ArithConstraint::Eq(term(x, 1), ArithExpr::constant(4)), 10)
            .unwrap();

        // Level 1: y := x + 3 ⇒ y == 7.
        s.notify_new_decision_level();
        let y = s
            .register_var(
                Some(ArithExpr::linear(vec![(x, IBig::from(1))], IBig::from(3))),
                true,
            )
            .unwrap();
        assert!(is_sat(&s.check().unwrap()));

        // Backtrack to level 0: y's definition is relaxed and y is free.
        s.notify_backtrack(0);
        assert!(is_sat(&s.check().unwrap()));

        // Re-assert y == x + 3 as an explicit constraint. With x == 4 still active this
        // forces y == 7 again; pinning y == 0 must now conflict.
        s.notify_new_decision_level();
        s.push_constraint(
            ArithConstraint::Eq(
                term(y, 1),
                ArithExpr::linear(vec![(x, IBig::from(1))], IBig::from(3)),
            ),
            20,
        )
        .unwrap();
        match s.check().unwrap() {
            ArithCheckResult::Sat(b) => assert!(b.get(&IBig::from(7)).unwrap().contains(&y)),
            ArithCheckResult::Unsat(_) => panic!("expected SAT with y recoupled to x + 3"),
        }

        s.notify_new_decision_level();
        s.push_constraint(ArithConstraint::Eq(term(y, 1), ArithExpr::constant(0)), 30)
            .unwrap();
        assert!(matches!(s.check().unwrap(), ArithCheckResult::Unsat(_)));
    }

    #[test]
    fn unregistered_var_is_rejected() {
        let mut s = IncrementalLiraSolver::new();
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
