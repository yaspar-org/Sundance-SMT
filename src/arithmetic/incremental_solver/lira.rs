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
//! - A pushed constraint `Σ aᵢ xᵢ ⋈ c` is normalized and tightened to the integer grid
//!   ([`Rel::normalize`], [`Rel::tighten_integral`]), giving a canonical linear form
//!   `Σ a'ᵢ xᵢ` (sorted, coprime, leading coefficient positive) and bound(s). A single-variable
//!   form `x` is bounded directly; otherwise the form's slack row is looked up in a cache and
//!   created (via [`LRASolver::add_relation`]) only on first use, so re-asserting an atom, its
//!   negation, or the same form with another constant shares one row. The tableau grows with the
//!   number of distinct forms, not the number of pushes; on backtrack the bound trail relaxes the
//!   bounds and the rows stay.
//! - Each bounded var tracks which literal set its current lower and upper bound
//!   (a backtrackable trail mirroring the solver's). Conflicts cite those literals. A bound that
//!   crosses the opposite one is never asserted; it is recorded as a pending conflict and reported
//!   by the next check.
//! - Decision levels are tracked by capturing an [`LRASolver::set_backtrack`] token at each level
//!   boundary and replaying it via [`LRASolver::backtrack`].
//! - **`div`/`mod` by a nonzero constant** (resolved from the denominator's affine form):
//!   `div(a, n)` is a quotient var `q`, shared per `(a, n)`, constrained by the single row
//!   `0 ≤ a − n·q ≤ |n| − 1`; `mod(a, n) = a − n·q`. That row is definitional, so its bounds are
//!   *permanent*: they cite no literal and are re-asserted whenever a backtrack relaxes them.
//! - **`div`/`mod` by anything else** (a variable, an uninterpreted term, or zero) is an opaque
//!   integer var, shared per `(a, b)`, with no constraints: the solver knows less about it, which
//!   is sound for conflicts, and the egraph still equates it with congruent terms. This mirrors
//!   how the translation layer treats non-linear products. From then on the solver is not exact
//!   ([`IncrementalArithSolver::is_exact`]): a model it accepts may give the term a value that
//!   is not the quotient.
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

/// Which side of a variable's bounds.
#[derive(Debug, Clone, Copy)]
enum Side {
    Lower,
    Upper,
}

/// Incremental LIRA backend: a persistent [`LIRASolver`] driven by push/pop of constraints keyed
/// by SAT literal. See the module docs for the mapping onto the incremental solver.
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
    /// `(numerator, divisor)` → opaque var for `div` (`opaque_divs`) or `mod` (`opaque_mods`)
    /// whose divisor is not a nonzero constant.
    opaque_divs: DeterministicHashMap<(VarId, VarId), Var>,
    /// See `opaque_divs`.
    opaque_mods: DeterministicHashMap<(VarId, VarId), Var>,
    /// Normalized multi-variable linear form `Σ aᵢ xᵢ` → its slack var.
    slacks: DeterministicHashMap<Vec<(Var, Rational)>, Var>,
    /// The literal that set a var's current lower bound. Vars bounded only permanently (or not
    /// at all) have no entry.
    lower_lits: DeterministicHashMap<Var, i32>,
    /// The literal that set a var's current upper bound.
    upper_lits: DeterministicHashMap<Var, i32>,
    /// Undo trail for `lower_lits` / `upper_lits`: `(var, side, previous lit)`.
    bound_trail: Vec<(Var, Side, Option<i32>)>,
    /// `bound_marks[l]` is the `bound_trail` length at the `l → l+1` decision-level boundary.
    bound_marks: Vec<usize>,
    /// A conflict found while pushing (a bound crossing the opposite one, or a constraint
    /// infeasible on its own), with the decision level it was found at. Reported by the next
    /// check; cleared by backtracking below that level.
    pending_conflict: Option<(Vec<i32>, usize)>,
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
            opaque_divs: DeterministicHashMap::new(),
            opaque_mods: DeterministicHashMap::new(),
            slacks: DeterministicHashMap::new(),
            lower_lits: DeterministicHashMap::new(),
            upper_lits: DeterministicHashMap::new(),
            bound_trail: Vec::new(),
            bound_marks: Vec::new(),
            pending_conflict: None,
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

    /// The value of a `div`/`mod` denominator if it is a nonzero constant, `None` otherwise.
    fn constant_divisor(&self, denom: VarId) -> SolverResult<Option<IBig>> {
        Ok(self
            .def(denom)?
            .as_constant()
            .filter(|n| **n != IBig::ZERO)
            .cloned())
    }

    /// The opaque var standing for `div(a, b)` (or `mod(a, b)` if `is_mod`) when `b` is not a
    /// nonzero constant, created on first use.
    fn opaque_div_mod(&mut self, is_mod: bool, a: VarId, b: VarId) -> SolverResult<Var> {
        // Both operands must be registered, as for any other term of a definition.
        self.def(a)?;
        self.def(b)?;
        let existing = if is_mod {
            self.opaque_mods.get(&(a, b))
        } else {
            self.opaque_divs.get(&(a, b))
        };
        if let Some(v) = existing {
            return Ok(*v);
        }
        let v = self.fresh_var();
        if is_mod {
            self.opaque_mods.insert((a, b), v);
        } else {
            self.opaque_divs.insert((a, b), v);
        }
        Ok(v)
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
        self.add_permanent_row(r.monomials(), bounds)?;
        self.quotients.insert((a, n.clone()), q);
        Ok(q)
    }

    /// Convert an [`ArithExpr`] to an affine form, substituting variable definitions and
    /// converting `div`/`mod` terms to quotient vars (constant divisor) or opaque vars (any other
    /// divisor).
    fn expr_to_affine(&mut self, expr: &ArithExpr) -> SolverResult<Affine> {
        let mut out = Affine::constant(expr.constant.clone());
        for (var_id, coeff) in &expr.terms {
            let def = self.def(*var_id)?.clone();
            out.add_scaled(&def, coeff);
        }
        for (a, b, coeff) in &expr.divs {
            let Some(n) = self.constant_divisor(*b)? else {
                let v = self.opaque_div_mod(false, *a, *b)?;
                out.add_term(v, coeff);
                continue;
            };
            let q = self.quotient(*a, &n)?;
            // div(a, n) = q
            out.add_term(q, coeff);
        }
        for (a, b, coeff) in &expr.mods {
            let Some(n) = self.constant_divisor(*b)? else {
                let v = self.opaque_div_mod(true, *a, *b)?;
                out.add_term(v, coeff);
                continue;
            };
            let q = self.quotient(*a, &n)?;
            // mod(a, n) = a − n·q
            let def = self.def(*a)?.clone();
            out.add_scaled(&def, coeff);
            out.add_term(q, &-(coeff * &n));
        }
        Ok(out)
    }

    /// Assert permanent `bounds` on `slack` at the current decision level.
    fn assert_permanent_bounds(&mut self, slack: Var, bounds: &Bounds<QDelta>) -> SolverResult<()> {
        let lra = self.solver.lra_solver_mut();
        // `Some(false)` (crossing an existing opposite bound) cannot happen: a permanent slack is
        // dedicated to its row, carries only these bounds, and they are consistent.
        if let Some(lower) = &bounds.lower {
            let r = lra.assert_lower(&slack, lower)?;
            debug_assert_ne!(r, Some(false), "lower bound crossed on permanent slack");
        }
        if let Some(upper) = &bounds.upper {
            let r = lra.assert_upper(&slack, upper)?;
            debug_assert_ne!(r, Some(false), "upper bound crossed on permanent slack");
        }
        Ok(())
    }

    /// Add a fresh, dedicated slack row `slack = Σ terms` with permanent `bounds`: they cite no
    /// literal and are re-asserted after any backtrack that relaxes them.
    fn add_permanent_row(
        &mut self,
        terms: Vec<Mon<Rational>>,
        bounds: Bounds<QDelta>,
    ) -> SolverResult<()> {
        let slack = self.fresh_var();
        // `add_relation` only reads the relation's terms; the bounds are asserted separately.
        self.solver
            .lra_solver_mut()
            .add_relation(Rel::mk_eq(terms, Rational::ZERO), slack)?;
        self.assert_permanent_bounds(slack, &bounds)?;
        self.permanent_by_level[self.sat_level].push((slack, bounds));
        Ok(())
    }

    /// The var to bound for a normalized linear form: the variable itself for `1·x`, otherwise
    /// the form's cached slack (adding its row on first use).
    fn bounded_var(&mut self, terms: &[Mon<Rational>]) -> SolverResult<Var> {
        if let [mon] = terms {
            // Normalized coefficients are coprime with a positive leading term.
            debug_assert_eq!(*mon.coeff_ref(), Rational::ONE);
            self.solver.lra_solver_mut().ensure_var(mon.var())?;
            return Ok(mon.var());
        }
        let key: Vec<(Var, Rational)> = terms
            .iter()
            .map(|m| (m.var(), m.coeff_ref().clone()))
            .collect();
        if let Some(slack) = self.slacks.get(&key) {
            return Ok(*slack);
        }
        let slack = self.fresh_var();
        self.solver
            .lra_solver_mut()
            .add_relation(Rel::mk_eq(terms.to_vec(), Rational::ZERO), slack)?;
        self.slacks.insert(key, slack);
        Ok(slack)
    }

    /// Assert `val` as the `side` bound of `var`, citing `lit`, at the current decision level.
    ///
    /// A bound no tighter than the current one is a no-op (the tighter bound's literal stays
    /// responsible). A bound crossing the opposite one is not asserted; the conflict clause is
    /// returned instead.
    fn assert_bound(
        &mut self,
        var: Var,
        side: Side,
        val: &QDelta,
        lit: i32,
    ) -> SolverResult<Option<Vec<i32>>> {
        let lra = self.solver.lra_solver_mut();
        let bounds = lra
            .get_bounds(&var)
            .ok_or_else(|| SolverError(format!("bounded var {var:?} is not in the tableau")))?;
        let (tighter, crosses, opposite) = match side {
            Side::Lower => (
                bounds.above_lower(val),
                bounds.above_upper(val),
                &self.upper_lits,
            ),
            Side::Upper => (
                bounds.below_upper(val),
                bounds.below_lower(val),
                &self.lower_lits,
            ),
        };
        if crosses {
            // Only literals bound these vars (permanent bounds live on dedicated slacks), so the
            // opposite bound has one.
            let other = opposite
                .get(&var)
                .expect("lira-inc: crossed bound has no literal");
            return Ok(Some(vec![-lit, -other]));
        }
        if !tighter {
            return Ok(None);
        }
        let lits = match side {
            Side::Lower => {
                lra.assert_lower(&var, val)?;
                &mut self.lower_lits
            }
            Side::Upper => {
                lra.assert_upper(&var, val)?;
                &mut self.upper_lits
            }
        };
        let prev = lits.insert(var, lit);
        self.bound_trail.push((var, side, prev));
        Ok(None)
    }

    /// Record a conflict found while pushing, unless one is already pending.
    fn set_pending_conflict(&mut self, clause: Vec<i32>) {
        debug_println!(21, 0, "[lira-inc] pending conflict {:?}", clause);
        if self.pending_conflict.is_none() {
            self.pending_conflict = Some((clause, self.sat_level));
        }
    }

    /// Register a fresh integer variable; see [`IncrementalArithSolver::register_var`]. Errors if
    /// `definition` refers to an unregistered variable.
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
    /// unregistered variable.
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
        // With a conflict pending, nothing below matters: the next check reports it, and the
        // backtrack that clears it also pops this (later-pushed) literal.
        if self.pending_conflict.is_some() {
            return Ok(());
        }

        // A constraint with no variables left is decided by its constant.
        if diff.terms.is_empty() {
            let holds = match constraint {
                ArithConstraint::Leq(..) => Rational::ZERO <= c,
                ArithConstraint::Lt(..) => Rational::ZERO < c,
                ArithConstraint::Eq(..) => Rational::ZERO == c,
            };
            if !holds {
                self.set_pending_conflict(vec![-lit]);
            }
            return Ok(());
        }

        // Normalize and tighten to the integer grid (all internal vars are integers), then derive
        // the QDelta bound(s) (handles strict-inequality δ adjustment for anything left strict).
        let mut rel = mk(diff.monomials(), c);
        rel.normalize();
        if rel.tighten_integral() {
            // No integer solution (e.g. `2x + 2y = 1`): the rational relaxation is feasible and
            // branch-and-bound could diverge, so the constraint is a conflict on its own.
            self.set_pending_conflict(vec![-lit]);
            return Ok(());
        }
        let bounds = rel.to_qdelta_bounds();
        let var = self.bounded_var(rel.terms_ref())?;
        for (side, val) in [(Side::Lower, &bounds.lower), (Side::Upper, &bounds.upper)] {
            if let Some(val) = val
                && let Some(clause) = self.assert_bound(var, side, val, lit)?
            {
                self.set_pending_conflict(clause);
                return Ok(());
            }
        }
        self.pending_partial += 1;
        debug_println!(
            21,
            0,
            "[lira-inc] pushed constraint lit={} on {:?} at level {}",
            lit,
            var,
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
    ///
    /// A [`Conflict`] names vars, not which of their bounds it uses, so both current bounds'
    /// literals are cited (a superset of the Farkas explanation, hence still a valid clause).
    fn conflict_clause(&self, conflict: &Conflict<Var>) -> Vec<i32> {
        let lits: DeterministicHashSet<i32> = conflict
            .iter()
            .flat_map(|var| [self.lower_lits.get(var), self.upper_lits.get(var)])
            .flatten()
            .map(|lit| -lit)
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
        if let Some((clause, _)) = &self.pending_conflict {
            return Ok(ArithCheckResult::Unsat(clause.clone()));
        }
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
        if let Some((clause, _)) = &self.pending_conflict {
            return Ok(PartialCheckResult::Unsat(clause.clone()));
        }
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
        self.bound_marks.push(self.bound_trail.len());
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
        // Restore which literal is responsible for each bound, mirroring the solver's trail.
        let mark = self.bound_marks[level];
        self.bound_marks.truncate(level);
        for (var, side, prev) in self.bound_trail.drain(mark..).rev() {
            let lits = match side {
                Side::Lower => &mut self.lower_lits,
                Side::Upper => &mut self.upper_lits,
            };
            match prev {
                Some(lit) => lits.insert(var, lit),
                None => lits.remove(&var),
            };
        }
        if self
            .pending_conflict
            .as_ref()
            .is_some_and(|(_, l)| *l > level)
        {
            self.pending_conflict = None;
        }
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
            self.assert_permanent_bounds(slack, &bounds)
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

    fn is_exact(&self) -> bool {
        self.opaque_divs.is_empty() && self.opaque_mods.is_empty()
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
    fn non_constant_divisor_is_opaque() {
        // div(x, d) and mod(x, d) with a free d are opaque vars: each is shared by every
        // occurrence, so div(x, d) <= 0 and div(x, d) >= 1 conflict, but div(x, d) and mod(x, d)
        // are unrelated.
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        let d = s.try_register_var(None, false).unwrap(); // no constant definition
        let q = s.try_register_var(Some(div_term(x, d, 1)), true).unwrap();
        s.try_push_constraint(
            ArithConstraint::Leq(div_term(x, d, 1), ArithExpr::constant(0)),
            10,
        )
        .unwrap();
        s.try_push_constraint(
            ArithConstraint::Leq(ArithExpr::constant(7), mod_term(x, d, 1)),
            20,
        )
        .unwrap();
        match s.try_check().unwrap() {
            ArithCheckResult::Sat(buckets) => {
                let q_val = buckets
                    .iter()
                    .find(|(_, vars)| vars.contains(&q))
                    .map(|(v, _)| v.clone())
                    .expect("q in model");
                assert!(q_val <= IBig::ZERO, "div(x, d) = {q_val} should be <= 0");
            }
            r => panic!("expected SAT, got {r:?}"),
        }
        s.notify_new_decision_level();
        s.try_push_constraint(ArithConstraint::Leq(ArithExpr::constant(1), term(q, 1)), 30)
            .unwrap();
        match s.try_check().unwrap() {
            ArithCheckResult::Unsat(core) => {
                assert!(core.contains(&-10) && core.contains(&-30), "core {core:?}");
                assert!(
                    !core.contains(&-20),
                    "mod(x, d) is unrelated: core {core:?}"
                );
            }
            r => panic!("expected UNSAT, got {r:?}"),
        }
    }

    #[test]
    fn opaque_div_mod_makes_the_solver_inexact() {
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        let three = const_var(&mut s, 3);
        s.try_register_var(Some(div_term(x, three, 1)), true)
            .unwrap();
        assert!(s.is_exact(), "div by a constant is interpreted");
        let d = s.try_register_var(None, false).unwrap();
        s.try_register_var(Some(mod_term(x, d, 1)), true).unwrap();
        assert!(!s.is_exact(), "mod by a variable is opaque");
    }

    #[test]
    fn zero_divisor_is_opaque() {
        // SMT-LIB leaves div/mod by zero unspecified, so they are opaque too.
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        let zero = const_var(&mut s, 0);
        s.try_push_constraint(
            ArithConstraint::Eq(div_term(x, zero, 1), ArithExpr::constant(5)),
            10,
        )
        .unwrap();
        s.try_push_constraint(
            ArithConstraint::Eq(mod_term(x, zero, 1), ArithExpr::constant(-3)),
            20,
        )
        .unwrap();
        assert!(is_sat(&s.try_check().unwrap()));
    }

    #[test]
    fn unregistered_divisor_is_an_error() {
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        assert!(
            s.try_push_constraint(
                ArithConstraint::Leq(div_term(x, 99, 1), ArithExpr::constant(0)),
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
        let y = s.try_register_var(None, true).unwrap();
        let sum = ArithExpr::linear(vec![(x, IBig::from(1)), (y, IBig::from(1))], IBig::ZERO);
        // x + y >= 5, x <= 1, y <= 1: infeasible already over the reals, but only via simplex.
        s.try_push_constraint(ArithConstraint::Leq(ArithExpr::constant(5), sum), 1)
            .unwrap();
        s.try_push_constraint(ArithConstraint::Leq(term(x, 1), ArithExpr::constant(1)), 2)
            .unwrap();
        s.try_push_constraint(ArithConstraint::Leq(term(y, 1), ArithExpr::constant(1)), 3)
            .unwrap();
        // Below the batch threshold the check is skipped.
        assert!(matches!(
            s.try_check_partial_trail().unwrap(),
            PartialCheckResult::Unchanged
        ));
        // Pad with redundant constraints up to the threshold.
        for lit in 4..=(PARTIAL_CHECK_ASSERTION_BATCH as i32) {
            s.try_push_constraint(
                ArithConstraint::Leq(term(x, 1), ArithExpr::constant(100 + lit)),
                lit,
            )
            .unwrap();
        }
        match s.try_check_partial_trail().unwrap() {
            PartialCheckResult::Unsat(mut core) => {
                core.sort();
                assert_eq!(core, vec![-3, -2, -1]);
            }
            r => panic!("expected partial UNSAT, got {r:?}"),
        }
    }

    #[test]
    fn crossing_bounds_conflict_immediately() {
        // x >= 5 then x <= 1 are direct bounds on x; the second crosses the first and is reported
        // by the next (even partial, unbatched) check, citing exactly the two literals.
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        s.try_push_constraint(ArithConstraint::Leq(ArithExpr::constant(5), term(x, 1)), 1)
            .unwrap();
        s.notify_new_decision_level();
        s.try_push_constraint(ArithConstraint::Leq(term(x, 1), ArithExpr::constant(1)), 2)
            .unwrap();
        match s.try_check_partial_trail().unwrap() {
            PartialCheckResult::Unsat(mut core) => {
                core.sort();
                assert_eq!(core, vec![-2, -1]);
            }
            r => panic!("expected partial UNSAT, got {r:?}"),
        }
        // Backtracking below the level it was found at clears the pending conflict.
        s.notify_backtrack(0);
        assert!(is_sat(&s.try_check().unwrap()));
    }

    #[test]
    fn pending_conflict_survives_backtrack_to_its_level() {
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        s.notify_new_decision_level();
        s.try_push_constraint(ArithConstraint::Leq(ArithExpr::constant(5), term(x, 1)), 1)
            .unwrap();
        s.try_push_constraint(ArithConstraint::Leq(term(x, 1), ArithExpr::constant(1)), 2)
            .unwrap();
        s.notify_new_decision_level();
        s.notify_backtrack(1);
        assert!(matches!(s.try_check().unwrap(), ArithCheckResult::Unsat(_)));
        s.notify_backtrack(0);
        assert!(is_sat(&s.try_check().unwrap()));
    }

    #[test]
    fn shared_form_reuses_slack_and_tracks_tightest_lit() {
        // x + y <= 5 (lit 1) and 2x + 2y <= 7 (lit 2, i.e. x + y <= 3) share one slack. The
        // conflict with x + y >= 4 cites the tighter lit 2; after backtracking it away, the
        // responsible lit reverts to 1.
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        let y = s.try_register_var(None, true).unwrap();
        let sum =
            |k: i32| ArithExpr::linear(vec![(x, IBig::from(k)), (y, IBig::from(k))], IBig::ZERO);
        s.try_push_constraint(ArithConstraint::Leq(sum(1), ArithExpr::constant(5)), 1)
            .unwrap();
        s.notify_new_decision_level();
        s.try_push_constraint(ArithConstraint::Leq(sum(2), ArithExpr::constant(7)), 2)
            .unwrap();
        assert_eq!(s.slacks.len(), 1);
        s.notify_new_decision_level();
        s.try_push_constraint(ArithConstraint::Leq(ArithExpr::constant(4), sum(1)), 3)
            .unwrap();
        assert_eq!(s.slacks.len(), 1, "opposite polarity must reuse the slack");
        match s.try_check().unwrap() {
            ArithCheckResult::Unsat(mut core) => {
                core.sort();
                assert_eq!(core, vec![-3, -2]);
            }
            r => panic!("expected UNSAT, got {r:?}"),
        }
        s.notify_backtrack(1);
        s.notify_backtrack(0);
        s.try_push_constraint(ArithConstraint::Leq(ArithExpr::constant(6), sum(1)), 4)
            .unwrap();
        match s.try_check().unwrap() {
            ArithCheckResult::Unsat(mut core) => {
                core.sort();
                assert_eq!(core, vec![-4, -1]);
            }
            r => panic!("expected UNSAT, got {r:?}"),
        }
    }

    #[test]
    fn single_var_constraints_add_no_rows() {
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        for (lit, c) in [(1, 10), (2, 7), (3, 9)] {
            s.try_push_constraint(
                ArithConstraint::Leq(term(x, 1), ArithExpr::constant(c)),
                lit,
            )
            .unwrap();
        }
        // 3x >= 4 tightens to x >= 2.
        s.try_push_constraint(ArithConstraint::Leq(ArithExpr::constant(4), term(x, 3)), 4)
            .unwrap();
        assert!(s.slacks.is_empty());
        assert_eq!(s.upper_lits.get(&Var::int(2)), Some(&2));
        assert_eq!(s.lower_lits.get(&Var::int(2)), Some(&4));
        assert!(is_sat(&s.try_check().unwrap()));
    }

    /// A test constraint `a·x + b·y ⋈ c` over two integer vars; `kind` 0/1/2 = `≤`/`<`/`=`.
    #[derive(Clone, Copy, Debug)]
    struct TestCon {
        a: i64,
        b: i64,
        kind: u8,
        c: i64,
    }

    impl TestCon {
        fn holds(&self, x: i64, y: i64) -> bool {
            let l = self.a * x + self.b * y;
            match self.kind {
                0 => l <= self.c,
                1 => l < self.c,
                _ => l == self.c,
            }
        }

        fn to_arith(self, x: VarId, y: VarId) -> ArithConstraint {
            let l = ArithExpr::linear(
                vec![(x, IBig::from(self.a)), (y, IBig::from(self.b))],
                IBig::ZERO,
            );
            let r = ArithExpr::constant(self.c);
            match self.kind {
                0 => ArithConstraint::Leq(l, r),
                1 => ArithConstraint::Lt(l, r),
                _ => ArithConstraint::Eq(l, r),
            }
        }
    }

    /// Whether the constraints have a common integer solution in `[-r, r]²`.
    fn brute_force_sat(cons: &[TestCon], r: i64) -> bool {
        (-r..=r).any(|x| (-r..=r).any(|y| cons.iter().all(|c| c.holds(x, y))))
    }

    #[test]
    fn randomized_verdicts_and_cores_match_brute_force() {
        // Deterministic LCG.
        let mut state: u64 = 0x2545_f491_4f6c_dd1d;
        let mut next = |n: u64| {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            (state >> 33) % n
        };
        for _round in 0..300 {
            let mut s = LiraIncrementalState::new();
            let x = s.try_register_var(None, true).unwrap();
            let y = s.try_register_var(None, true).unwrap();
            // Box both vars to [-4, 4] with literals of their own (direct bounds) so
            // branch-and-bound terminates and must cite them.
            let mut cons: Vec<TestCon> = vec![
                TestCon {
                    a: 1,
                    b: 0,
                    kind: 0,
                    c: 4,
                },
                TestCon {
                    a: -1,
                    b: 0,
                    kind: 0,
                    c: 4,
                },
                TestCon {
                    a: 0,
                    b: 1,
                    kind: 0,
                    c: 4,
                },
                TestCon {
                    a: 0,
                    b: -1,
                    kind: 0,
                    c: 4,
                },
            ];
            // `active[l]`: indices into `cons` pushed at level `l` (lit = index + 1).
            let mut active: Vec<Vec<usize>> = vec![(0..4).collect()];
            for (i, con) in cons.iter().enumerate() {
                s.try_push_constraint(con.to_arith(x, y), i as i32 + 1)
                    .unwrap();
            }
            for _step in 0..12 {
                match next(10) {
                    0..=1 => {
                        s.notify_new_decision_level();
                        active.push(Vec::new());
                    }
                    2 if active.len() > 1 => {
                        let level = next(active.len() as u64 - 1) as usize;
                        s.notify_backtrack(level);
                        active.truncate(level + 1);
                    }
                    _ => {
                        let con = TestCon {
                            a: next(7) as i64 - 3,
                            b: next(7) as i64 - 3,
                            kind: next(3) as u8,
                            c: next(13) as i64 - 6,
                        };
                        cons.push(con);
                        let i = cons.len() - 1;
                        s.try_push_constraint(con.to_arith(x, y), i as i32 + 1)
                            .unwrap();
                        active.last_mut().unwrap().push(i);
                    }
                }
                let live: Vec<TestCon> = active.iter().flatten().map(|&i| cons[i]).collect();
                let expect_sat = brute_force_sat(&live, 4);
                match s.try_check().unwrap() {
                    ArithCheckResult::Sat(buckets) => {
                        assert!(expect_sat, "SAT reported for {live:?}");
                        let val = |v| {
                            let (k, _) = buckets.iter().find(|(_, vs)| vs.contains(&v)).unwrap();
                            i64::try_from(k.clone()).unwrap()
                        };
                        let (vx, vy) = (val(x), val(y));
                        assert!(
                            live.iter().all(|c| c.holds(vx, vy)),
                            "bad model {vx},{vy} for {live:?}"
                        );
                    }
                    ArithCheckResult::Unsat(core) => {
                        assert!(!expect_sat, "UNSAT reported for {live:?}");
                        let core_cons: Vec<TestCon> = core
                            .iter()
                            .map(|lit| {
                                let i = (-lit - 1) as usize;
                                assert!(
                                    active.iter().flatten().any(|&j| j == i),
                                    "core cites inactive lit {}",
                                    -lit
                                );
                                cons[i]
                            })
                            .collect();
                        // Integer points of these small systems lie well inside [-40, 40]².
                        assert!(
                            !brute_force_sat(&core_cons, 40),
                            "unsound core {core_cons:?} for {live:?}"
                        );
                    }
                    ArithCheckResult::Unknown => panic!("unexpected UNKNOWN for {live:?}"),
                }
            }
        }
    }

    #[test]
    fn partial_check_ignores_integrality() {
        // x + y = 1 and x - y = 0 pin x = y = 1/2: feasible over the reals (each constraint is
        // integer-tight on its own), but not over the integers. The partial check reports Sat;
        // the full check (branch-and-bound) reports Unsat.
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        let y = s.try_register_var(None, true).unwrap();
        let sum = ArithExpr::linear(vec![(x, IBig::from(1)), (y, IBig::from(1))], IBig::ZERO);
        let diff = ArithExpr::linear(vec![(x, IBig::from(1)), (y, IBig::from(-1))], IBig::ZERO);
        s.try_push_constraint(ArithConstraint::Eq(sum, ArithExpr::constant(1)), 1)
            .unwrap();
        s.try_push_constraint(ArithConstraint::Eq(diff, ArithExpr::constant(0)), 2)
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
    fn gcd_infeasible_equality_is_unsat() {
        // 2x + 2y = 1 has no integer solution (gcd 2 does not divide 1) but is feasible over the
        // reals and unbounded, where branch-and-bound would diverge. It is refuted on its own.
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        let y = s.try_register_var(None, true).unwrap();
        s.try_push_constraint(
            ArithConstraint::Eq(
                ArithExpr::linear(vec![(x, IBig::from(2)), (y, IBig::from(2))], IBig::from(0)),
                ArithExpr::constant(1),
            ),
            10,
        )
        .unwrap();
        match s.try_check().unwrap() {
            ArithCheckResult::Unsat(core) => assert_eq!(core, vec![-10]),
            r => panic!("expected UNSAT, got {r:?}"),
        }
    }

    /// `x = 2a` and `x = 2b + 1`: no integer solution, but each equality is tight on its own and
    /// the rational relaxation is unbounded, so branch-and-bound never terminates.
    fn push_parity_conflict(s: &mut LiraIncrementalState) {
        let x = s.try_register_var(None, true).unwrap();
        let a = s.try_register_var(None, true).unwrap();
        let b = s.try_register_var(None, true).unwrap();
        s.try_push_constraint(ArithConstraint::Eq(term(x, 1), term(a, 2)), 10)
            .unwrap();
        let two_b_plus_one = ArithExpr::linear(vec![(b, IBig::from(2))], IBig::ONE);
        s.try_push_constraint(ArithConstraint::Eq(term(x, 1), two_b_plus_one), 20)
            .unwrap();
    }

    #[test]
    fn branch_and_bound_stops_at_deadline() {
        // Deadline already passed: branch-and-bound gives up at its first branch.
        let config = SolverConfig {
            deadline: Some(std::time::Instant::now()),
            ..SolverConfig::default()
        };
        let mut s = LiraIncrementalState::with_config(config);
        push_parity_conflict(&mut s);
        assert!(matches!(s.try_check().unwrap(), ArithCheckResult::Unknown));

        // Deadline during the search: the search, and the unwinding of its deep stack, end
        // shortly after it.
        let start = std::time::Instant::now();
        let config = SolverConfig {
            deadline: Some(start + std::time::Duration::from_millis(300)),
            ..SolverConfig::default()
        };
        let mut s = LiraIncrementalState::with_config(config);
        push_parity_conflict(&mut s);
        assert!(matches!(s.try_check().unwrap(), ArithCheckResult::Unknown));
        assert!(
            start.elapsed() < std::time::Duration::from_secs(10),
            "took {:?}",
            start.elapsed()
        );
        // Giving up leaves no stale conflict: after backtracking past the constraints, the
        // (empty) system is not reported Unsat. It may still be Unknown, as the deadline has
        // passed.
        let mut s = LiraIncrementalState::with_config(SolverConfig {
            deadline: Some(std::time::Instant::now()),
            ..SolverConfig::default()
        });
        s.notify_new_decision_level();
        push_parity_conflict(&mut s);
        assert!(matches!(s.try_check().unwrap(), ArithCheckResult::Unknown));
        s.notify_backtrack(0);
        assert!(!matches!(
            s.try_check().unwrap(),
            ArithCheckResult::Unsat(_)
        ));
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
        // x + y = 1 and x - y = 0 pin x = y = 1/2: no integer solution, but each constraint is
        // tight on its own, so showing it needs branching, which the one-solve budget forbids.
        s.try_push_constraint(
            ArithConstraint::Eq(
                ArithExpr::linear(vec![(x, IBig::from(1)), (y, IBig::from(1))], IBig::from(0)),
                ArithExpr::constant(1),
            ),
            10,
        )
        .unwrap();
        s.try_push_constraint(
            ArithConstraint::Eq(
                ArithExpr::linear(vec![(x, IBig::from(1)), (y, IBig::from(-1))], IBig::from(0)),
                ArithExpr::constant(0),
            ),
            20,
        )
        .unwrap();
        assert!(matches!(s.try_check().unwrap(), ArithCheckResult::Unknown));
    }

    #[test]
    fn unbounded_integer_strip_is_unsat() {
        // −1 < x − y < 0: rationally feasible, unbounded, no integer point. Integer tightening
        // makes the relaxation infeasible, so branch-and-bound (which diverges here) never runs.
        let mut s = LiraIncrementalState::new();
        let x = s.try_register_var(None, true).unwrap();
        let y = s.try_register_var(None, true).unwrap();
        let x_minus_y =
            ArithExpr::linear(vec![(x, IBig::from(1)), (y, IBig::from(-1))], IBig::ZERO);
        s.try_push_constraint(
            ArithConstraint::Lt(x_minus_y.clone(), ArithExpr::constant(0)),
            1,
        )
        .unwrap();
        s.try_push_constraint(ArithConstraint::Lt(ArithExpr::constant(-1), x_minus_y), 2)
            .unwrap();
        match s.try_check().unwrap() {
            ArithCheckResult::Unsat(core) => {
                assert!(core.contains(&-1) && core.contains(&-2), "core {core:?}")
            }
            r => panic!("expected UNSAT, got {r:?}"),
        }
    }
}
