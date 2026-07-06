// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Incremental arithmetic solver skeleton (Stage 1 of the incremental-arithmetic plan).
//!
//! The one-shot pipeline ([`crate::arithmetic::lialp`]) rebuilds a [`ConvContext`] +
//! `LRASolver` from scratch on every `check_integer_constraints_satisfiable` call. This
//! module prototypes a long-lived alternative: an [`IncrementalArithSolver`] that **owns**
//! an [`LRASolver`] for the lifetime of the search and exposes bound assertion, a full
//! feasibility check, and push/pop scoping directly on top of it.
//!
//! The design leans entirely on machinery the `LRASolver` already provides:
//! [`LRASolver::assert_lower`]/[`LRASolver::assert_upper`] (tighten one bound and report
//! immediate bound-vs-bound conflicts), [`LRASolver::set_backtrack`]/
//! [`LRASolver::backtrack`] (the bound trail, already exercised by LIRA branch-and-bound),
//! and [`LRASolver::solve`] (a full simplex check that can be re-run after new bounds are
//! asserted).
//!
//! ## Scope of Stage 1
//!
//! This is the **skeleton + API contract + determinism story + isolated unit tests only.**
//! Deliberately out of scope (later stages of the plan):
//!
//! - Building the static tableau by walking `SolverState.arithmetic_terms` (Stage 2). Here
//!   the caller supplies a ready-made `LRASolver` and registers the atoms it cares about,
//!   so the type is unit-testable with no `SolverState` and no propagator.
//! - Translating conflicts/models from internal [`Var`]s back to SAT literals / egraph
//!   terms (Stage 4). Stage 1 stays entirely in `Var` space.
//! - Wiring into [`crate::cadical_propagator`] (Stage 7).
//!
//! ## Determinism
//!
//! Every map/set here is a [`DeterministicHashMap`]/[`DeterministicHashSet`] (BTree-backed)
//! keyed on [`AtomId`] or [`Var`], both of which are `Ord`. Iteration order is therefore a
//! deterministic function of the keys and independent of run-to-run hashing — matching the
//! solver-wide determinism requirement in `src/utils.rs`.

use crate::arithmetic::lia::config::SolverConfig;
use crate::arithmetic::lia::linear_system::Constraint;
use crate::arithmetic::lia::lra_solver::LRASolver;
use crate::arithmetic::lia::qdelta::QDelta;
use crate::arithmetic::lia::solver_result::{Assignment, Conflict, SolverDecision};
use crate::arithmetic::lia::stats::Stats as LiaStats;
use crate::arithmetic::lia::variables::Var;
use crate::debug_println;
use crate::utils::DeterministicHashMap;
use dashu::Rational;

/// Opaque handle for a registered arithmetic atom.
///
/// An atom is a single comparison (e.g. `s <= 3`) over a slack [`Var`] that already exists
/// in the owned `LRASolver`. Registration records the *latent* bound the atom would assert
/// without asserting it yet; [`IncrementalArithSolver::assert_atom`] activates it later.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AtomId(pub usize);

/// A backtracking scope marker returned by [`IncrementalArithSolver::push`] and consumed by
/// [`IncrementalArithSolver::pop`]. Wraps the underlying `LRASolver` backtrack level.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Level(pub usize);

/// Outcome of asserting a single atom's bound(s).
///
/// Mirrors the three-way return of [`LRASolver::assert_lower`]/[`LRASolver::assert_upper`]
/// (`Some(false)` / `Some(true)` / `None`). For an equality atom (which asserts both a lower
/// and an upper bound), the outcome is the "worst" of the two: any `Conflict` wins, otherwise
/// any `Unknown` wins, otherwise `Sat`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssertOutcome {
    /// The new bound directly contradicts an existing bound on the same slack; the system is
    /// infeasible without any simplex step. A subsequent [`IncrementalArithSolver::check`]
    /// will report the conflict.
    Conflict,
    /// The new bound is consistent with existing bounds and the current assignment already
    /// satisfies it.
    Sat,
    /// The new bound is consistent with existing bounds, but overall satisfiability is
    /// unknown until [`IncrementalArithSolver::check`] runs.
    Unknown,
}

impl AssertOutcome {
    /// Fold a raw `assert_lower`/`assert_upper` return into an [`AssertOutcome`].
    fn from_raw(raw: Option<bool>) -> Self {
        match raw {
            Some(false) => AssertOutcome::Conflict,
            Some(true) => AssertOutcome::Sat,
            None => AssertOutcome::Unknown,
        }
    }

    /// Combine two outcomes, keeping the most pessimistic (`Conflict` > `Unknown` > `Sat`).
    fn combine(self, other: Self) -> Self {
        match (self, other) {
            (AssertOutcome::Conflict, _) | (_, AssertOutcome::Conflict) => AssertOutcome::Conflict,
            (AssertOutcome::Unknown, _) | (_, AssertOutcome::Unknown) => AssertOutcome::Unknown,
            _ => AssertOutcome::Sat,
        }
    }
}

/// Result of a full feasibility [`IncrementalArithSolver::check`] at the current bound set.
///
/// Still expressed in internal [`Var`] space; literal/term translation is Stage 4.
#[derive(Debug)]
pub enum CheckResult {
    /// Feasible: an assignment satisfying all asserted bounds.
    Sat(Assignment<Var>, LiaStats),
    /// Infeasible: a conflict set of slack [`Var`]s explaining the infeasibility.
    Unsat(Conflict<Var>, LiaStats),
    /// The solver could not decide (e.g. incomplete integer reasoning).
    Unknown(LiaStats),
}

/// The latent bound(s) an atom would assert, precomputed at registration time.
///
/// Uses the same rational→[`QDelta`] mapping as `Rel::to_qdelta_bounds`
/// (`linear_system.rs`): `Le` → upper `c`, `Ge` → lower `c`, `Lt` → upper `c − δ`,
/// `Gt` → lower `c + δ`, `Eq` → both lower and upper `c`.
#[derive(Debug, Clone)]
struct LatentBound {
    /// Slack variable the bound is asserted on. Must already exist in the owned solver.
    slack: Var,
    /// Lower bound to assert, if any.
    lower: Option<QDelta>,
    /// Upper bound to assert, if any.
    upper: Option<QDelta>,
}

impl LatentBound {
    /// Build the latent bound for `slack <constraint> threshold`.
    fn new(slack: Var, constraint: Constraint, threshold: Rational) -> Self {
        let c = QDelta::from(threshold);
        let (lower, upper) = match constraint {
            Constraint::Eq => (Some(c.clone()), Some(c)),
            Constraint::Le => (None, Some(c)),
            Constraint::Ge => (Some(c), None),
            // strict bounds are encoded with the qdelta infinitesimal
            Constraint::Lt => (None, Some(c - QDelta::DELTA)),
            Constraint::Gt => (Some(c + QDelta::DELTA), None),
        };
        LatentBound {
            slack,
            lower,
            upper,
        }
    }
}

/// A long-lived incremental arithmetic solver over a fixed slack-variable set.
///
/// Owns an [`LRASolver`] and an atom registry. Runtime incrementality is *purely bound
/// assertion/retraction* on pre-existing slacks — no rows or variables are added after
/// construction (that static-tableau construction is Stage 2).
#[derive(Debug)]
pub struct IncrementalArithSolver {
    /// The persistent real-arithmetic solver. All slacks referenced by registered atoms must
    /// already exist here.
    lra: LRASolver,
    /// Solver configuration (currently unused at Stage 1; retained for the LIRA wrap-up in
    /// Stage 5).
    #[allow(dead_code)]
    config: SolverConfig,
    /// Registry: atom → the latent bound it would assert. `AtomId(i)` indexes insertion order.
    atoms: DeterministicHashMap<AtomId, LatentBound>,
    /// Registry: SAT literal → its registered atom. Populated by the static builder
    /// (Stage 2); the durable replacement for the one-shot path's per-call `slack_to_lits`.
    /// Both `+lit` and `-lit` for an atom map to distinct [`AtomId`]s asserting opposite
    /// bound directions on the same slack.
    literal_atoms: DeterministicHashMap<i32, AtomId>,
    /// Next fresh [`AtomId`].
    next_atom: usize,
    /// Best-effort trail of asserted atoms and the scope level they were asserted at, used to
    /// truncate on [`IncrementalArithSolver::pop`]. Bound *values* are restored by the
    /// `LRASolver`'s own bound trail; this trail only tracks which atoms are logically live
    /// (needed for Stage 4 core reconstruction).
    asserted: Vec<(AtomId, usize)>,
    /// Sticky record of a conflict detected *at assert time*.
    ///
    /// [`LRASolver::assert_lower`]/[`LRASolver::assert_upper`] report an immediate
    /// bound-vs-bound conflict by returning `Some(false)` but **do not store** the rejected
    /// bound (see `lra_solver.rs`). So a later [`check`](Self::check) would not rediscover it.
    /// We latch the conflicting slack (with the scope level it was found at) here so that
    /// [`check`](Self::check) faithfully reports `Unsat` until the offending scope is popped.
    conflict: Option<(Var, usize)>,
}

impl IncrementalArithSolver {
    /// Wrap an already-constructed [`LRASolver`] (e.g. from `LinearSystem::to_lra_solver` or
    /// `LRASolver::from_eqs`).
    pub fn new(lra: LRASolver, config: SolverConfig) -> Self {
        IncrementalArithSolver {
            lra,
            config,
            atoms: DeterministicHashMap::new(),
            literal_atoms: DeterministicHashMap::new(),
            next_atom: 0,
            asserted: Vec::new(),
            conflict: None,
        }
    }

    /// The current scope level, read live from the owned solver so it is always authoritative
    /// (the solver's [`LRASolver::backtrack_level`] is a monotonically increasing timestamp,
    /// unaffected by `backtrack`, and is *not* bumped by `set_backtrack` when already UNSAT).
    fn current_level(&self) -> usize {
        self.lra.backtrack_level()
    }

    /// Register a comparison atom `slack <constraint> threshold` without asserting it.
    ///
    /// Returns an [`AtomId`] to pass to [`assert_atom`](Self::assert_atom). The `slack` must
    /// already be a variable in the owned solver; that is checked lazily at assert time.
    pub fn register_atom(&mut self, slack: Var, constraint: Constraint, threshold: Rational) -> AtomId {
        let id = AtomId(self.next_atom);
        self.next_atom += 1;
        self.atoms
            .insert(id, LatentBound::new(slack, constraint, threshold));
        id
    }

    /// Register a comparison atom and associate it with a SAT literal.
    ///
    /// Like [`register_atom`](Self::register_atom), but also records `lit -> AtomId` so the
    /// atom can be asserted from the SAT model via [`assert_literal`](Self::assert_literal).
    /// Used by the static builder to register both polarities of each arithmetic atom.
    pub fn register_literal_atom(
        &mut self,
        lit: i32,
        slack: Var,
        constraint: Constraint,
        threshold: Rational,
    ) -> AtomId {
        let id = self.register_atom(slack, constraint, threshold);
        self.literal_atoms.insert(lit, id);
        id
    }

    /// Assert the atom associated with a SAT literal, if any.
    ///
    /// Returns `None` when `lit` is not a registered arithmetic atom (so callers can pass a
    /// whole SAT model and let non-arithmetic literals fall through). Otherwise behaves like
    /// [`assert_atom`](Self::assert_atom).
    pub fn assert_literal(&mut self, lit: i32) -> Option<AssertOutcome> {
        let atom = *self.literal_atoms.get(&lit)?;
        Some(self.assert_atom(atom))
    }

    /// Look up the [`AtomId`] registered for a SAT literal, if any.
    pub fn atom_for_literal(&self, lit: i32) -> Option<AtomId> {
        self.literal_atoms.get(&lit).copied()
    }

    /// Number of registered atoms.
    pub fn num_atoms(&self) -> usize {
        self.atoms.len()
    }

    /// Assert a previously-registered atom, tightening its slack's bound(s).
    ///
    /// Cheap: at most two [`LRASolver::assert_lower`]/[`LRASolver::assert_upper`] calls. May
    /// detect an immediate bound-vs-bound conflict (returns [`AssertOutcome::Conflict`]) but
    /// does not run simplex — call [`check`](Self::check) for that.
    ///
    /// # Panics
    ///
    /// Panics if `atom` was not produced by this solver's [`register_atom`](Self::register_atom),
    /// or if its slack does not exist in the owned solver.
    pub fn assert_atom(&mut self, atom: AtomId) -> AssertOutcome {
        let bound = self
            .atoms
            .get(&atom)
            .unwrap_or_else(|| panic!("assert_atom: unknown atom {atom:?}"))
            .clone();
        debug_println!(
            10,
            0,
            "incremental: assert_atom {:?} on slack {:?} (lower={:?}, upper={:?})",
            atom,
            bound.slack,
            bound.lower,
            bound.upper
        );

        let mut outcome = AssertOutcome::Sat;
        if let Some(l) = &bound.lower {
            let raw = self
                .lra
                .assert_lower(&bound.slack, l)
                .expect("assert_atom: assert_lower failed");
            outcome = outcome.combine(AssertOutcome::from_raw(raw));
        }
        if let Some(u) = &bound.upper {
            let raw = self
                .lra
                .assert_upper(&bound.slack, u)
                .expect("assert_atom: assert_upper failed");
            outcome = outcome.combine(AssertOutcome::from_raw(raw));
        }

        let level = self.current_level();
        self.asserted.push((atom, level));
        // The LRA solver rejects a directly-contradictory bound without storing it, so latch
        // the conflict here (once) so `check` stays Unsat until this scope is popped.
        if outcome == AssertOutcome::Conflict && self.conflict.is_none() {
            self.conflict = Some((bound.slack, level));
        }
        outcome
    }

    /// Run a full feasibility check at the current bound set.
    ///
    /// Stage 1 delegates to the LRA (rational) [`LRASolver::solve`]; integer/LIRA reasoning
    /// under push/pop is Stage 5.
    pub fn check(&mut self) -> CheckResult {
        // A conflict latched at assert time is not visible to the tableau (the rejected bound
        // was never stored), so report it directly.
        if let Some((slack, _)) = self.conflict {
            let mut conflict = Conflict::new();
            conflict.insert(slack);
            return CheckResult::Unsat(conflict, LiaStats::new());
        }
        let ret = self.lra.solve().expect("check: LRASolver::solve failed");
        match ret.decision {
            SolverDecision::FEASIBLE(model) => CheckResult::Sat(model, ret.stats),
            SolverDecision::INFEASIBLE(conflict) => CheckResult::Unsat(conflict, ret.stats),
            SolverDecision::UNKNOWN => CheckResult::Unknown(ret.stats),
        }
    }

    /// Open a new scope. Returns a [`Level`] to pass to [`pop`](Self::pop) to discard every
    /// bound asserted after this point.
    ///
    /// The returned [`Level`] is the **restore target** — the level the solver had *before*
    /// this push. `set_backtrack` advances the solver's internal level (and returns the
    /// pre-bump value), so bounds asserted after this call are tagged with a strictly greater
    /// level and are discarded by the matching `pop`.
    ///
    /// Edge case (push-after-unsat): when the solver is already UNSAT, `set_backtrack` is a
    /// no-op and does not advance the level, so this scope coincides with the current one.
    /// That is sound — unsat is monotone under additional bounds, so no bound asserted in the
    /// coincident scope can restore feasibility, and popping it is harmless.
    pub fn push(&mut self) -> Level {
        Level(self.lra.set_backtrack())
    }

    /// Discard all bounds asserted since the matching [`push`](Self::push) that returned
    /// `level`. Bound *values* and the current assignment are restored by the owned solver;
    /// the local asserted-atom trail is truncated to match, and a latched assert-time conflict
    /// is cleared iff it was discovered in a scope being discarded.
    ///
    /// A `pop` to a level `>=` the current one (e.g. popping a coincident push-after-unsat
    /// scope, or popping without a matching push) is a no-op in the solver and leaves the
    /// trail untouched.
    pub fn pop(&mut self, level: Level) {
        self.lra.backtrack(level.0);
        self.asserted.retain(|(_, l)| *l <= level.0);
        // Clear a latched conflict if it was discovered in a scope we are discarding.
        if let Some((_, clvl)) = self.conflict
            && clvl > level.0
        {
            self.conflict = None;
        }
    }

    /// Borrow the underlying solver (test/introspection aid; not part of the incremental API).
    #[cfg(test)]
    pub(crate) fn lra(&self) -> &LRASolver {
        &self.lra
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arithmetic::lia::bounds::Bounds;
    use crate::arithmetic::lia::tableau::TableauKind;
    use crate::arithmetic::lia::types::rbig;
    use crate::arithmetic::lia::variables::{Owner, VarInfo};
    use crate::arithmetic::lia::context::ConvContext;

    /// Build a tiny solver over the single tableau row `s = x` where `x` is an unbounded
    /// non-basic integer and `s` an unbounded basic real. Registering atoms on `s` then lets
    /// us drive it purely through bound assertion, exactly as the incremental design intends.
    fn single_var_solver() -> IncrementalArithSolver {
        // non-basic x (col 0), basic s (row 0), equation s = 1*x
        let non_basic = vec![VarInfo::new(Var::int(0), Owner::NonBasic(0))];
        let basic = vec![VarInfo::new(Var::real(1), Owner::Basic(0)).with_bounds(Bounds::unbounded())];
        let equations = vec![vec![rbig!(1)]];
        let lra = LRASolver::from_eqs(
            basic,
            non_basic,
            equations,
            ConvContext::default(),
            TableauKind::Dense,
        )
        .expect("failed to build LRASolver");
        IncrementalArithSolver::new(lra, SolverConfig::default())
    }

    #[test]
    fn register_returns_distinct_ids() {
        let mut s = single_var_solver();
        let a = s.register_atom(Var::real(1), Constraint::Le, rbig!(5));
        let b = s.register_atom(Var::real(1), Constraint::Ge, rbig!(0));
        assert_ne!(a, b);
        assert_eq!(s.num_atoms(), 2);
    }

    #[test]
    fn assert_consistent_bounds_is_feasible() {
        let mut s = single_var_solver();
        // 0 <= s <= 5
        let lo = s.register_atom(Var::real(1), Constraint::Ge, rbig!(0));
        let hi = s.register_atom(Var::real(1), Constraint::Le, rbig!(5));
        assert_eq!(s.assert_atom(lo), AssertOutcome::Sat);
        // upper bound of 5 is consistent with the (satisfied) lower bound
        assert!(matches!(
            s.assert_atom(hi),
            AssertOutcome::Sat | AssertOutcome::Unknown
        ));
        assert!(matches!(s.check(), CheckResult::Sat(..)));
    }

    #[test]
    fn contradictory_bounds_conflict_on_assert() {
        let mut s = single_var_solver();
        // s >= 5 then s <= 3 is an immediate bound-vs-bound conflict
        let lo = s.register_atom(Var::real(1), Constraint::Ge, rbig!(5));
        let hi = s.register_atom(Var::real(1), Constraint::Le, rbig!(3));
        // s is basic, so tightening its lower bound needs a pivot -> Unknown (not eagerly Sat)
        assert!(matches!(
            s.assert_atom(lo),
            AssertOutcome::Sat | AssertOutcome::Unknown
        ));
        // upper bound 3 < lower bound 5: immediate bound-vs-bound conflict
        assert_eq!(s.assert_atom(hi), AssertOutcome::Conflict);
        assert!(matches!(s.check(), CheckResult::Unsat(..)));
    }

    #[test]
    fn push_pop_restores_feasibility() {
        let mut s = single_var_solver();
        let base = s.register_atom(Var::real(1), Constraint::Ge, rbig!(0));
        assert_eq!(s.assert_atom(base), AssertOutcome::Sat);
        assert!(matches!(s.check(), CheckResult::Sat(..)));

        // enter a scope, assert a contradictory upper bound
        let level = s.push();
        let bad = s.register_atom(Var::real(1), Constraint::Le, rbig!(-1));
        assert_eq!(s.assert_atom(bad), AssertOutcome::Conflict);
        assert!(matches!(s.check(), CheckResult::Unsat(..)));

        // pop the scope: the s <= -1 bound is discarded, feasibility returns
        s.pop(level);
        assert!(
            s.asserted.iter().all(|(_, l)| *l <= level.0),
            "asserted trail should be truncated after pop"
        );
        assert!(matches!(s.check(), CheckResult::Sat(..)));
    }

    #[test]
    fn equality_atom_asserts_both_bounds() {
        let mut s = single_var_solver();
        // s = 4 pins s to a point; still feasible since x is unbounded
        let eq = s.register_atom(Var::real(1), Constraint::Eq, rbig!(4));
        assert!(matches!(
            s.assert_atom(eq),
            AssertOutcome::Sat | AssertOutcome::Unknown
        ));
        match s.check() {
            CheckResult::Sat(model, _) => {
                assert_eq!(model.get(&Var::real(1)), Some(&rbig!(4)));
            }
            other => panic!("expected Sat, got {other:?}"),
        }
        // sanity: the bound really is registered on the slack in the owned solver
        let bounds = s.lra().get_bounds(&Var::real(1)).unwrap();
        assert_eq!(bounds.lower, Some(QDelta::from(rbig!(4))));
        assert_eq!(bounds.upper, Some(QDelta::from(rbig!(4))));
    }

    // ─── Stage 3: push/pop robustness ───────────────────────────────────────────

    #[test]
    fn nested_push_pop_restores_each_level() {
        let mut s = single_var_solver();
        // base scope: s >= 0, feasible
        let base = s.register_atom(Var::real(1), Constraint::Ge, rbig!(0));
        assert!(matches!(
            s.assert_atom(base),
            AssertOutcome::Sat | AssertOutcome::Unknown
        ));
        assert!(matches!(s.check(), CheckResult::Sat(..)));

        // level 1: s <= 10, still feasible
        let l1 = s.push();
        let a1 = s.register_atom(Var::real(1), Constraint::Le, rbig!(10));
        s.assert_atom(a1);
        assert!(matches!(s.check(), CheckResult::Sat(..)));

        // level 2: s <= -1, now infeasible (contradicts s >= 0)
        let l2 = s.push();
        let a2 = s.register_atom(Var::real(1), Constraint::Le, rbig!(-1));
        assert_eq!(s.assert_atom(a2), AssertOutcome::Conflict);
        assert!(matches!(s.check(), CheckResult::Unsat(..)));

        // pop level 2: back to {s >= 0, s <= 10}, feasible again
        s.pop(l2);
        assert!(matches!(s.check(), CheckResult::Sat(..)));

        // pop level 1: back to just {s >= 0}, still feasible
        s.pop(l1);
        assert!(matches!(s.check(), CheckResult::Sat(..)));
        // only the base atom remains on the trail
        assert_eq!(s.asserted.len(), 1);
    }

    #[test]
    fn push_after_unsat_then_pop_recovers() {
        let mut s = single_var_solver();
        // make the base state unsat: s >= 5 and s <= 3
        let lo = s.register_atom(Var::real(1), Constraint::Ge, rbig!(5));
        let hi = s.register_atom(Var::real(1), Constraint::Le, rbig!(3));
        s.assert_atom(lo);
        assert_eq!(s.assert_atom(hi), AssertOutcome::Conflict);
        assert!(matches!(s.check(), CheckResult::Unsat(..)));

        // push while unsat: set_backtrack is a no-op, so this scope coincides with the current
        // one. Popping it must not panic and must leave the (still-unsat) state intact.
        let level = s.push();
        s.pop(level);
        assert!(matches!(s.check(), CheckResult::Unsat(..)));
    }

    #[test]
    fn pop_without_push_is_noop() {
        let mut s = single_var_solver();
        let base = s.register_atom(Var::real(1), Constraint::Ge, rbig!(0));
        s.assert_atom(base);
        assert!(matches!(s.check(), CheckResult::Sat(..)));
        // Level(0) targets the base scope; backtrack early-returns (level >= current), so this
        // is a no-op and must not panic on the absent old_assignment.
        s.pop(Level(0));
        assert!(matches!(s.check(), CheckResult::Sat(..)));
        assert_eq!(s.asserted.len(), 1);
    }

    #[test]
    fn strict_inequality_atom_through_api() {
        let mut s = single_var_solver();
        // s > 3 and s < 4 over the reals: feasible (e.g. s = 3.5); the qdelta strict bounds
        // must not collapse to an empty interval.
        let gt = s.register_atom(Var::real(1), Constraint::Gt, rbig!(3));
        let lt = s.register_atom(Var::real(1), Constraint::Lt, rbig!(4));
        s.assert_atom(gt);
        s.assert_atom(lt);
        assert!(matches!(s.check(), CheckResult::Sat(..)));

        // Tightening to s < 3 (with s > 3 still asserted in a nested scope) is infeasible.
        let level = s.push();
        let lt3 = s.register_atom(Var::real(1), Constraint::Lt, rbig!(3));
        s.assert_atom(lt3);
        assert!(matches!(s.check(), CheckResult::Unsat(..)));
        s.pop(level);
        assert!(matches!(s.check(), CheckResult::Sat(..)));
    }
}
