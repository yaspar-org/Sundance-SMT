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
use crate::arithmetic::lia::lira_solver::LIRASolver;
use crate::arithmetic::lia::lra_solver::LRASolver;
use crate::arithmetic::lia::qdelta::QDelta;
use crate::arithmetic::lia::solver_result::{Assignment, Conflict, SolverDecision};
use crate::arithmetic::lia::stats::Stats as LiaStats;
use crate::arithmetic::lia::variables::Var;
use crate::debug_println;
use crate::utils::{DeterministicHashMap, DeterministicHashSet};
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
/// Stage 4: results carry SAT-literal-level cores and Nelson-Oppen-ready model shapes that the
/// propagator can consume directly.
#[derive(Debug)]
pub enum CheckResult {
    /// Feasible.
    /// - `core_literals`: empty (no conflict).
    /// - `model`: value→term-set map ready for the Nelson-Oppen splitting loop
    ///   (term_ids grouped by their integer arithmetic value).
    /// - `stats`: runtime statistics.
    Sat {
        model: DeterministicHashMap<i64, DeterministicHashSet<u64>>,
        stats: LiaStats,
    },
    /// Infeasible.
    /// - `core_literals`: the SAT-level conflict clause — union of negated atom literals and
    ///   justification literals for each conflicting slack. This is the durable replacement of
    ///   the one-shot path's `ArithResult::Unsat(Vec<i32>)`.
    /// - `stats`: runtime statistics.
    Unsat {
        core_literals: Vec<i32>,
        stats: LiaStats,
    },
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

/// A single entry on the assertion trail, recording everything needed to reconstruct unsat
/// cores in terms of SAT literals (Stage 4).
#[derive(Debug, Clone)]
struct AssertedAtom {
    /// The registered atom that was asserted.
    atom: AtomId,
    /// The scope level at the time of assertion.
    level: usize,
    /// The SAT literal that triggered this assertion (via [`IncrementalArithSolver::assert_literal`]).
    /// `0` when asserted directly via [`IncrementalArithSolver::assert_atom`] without a literal.
    lit: i32,
    /// Extra justification literals (e.g. egraph-merge explanations / `additional_constraints`)
    /// to include in the unsat core alongside the atom's own literal.
    justification: Vec<i32>,
}

/// A long-lived incremental arithmetic solver over a fixed slack-variable set.
///
/// Owns an [`LRASolver`] and an atom registry. Runtime incrementality is *purely bound
/// assertion/retraction* on pre-existing slacks — no rows or variables are added after
/// construction (that static-tableau construction is Stage 2).
#[derive(Debug)]
pub struct IncrementalArithSolver {
    /// The persistent mixed integer/real arithmetic solver. Owns the [`LRASolver`] that all
    /// slacks referenced by registered atoms live in. [`check`](Self::check) drives B&B via
    /// this solver; bounds are asserted/backtracked on `lira.lra_solver_mut()`.
    lira: LIRASolver,
    /// Solver configuration (retained for later LIRA re-configuration; currently just the
    /// same config the wrapped LIRA was built with).
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
    /// Root registry: `(term_id, root_var)` pairs populated by the static builder. Used in the
    /// Sat model translation: for each root, look up its value in the assignment and group
    /// term_ids by integer value, producing the `DeterministicHashMap<i64, DeterministicHashSet<u64>>`
    /// that the Nelson-Oppen splitting loop expects.
    roots: Vec<(u64, Var)>,
    /// Trail of asserted atoms with per-assertion metadata for core reconstruction (Stage 4).
    ///
    /// Each entry records:
    /// - the atom that was asserted,
    /// - the scope level it was asserted at (for truncation on pop),
    /// - the SAT literal that triggered the assertion (if via `assert_literal`; 0 otherwise),
    /// - extra justification literals (egraph-merge explanations from `additional_constraints`
    ///   at the time of assertion — a caller obligation, empty in the pre-search builder).
    asserted: Vec<AssertedAtom>,
    /// Sticky record of a conflict detected *at assert time*.
    ///
    /// [`LRASolver::assert_lower`]/[`LRASolver::assert_upper`] report an immediate
    /// bound-vs-bound conflict by returning `Some(false)` but **do not store** the rejected
    /// bound (see `lra_solver.rs`). So a later [`check`](Self::check) would not rediscover it.
    /// We latch the conflicting slack (with the scope level it was found at) here so that
    /// [`check`](Self::check) faithfully reports `Unsat` until the offending scope is popped.
    conflict: Option<(Var, usize)>,
    /// Registry: sorted variable pair → the equality slack and its two atoms (Le, Ge)
    /// (Stage 6). Introduced lazily by [`register_var_equality`](Self::register_var_equality) —
    /// when the propagator learns that two arithmetic terms are egraph-equal, calling
    /// `assert_equality(v_a, v_b, justification)` looks up (or creates) the slack `s = v_a - v_b`
    /// and asserts both bounds `s ≤ 0 ∧ s ≥ 0`. Keyed on the sorted pair so `(v_a, v_b)` and
    /// `(v_b, v_a)` share the same entry.
    equality_atoms: DeterministicHashMap<(Var, Var), (Var, AtomId, AtomId)>,
    /// Persistent egraph-id → `Var` map, populated by the static builder and consulted by
    /// [`Self::register_atom_dynamic`](Self::register_atom_dynamic) to translate an atom's
    /// term-level monomials back into the LP `Var`s that already live in the LRA.
    ///
    /// This is required for Stage 7 to handle atoms introduced at runtime — e.g. the
    /// Nelson-Oppen splitting clauses `(< a b) ∨ (> a b) ∨ (= a b)` whose disjuncts
    /// don't exist in `cnf_cache.var_map` when the static builder walks it. When such a
    /// literal is later asserted from a SAT model, we extract its `LinearConstraint`
    /// against this map and register a fresh atom slack on the fly.
    term_var_map: DeterministicHashMap<u32, Var>,
}

impl IncrementalArithSolver {
    /// Wrap an already-constructed [`LRASolver`] (e.g. from `LinearSystem::to_lra_solver` or
    /// `LRASolver::from_eqs`). The LRA is wrapped in an [`LIRASolver`] internally so
    /// [`check`](Self::check) can drive branch-and-bound over integer variables.
    pub fn new(lra: LRASolver, config: SolverConfig) -> Self {
        let lira = LIRASolver::new(lra, config.clone());
        IncrementalArithSolver {
            lira,
            config,
            atoms: DeterministicHashMap::new(),
            literal_atoms: DeterministicHashMap::new(),
            next_atom: 0,
            roots: Vec::new(),
            asserted: Vec::new(),
            conflict: None,
            equality_atoms: DeterministicHashMap::new(),
            term_var_map: DeterministicHashMap::new(),
        }
    }

    /// Populate the persistent `term_var_map` from the builder. Called once per
    /// (egraph_id, Var) pair after `to_lra_solver` finishes. See the field-level docstring
    /// on [`term_var_map`](Self::term_var_map) for the Stage 7 rationale.
    pub fn register_term_var(&mut self, egraph_id: u32, var: Var) {
        self.term_var_map.insert(egraph_id, var);
    }

    /// Look up the `Var` associated with an egraph_id, if any.
    pub fn var_for_egraph_id(&self, egraph_id: u32) -> Option<Var> {
        self.term_var_map.get(&egraph_id).copied()
    }

    /// Register a new atom encountered at check time (e.g. from a Nelson-Oppen
    /// splitting clause the static builder didn't see). Allocates a fresh slack row
    /// `slack = Σ monomials` via [`LRASolver::add_slack_row`], registers both polarities
    /// of `lit` against that slack (using the atom's `Constraint::negate` for the
    /// negative-polarity direction; `Eq`'s negation is left to Nelson-Oppen and only
    /// the positive polarity is registered in that case), and returns the positive
    /// polarity's [`AtomId`].
    ///
    /// Panics if `monomials` references a `Var` unknown to the LRA — that would mean
    /// the caller referenced a term outside the LP, which is a bug.
    pub fn register_atom_dynamic(
        &mut self,
        lit: i32,
        monomials: Vec<crate::arithmetic::lia::linear_system::Mon<Rational>>,
        constant: Rational,
        constraint: Constraint,
    ) -> AtomId {
        let coeffs: Vec<(Var, Rational)> = monomials
            .iter()
            .map(|m| (m.var(), m.coeff_ref().clone()))
            .collect();
        let slack = self
            .lira
            .lra_solver_mut()
            .add_slack_row(&format!("!ext_slack_dyn_atom_{lit}"), &coeffs)
            .expect("register_atom_dynamic: add_slack_row failed");
        let pos = self.register_literal_atom(lit, slack, constraint, constant.clone());
        if let Some(neg_constraint) = constraint.negate() {
            self.register_literal_atom(-lit, slack, neg_constraint, constant);
        }
        pos
    }

    /// Add a root mapping. Called by the static builder to register each arithmetic term's
    /// `(term_id, root_var)` pair for NO model translation.
    pub fn register_root(&mut self, term_id: u64, root_var: Var) {
        self.roots.push((term_id, root_var));
    }

    /// The current scope level, read live from the owned solver so it is always authoritative
    /// (the solver's [`LRASolver::backtrack_level`] is a monotonically increasing timestamp,
    /// unaffected by `backtrack`, and is *not* bumped by `set_backtrack` when already UNSAT).
    fn current_level(&self) -> usize {
        self.lira.lra_solver().backtrack_level()
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

    /// Assert the atom associated with a SAT literal, with optional extra justification
    /// literals to include in unsat cores (e.g. egraph-merge explanations).
    ///
    /// Returns `None` when `lit` is not a registered arithmetic atom (so callers can pass a
    /// whole SAT model and let non-arithmetic literals fall through). Otherwise behaves like
    /// [`assert_atom`](Self::assert_atom).
    pub fn assert_literal_justified(
        &mut self,
        lit: i32,
        justification: Vec<i32>,
    ) -> Option<AssertOutcome> {
        let atom = *self.literal_atoms.get(&lit)?;
        Some(self.assert_atom_impl(atom, lit, justification))
    }

    /// Assert the atom associated with a SAT literal (no extra justification).
    ///
    /// Convenience wrapper over [`assert_literal_justified`](Self::assert_literal_justified).
    pub fn assert_literal(&mut self, lit: i32) -> Option<AssertOutcome> {
        self.assert_literal_justified(lit, Vec::new())
    }

    /// Look up the [`AtomId`] registered for a SAT literal, if any.
    pub fn atom_for_literal(&self, lit: i32) -> Option<AtomId> {
        self.literal_atoms.get(&lit).copied()
    }

    /// Number of registered atoms.
    pub fn num_atoms(&self) -> usize {
        self.atoms.len()
    }

    /// Assert a previously-registered atom without a SAT literal or justification.
    ///
    /// Equivalent to [`assert_atom_impl`](Self::assert_atom_impl) with `lit=0` and empty
    /// justification. Use [`assert_literal`](Self::assert_literal) or
    /// [`assert_literal_justified`](Self::assert_literal_justified) when a literal is available.
    pub fn assert_atom(&mut self, atom: AtomId) -> AssertOutcome {
        self.assert_atom_impl(atom, 0, Vec::new())
    }

    /// Sort a `(Var, Var)` pair so `(a, b)` and `(b, a)` hash to the same key.
    fn equality_key(v_a: Var, v_b: Var) -> (Var, Var) {
        if v_a <= v_b { (v_a, v_b) } else { (v_b, v_a) }
    }

    /// Register (or look up) the equality slack `s = v_a - v_b` and its two atoms
    /// `s ≤ 0` and `s ≥ 0` (Stage 6). Returns `(Le AtomId, Ge AtomId)`.
    ///
    /// First call for a given `{v_a, v_b}` allocates a fresh basic slack via
    /// [`LRASolver::add_slack_row`] and registers both atoms. Subsequent calls with either
    /// order of the same pair return the same atoms (idempotent). This is the primitive
    /// [`assert_equality`](Self::assert_equality) uses to convey an egraph-implied merge
    /// `t_a ≡ t_b` to the LP as an ordinary bound assertion.
    ///
    /// `v_a` and `v_b` must be `Var`s already in the LRA (typically root vars returned by
    /// [`var_for_term`](Self::var_for_term) or slack vars from the atom registry).
    pub fn register_var_equality(&mut self, v_a: Var, v_b: Var) -> (AtomId, AtomId) {
        let key = Self::equality_key(v_a, v_b);
        if let Some(&(_slack, le, ge)) = self.equality_atoms.get(&key) {
            return (le, ge);
        }
        let (v_lo, v_hi) = key;
        let name = format!("!ext_slack_eq_{v_lo:?}_{v_hi:?}");
        let slack = self
            .lira
            .lra_solver_mut()
            .add_slack_row(
                &name,
                &[
                    (v_lo, Rational::ONE),
                    (v_hi, -Rational::ONE),
                ],
            )
            .expect("register_var_equality: add_slack_row failed");
        // s ≤ 0 and s ≥ 0 together pin s = 0, i.e. v_lo = v_hi.
        let le = self.register_atom(slack, Constraint::Le, Rational::ZERO);
        let ge = self.register_atom(slack, Constraint::Ge, Rational::ZERO);
        self.equality_atoms.insert(key, (slack, le, ge));
        (le, ge)
    }

    /// Assert the LP equality `v_a = v_b` with an accompanying justification (typically
    /// the egraph-merge explanation from `explain_equality`).
    ///
    /// Registers the equality slack on first use, then asserts both bounds. The
    /// justification is threaded through both atom assertions so it appears in the unsat
    /// core if the equality contributes to a conflict. Returns the combined outcome
    /// (worst of the two bound-assertion outcomes).
    pub fn assert_equality(
        &mut self,
        v_a: Var,
        v_b: Var,
        justification: Vec<i32>,
    ) -> AssertOutcome {
        let (le, ge) = self.register_var_equality(v_a, v_b);
        let out_le = self.assert_atom_impl(le, 0, justification.clone());
        let out_ge = self.assert_atom_impl(ge, 0, justification);
        out_le.combine(out_ge)
    }

    /// Core assertion implementation. Tightens the atom's slack bound(s), records the assertion
    /// on the trail with the triggering literal and justification, and latches any immediate
    /// bound-vs-bound conflict.
    fn assert_atom_impl(
        &mut self,
        atom: AtomId,
        lit: i32,
        justification: Vec<i32>,
    ) -> AssertOutcome {
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
                .lira
                .lra_solver_mut()
                .assert_lower(&bound.slack, l)
                .expect("assert_atom: assert_lower failed");
            outcome = outcome.combine(AssertOutcome::from_raw(raw));
        }
        if let Some(u) = &bound.upper {
            let raw = self
                .lira
                .lra_solver_mut()
                .assert_upper(&bound.slack, u)
                .expect("assert_atom: assert_upper failed");
            outcome = outcome.combine(AssertOutcome::from_raw(raw));
        }

        let level = self.current_level();
        self.asserted.push(AssertedAtom {
            atom,
            level,
            lit,
            justification,
        });
        // The LRA solver rejects a directly-contradictory bound without storing it, so latch
        // the conflict here (once) so `check` stays Unsat until this scope is popped.
        if outcome == AssertOutcome::Conflict && self.conflict.is_none() {
            self.conflict = Some((bound.slack, level));
        }
        outcome
    }

    /// Collect the unsat core literals for a set of conflicting slack variables.
    ///
    /// Walks the asserted trail, finds atoms whose slack appears in `conflict_slacks`, and
    /// collects their negated atom literals + justification literals into a single clause.
    fn collect_core(&self, conflict_slacks: &Conflict<Var>) -> Vec<i32> {
        let mut core: Vec<i32> = Vec::new();
        for entry in &self.asserted {
            let slack = self.atoms[&entry.atom].slack;
            if conflict_slacks.contains(&slack) {
                // Include the negated atom literal (matching the one-shot convention: the
                // conflict clause is the *negation* of the asserted set, so the atom literal
                // appears negated).
                if entry.lit != 0 {
                    core.push(-entry.lit);
                }
                core.extend_from_slice(&entry.justification);
            }
        }
        core
    }

    /// Build the value→term-set model map from a feasible assignment (the shape NO expects).
    fn build_no_model(
        &self,
        assignment: &Assignment<Var>,
    ) -> DeterministicHashMap<i64, DeterministicHashSet<u64>> {
        let mut model: DeterministicHashMap<i64, DeterministicHashSet<u64>> =
            DeterministicHashMap::new();
        for &(term_id, root_var) in &self.roots {
            if let Some(value) = assignment.get(&root_var) {
                let val_i64: i64 = value.to_int().value().try_into().unwrap_or(i64::MAX);
                debug_println!(
                    21,
                    6,
                    "incremental::build_no_model: term_id={} root_var={:?} value={} -> {}",
                    term_id,
                    root_var,
                    value,
                    val_i64
                );
                model.entry(val_i64).or_default().insert(term_id);
            } else {
                debug_println!(
                    21,
                    6,
                    "incremental::build_no_model: term_id={} root_var={:?} NOT IN ASSIGNMENT",
                    term_id,
                    root_var
                );
            }
        }
        model
    }

    /// Run a full feasibility check at the current bound set.
    ///
    /// Routes through [`LIRASolver`] so `Int`-typed variables get branch-and-bound-driven
    /// integer assignments (Stage 5). To guarantee no B&B bounds leak past the boundary:
    ///
    /// 1. The pre-solve LRA `backtrack_level` is snapshotted.
    /// 2. The LIRA explorer + LIRA-local stats are reset so B&B starts from a fresh tree
    ///    (a persistent LIRA cannot be re-solved otherwise — after one solve its root is
    ///    in a terminal state and `solve` would hit `unreachable!`).
    /// 3. After solve returns — regardless of outcome — we unconditionally
    ///    `lra_solver_mut().backtrack(pre_solve_level)`. `branch_and_bound` returns early
    ///    on the *first* integer-feasible node, so on `Sat` its speculative branch
    ///    bounds are still asserted; unconditional backtrack pops them. On unsat/unknown
    ///    LIRA's own resolution usually returns to level 0 but this removes any
    ///    dependence on that invariant.
    ///
    /// Caveat: [`LRASolver::backtrack_level`] is a monotonically increasing timestamp
    /// (`backtrack` does not decrement it, see [Stage 3 findings]). So the counter after
    /// this call is `>= pre_solve_level`; what's *restored* is the bound trail — every
    /// bound tagged `level > pre_solve_level` is popped. That's the semantic containment
    /// callers care about: `push`/`pop`/`assert_atom` all key on the counter's current
    /// value at the time they run, so counter drift is harmless.
    ///
    /// On `Unsat`, the `Conflict<Var>` is translated to SAT-level core literals via the
    /// assertion trail; on `Sat`, the value→term-set map is built for Nelson-Oppen.
    pub fn check(&mut self) -> CheckResult {
        // A conflict latched at assert time is not visible to the tableau (the rejected bound
        // was never stored), so report it directly. The core is all trail entries touching that
        // slack.
        if let Some((slack, _)) = self.conflict {
            let mut conflict_set = Conflict::new();
            conflict_set.insert(slack);
            let core_literals = self.collect_core(&conflict_set);
            return CheckResult::Unsat {
                core_literals,
                stats: LiaStats::new(),
            };
        }

        let pre_solve_level = self.lira.lra_solver().backtrack_level();
        // Snapshot the tableau structure (basis/owner layout, coefficients) so we can
        // restore it after solve(). `backtrack` only pops bounds/assignment — it never
        // undoes pivots (Stage 3 finding: basis-left-pivoted is sound). But leaving the
        // pivoted basis around corrupts a subsequent check() that iterates basic vars by
        // index: the wrong variables appear basic, with wrong bounds relative to the
        // pre-pivot layout. try_unit_cube_test already does this save/restore pattern.
        let saved_tableau = self.lira.lra_solver().snapshot_tableau();
        self.lira.reset_state();
        let ret = self.lira.solve().expect("check: LIRASolver::solve failed");
        // Contain any speculative B&B bounds inside this check() call.
        self.lira.lra_solver_mut().backtrack(pre_solve_level);
        self.lira.lra_solver_mut().restore_tableau_from_snapshot(saved_tableau);
        self.lira.lra_solver_mut().reset_to_unknown();

        match ret.decision {
            SolverDecision::FEASIBLE(assignment) => {
                let model = self.build_no_model(&assignment);
                CheckResult::Sat {
                    model,
                    stats: ret.stats,
                }
            }
            SolverDecision::INFEASIBLE(conflict) => {
                let core_literals = self.collect_core(&conflict);
                CheckResult::Unsat {
                    core_literals,
                    stats: ret.stats,
                }
            }
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
        Level(self.lira.lra_solver_mut().set_backtrack())
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
        self.lira.lra_solver_mut().backtrack(level.0);
        self.asserted.retain(|entry| entry.level <= level.0);
        // Clear a latched conflict if it was discovered in a scope we are discarding.
        if let Some((_, clvl)) = self.conflict
            && clvl > level.0
        {
            self.conflict = None;
        }
    }

    /// Borrow the underlying LRA solver (test/introspection aid; not part of the incremental API).
    #[cfg(test)]
    pub(crate) fn lra(&self) -> &LRASolver {
        self.lira.lra_solver()
    }

    /// Look up the arithmetic `Var` (root variable) associated with an SMT term_id, if any.
    ///
    /// Populated by the static builder for every term in `arithmetic_terms`. Used by
    /// Stage 6 tests and by the propagator (Stage 7) to translate an egraph-implied
    /// term equality `t_a ≡ t_b` into an LP equality bound on `(var_of(t_a), var_of(t_b))`.
    ///
    /// This lookup is **stable across egraph merges** — `var_map` in the builder is keyed
    /// on `to_egraph_id(term_id)` which is a fixed bimap, not on the *current* egraph
    /// class root. That's exactly the Stage 6 invariant: `Var`s never re-key, so merges
    /// are handled as bounds rather than by rewriting the LP.
    pub fn var_for_term(&self, term_id: u64) -> Option<Var> {
        self.roots
            .iter()
            .find_map(|(t, v)| if *t == term_id { Some(*v) } else { None })
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

    /// Real-typed variant of [`single_var_solver`]: `s = x` with `x` a non-basic *Real*.
    /// Used by tests that assert strict inequalities meant to be interpreted over the
    /// reals — under [`single_var_solver`] the same bounds are LIA-unsat via B&B once
    /// `check()` routes through [`LIRASolver`].
    fn single_real_var_solver() -> IncrementalArithSolver {
        let non_basic = vec![VarInfo::new(Var::real(0), Owner::NonBasic(0))];
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
        assert!(matches!(s.check(), CheckResult::Sat { .. }));
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
        assert!(matches!(s.check(), CheckResult::Unsat { .. }));
    }

    #[test]
    fn push_pop_restores_feasibility() {
        let mut s = single_var_solver();
        let base = s.register_atom(Var::real(1), Constraint::Ge, rbig!(0));
        assert_eq!(s.assert_atom(base), AssertOutcome::Sat);
        assert!(matches!(s.check(), CheckResult::Sat { .. }));

        // enter a scope, assert a contradictory upper bound
        let level = s.push();
        let bad = s.register_atom(Var::real(1), Constraint::Le, rbig!(-1));
        assert_eq!(s.assert_atom(bad), AssertOutcome::Conflict);
        assert!(matches!(s.check(), CheckResult::Unsat { .. }));

        // pop the scope: the s <= -1 bound is discarded, feasibility returns
        s.pop(level);
        assert!(
            s.asserted.iter().all(|e| e.level <= level.0),
            "asserted trail should be truncated after pop"
        );
        assert!(matches!(s.check(), CheckResult::Sat { .. }));
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
        // No roots registered, so model map is empty; just verify feasibility.
        assert!(matches!(s.check(), CheckResult::Sat { .. }));
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
        assert!(matches!(s.check(), CheckResult::Sat { .. }));

        // level 1: s <= 10, still feasible
        let l1 = s.push();
        let a1 = s.register_atom(Var::real(1), Constraint::Le, rbig!(10));
        s.assert_atom(a1);
        assert!(matches!(s.check(), CheckResult::Sat { .. }));

        // level 2: s <= -1, now infeasible (contradicts s >= 0)
        let l2 = s.push();
        let a2 = s.register_atom(Var::real(1), Constraint::Le, rbig!(-1));
        assert_eq!(s.assert_atom(a2), AssertOutcome::Conflict);
        assert!(matches!(s.check(), CheckResult::Unsat { .. }));

        // pop level 2: back to {s >= 0, s <= 10}, feasible again
        s.pop(l2);
        assert!(matches!(s.check(), CheckResult::Sat { .. }));

        // pop level 1: back to just {s >= 0}, still feasible
        s.pop(l1);
        assert!(matches!(s.check(), CheckResult::Sat { .. }));
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
        assert!(matches!(s.check(), CheckResult::Unsat { .. }));

        // push while unsat: set_backtrack is a no-op, so this scope coincides with the current
        // one. Popping it must not panic and must leave the (still-unsat) state intact.
        let level = s.push();
        s.pop(level);
        assert!(matches!(s.check(), CheckResult::Unsat { .. }));
    }

    #[test]
    fn pop_without_push_is_noop() {
        let mut s = single_var_solver();
        let base = s.register_atom(Var::real(1), Constraint::Ge, rbig!(0));
        s.assert_atom(base);
        assert!(matches!(s.check(), CheckResult::Sat { .. }));
        // Level(0) targets the base scope; backtrack early-returns (level >= current), so this
        // is a no-op and must not panic on the absent old_assignment.
        s.pop(Level(0));
        assert!(matches!(s.check(), CheckResult::Sat { .. }));
        assert_eq!(s.asserted.len(), 1);
    }

    #[test]
    fn strict_inequality_atom_through_api() {
        // Real-typed variant: s > 3 and s < 4 has real witness 3.5 but no integer witness,
        // so with an Int-typed `x` LIRA would (correctly) return UNSAT via B&B. This test's
        // intent is the qdelta strict-bound plumbing, so use the Real setup.
        let mut s = single_real_var_solver();
        // s > 3 and s < 4 over the reals: feasible (e.g. s = 3.5); the qdelta strict bounds
        // must not collapse to an empty interval.
        let gt = s.register_atom(Var::real(1), Constraint::Gt, rbig!(3));
        let lt = s.register_atom(Var::real(1), Constraint::Lt, rbig!(4));
        s.assert_atom(gt);
        s.assert_atom(lt);
        assert!(matches!(s.check(), CheckResult::Sat { .. }));

        // Tightening to s < 3 (with s > 3 still asserted in a nested scope) is infeasible.
        let level = s.push();
        let lt3 = s.register_atom(Var::real(1), Constraint::Lt, rbig!(3));
        s.assert_atom(lt3);
        assert!(matches!(s.check(), CheckResult::Unsat { .. }));
        s.pop(level);
        assert!(matches!(s.check(), CheckResult::Sat { .. }));
    }

    // ─── Stage 4: core + NO model tests ─────────────────────────────────────────

    #[test]
    fn unsat_core_contains_negated_atom_literals() {
        let mut s = single_var_solver();
        // Use register_literal_atom so we can track the atom by literal.
        let lit_lo = 100; // fake SAT literal for s >= 5
        let lit_hi = 200; // fake SAT literal for s <= 3
        s.register_literal_atom(lit_lo, Var::real(1), Constraint::Ge, rbig!(5));
        s.register_literal_atom(lit_hi, Var::real(1), Constraint::Le, rbig!(3));
        s.assert_literal(lit_lo);
        s.assert_literal(lit_hi);
        match s.check() {
            CheckResult::Unsat { core_literals, .. } => {
                // Core should contain negated literals: -(100) = -100 and -(200) = -200
                assert!(
                    core_literals.contains(&-lit_lo) || core_literals.contains(&-lit_hi),
                    "core should contain at least one negated atom literal, got {core_literals:?}"
                );
            }
            other => panic!("expected Unsat, got {other:?}"),
        }
    }

    #[test]
    fn unsat_core_includes_justification_literals() {
        let mut s = single_var_solver();
        let lit_lo = 10;
        let lit_hi = 20;
        let justification = vec![42, -43]; // mock egraph-merge justifications
        s.register_literal_atom(lit_lo, Var::real(1), Constraint::Ge, rbig!(5));
        s.register_literal_atom(lit_hi, Var::real(1), Constraint::Le, rbig!(3));
        s.assert_literal(lit_lo);
        s.assert_literal_justified(lit_hi, justification.clone());
        match s.check() {
            CheckResult::Unsat { core_literals, .. } => {
                // Justification literals should appear in the core
                for j in &justification {
                    assert!(
                        core_literals.contains(j),
                        "core should include justification literal {j}, got {core_literals:?}"
                    );
                }
            }
            other => panic!("expected Unsat, got {other:?}"),
        }
    }

    #[test]
    fn sat_model_groups_roots_by_value() {
        let mut s = single_var_solver();
        // Register roots: term_id 100 → root Var::int(0) (which is the non-basic variable x)
        s.register_root(100, Var::int(0));
        // Assert that x = 7 via the slack: s = x, so bound x >= 7 and x <= 7 (equality on x).
        // x is non-basic (col 0) so we can assert bounds on it directly.
        let eq_atom = s.register_atom(Var::int(0), Constraint::Eq, rbig!(7));
        s.assert_atom(eq_atom);
        match s.check() {
            CheckResult::Sat { model, .. } => {
                // The model should map 7 → {100}
                let terms = model.get(&7);
                assert!(
                    terms.is_some() && terms.unwrap().contains(&100),
                    "model should contain 7 → {{100}}, got {model:?}"
                );
            }
            other => panic!("expected Sat, got {other:?}"),
        }
    }

    // ─── Stage 5: LIRA integer reasoning + level containment ────────────────────

    #[test]
    fn integer_sat_needs_branch_and_bound() {
        // Over the rationals, `x >= 1/2 ∧ x <= 3` is trivially satisfied by x = 1/2, but the
        // LRA-only `check()` from Stages 1-4 would return that fractional value even though
        // `x` is typed `Int`. Routing through LIRA must branch-and-bound to an integer
        // assignment (any integer in [1, 3]).
        let mut s = single_var_solver();
        s.register_root(100, Var::int(0));
        let lo = s.register_atom(Var::int(0), Constraint::Ge, rbig!(1 / 2));
        let hi = s.register_atom(Var::int(0), Constraint::Le, rbig!(3));
        s.assert_atom(lo);
        s.assert_atom(hi);
        match s.check() {
            CheckResult::Sat { model, .. } => {
                assert!(
                    !model.is_empty(),
                    "expected an integer model, got empty {model:?}"
                );
                for value in model.keys() {
                    assert!(
                        (1..=3).contains(value),
                        "B&B assigned x = {value}, expected an integer in [1, 3]"
                    );
                }
            }
            other => panic!("expected Sat (integer via B&B), got {other:?}"),
        }
    }

    #[test]
    fn integer_unsat_via_branch_and_bound() {
        // `x >= 1/3 ∧ x <= 2/3` is LRA-sat (x = 1/2) but LIA-unsat (no integer in [1/3, 2/3]).
        // B&B must prune both branches (x <= 0 and x >= 1) to conclude infeasibility.
        let mut s = single_var_solver();
        let lo = s.register_atom(Var::int(0), Constraint::Ge, rbig!(1 / 3));
        let hi = s.register_atom(Var::int(0), Constraint::Le, rbig!(2 / 3));
        s.assert_atom(lo);
        s.assert_atom(hi);
        assert!(
            matches!(s.check(), CheckResult::Unsat { .. }),
            "expected LIA-unsat via B&B"
        );
    }

    #[test]
    fn check_does_not_leak_branch_and_bound_levels() {
        // Regression: `LIRASolver::branch_and_bound` returns FEASIBLE the moment it finds an
        // integer-feasible node, leaving speculative branch bounds asserted on the LRA. The
        // incremental `check()` must contain those bounds so subsequent asserts see only
        // the externally-asserted state.
        //
        // Behavior probe (counter is a monotonic timestamp, so a value check is meaningless):
        // after `check()` returns, the pre-check bounds must still be enforced, and a fresh
        // assert that would only conflict with a *branch* bound (e.g. x = 2 when B&B picked
        // x=1) must succeed.
        let mut s = single_var_solver();
        s.register_root(100, Var::int(0));

        let level = s.push();
        let lo = s.register_atom(Var::int(0), Constraint::Ge, rbig!(1 / 2));
        let hi = s.register_atom(Var::int(0), Constraint::Le, rbig!(5));
        s.assert_atom(lo);
        s.assert_atom(hi);

        let pre_bounds = s.lra().get_bounds(&Var::int(0)).unwrap();
        // Force B&B: fractional LRA solution (1/2) → branch(es) → integer node → early exit.
        assert!(matches!(s.check(), CheckResult::Sat { .. }));
        let post_bounds = s.lra().get_bounds(&Var::int(0)).unwrap();
        assert_eq!(
            (pre_bounds.lower, pre_bounds.upper),
            (post_bounds.lower, post_bounds.upper),
            "check() leaked branch-and-bound bounds past the check boundary"
        );

        // Previously-asserted external bound x <= 5 still in effect: asserting a
        // contradictory upper (x <= 0) is still a bound-vs-bound conflict.
        let bad = s.register_atom(Var::int(0), Constraint::Le, rbig!(0));
        assert_eq!(s.assert_atom(bad), AssertOutcome::Conflict);
        s.pop(level);
    }

    #[test]
    fn check_is_idempotent() {
        // Calling `check()` twice back-to-back on the same asserted set must return
        // consistent verdicts. The persistent LIRASolver's explorer would otherwise be
        // left in a terminal state after the first call and the second would either hit
        // an `unreachable!` inside `branch_and_bound` or produce a stale result.
        let mut s = single_var_solver();
        s.register_root(100, Var::int(0));
        let lo = s.register_atom(Var::int(0), Constraint::Ge, rbig!(1 / 2));
        let hi = s.register_atom(Var::int(0), Constraint::Le, rbig!(3));
        s.assert_atom(lo);
        s.assert_atom(hi);
        assert!(matches!(s.check(), CheckResult::Sat { .. }));
        assert!(matches!(s.check(), CheckResult::Sat { .. }));

        // Same story on the unsat side.
        let mut u = single_var_solver();
        let lo = u.register_atom(Var::int(0), Constraint::Ge, rbig!(1 / 3));
        let hi = u.register_atom(Var::int(0), Constraint::Le, rbig!(2 / 3));
        u.assert_atom(lo);
        u.assert_atom(hi);
        assert!(matches!(u.check(), CheckResult::Unsat { .. }));
        assert!(matches!(u.check(), CheckResult::Unsat { .. }));
    }

    // ─── Stage 6: egraph-implied equality as retractable bound ──────────────────

    /// Two-Int-variable solver: non-basic `x` and `y` (cols 0, 1), no relations. Callers
    /// register atoms directly on `x`/`y` and use `register_var_equality(x, y)` to add an
    /// equality slack post-hoc via [`LRASolver::add_slack_row`].
    fn two_int_solver() -> IncrementalArithSolver {
        let non_basic = vec![
            VarInfo::new(Var::int(0), Owner::NonBasic(0)),
            VarInfo::new(Var::int(1), Owner::NonBasic(1)),
        ];
        // At least one basic variable is required by from_eqs; add a dummy row `s = 0`
        // that references no non-basic vars.
        let basic = vec![
            VarInfo::new(Var::real(2), Owner::Basic(0)).with_bounds(Bounds::unbounded()),
        ];
        let equations = vec![vec![rbig!(0), rbig!(0)]];
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
    fn equality_bound_forces_infeasibility() {
        // x >= 5 ∧ y <= 3, feasible with x=5, y=3. Adding x = y is unsat.
        let mut s = two_int_solver();
        let x_lo = s.register_atom(Var::int(0), Constraint::Ge, rbig!(5));
        let y_hi = s.register_atom(Var::int(1), Constraint::Le, rbig!(3));
        s.assert_atom(x_lo);
        s.assert_atom(y_hi);
        assert!(matches!(s.check(), CheckResult::Sat { .. }));

        // Assert x = y with a fake justification literal `999` (mock egraph-merge explanation).
        let outcome = s.assert_equality(Var::int(0), Var::int(1), vec![999]);
        // Either the assert-time or the check-time path must report infeasibility.
        let unsat_after_check = matches!(s.check(), CheckResult::Unsat { .. });
        assert!(
            outcome == AssertOutcome::Conflict || unsat_after_check,
            "expected equality assertion to yield unsat (outcome={outcome:?}, unsat_after_check={unsat_after_check})"
        );

        // And the justification literal 999 should appear in the core.
        match s.check() {
            CheckResult::Unsat { core_literals, .. } => {
                assert!(
                    core_literals.contains(&999),
                    "expected justification lit 999 in unsat core, got {core_literals:?}"
                );
            }
            other => panic!("expected Unsat, got {other:?}"),
        }
    }

    #[test]
    fn equality_bound_retracts_on_pop() {
        let mut s = two_int_solver();
        let x_lo = s.register_atom(Var::int(0), Constraint::Ge, rbig!(5));
        let y_hi = s.register_atom(Var::int(1), Constraint::Le, rbig!(3));
        s.assert_atom(x_lo);
        s.assert_atom(y_hi);

        // Wrap the equality in a scope so it can be popped.
        let level = s.push();
        s.assert_equality(Var::int(0), Var::int(1), vec![]);
        assert!(matches!(s.check(), CheckResult::Unsat { .. }));

        // Pop discards the equality bound; feasibility must return.
        s.pop(level);
        assert!(matches!(s.check(), CheckResult::Sat { .. }));
    }

    #[test]
    fn register_var_equality_is_idempotent() {
        let mut s = two_int_solver();
        let ncols_before = s.lra().tableau_ncols_for_test();
        let (le1, ge1) = s.register_var_equality(Var::int(0), Var::int(1));
        let nrows_after_first = s.lra().tableau_nrows_for_test();

        // Second call in either order returns the same atom IDs and doesn't grow the
        // tableau. Also confirms the sorted-pair key handles (a, b) and (b, a) the same.
        let (le2, ge2) = s.register_var_equality(Var::int(1), Var::int(0));
        assert_eq!(le1, le2);
        assert_eq!(ge1, ge2);
        assert_eq!(s.lra().tableau_nrows_for_test(), nrows_after_first);
        // Columns never change under add_slack_row.
        assert_eq!(s.lra().tableau_ncols_for_test(), ncols_before);
    }
}
