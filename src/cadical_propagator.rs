// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::arithmetic::lp::{ArithResult, ArithSolver, check_integer_constraints_satisfiable};
use crate::arithmetic::nelsonoppen::nelson_oppen_trichotomy_terms;
#[cfg(feature = "z3-solver")]
use crate::arithmetic::z3incremental::{PartialCheckResult, Z3IncrementalState};
use crate::debug_println;
use crate::egraphs::EgraphTrait;
use crate::egraphs::traits::Conflict;
use crate::log::is_important;
use crate::proof::{SMTProofTracer, Theory};
use crate::quantifiers::quantifier::QuantifierInstance::{Instantiation, Skolemization};
use crate::quantifiers::quantifier::{
    PendingInstantiations, instantiate_quantifiers, materialize_next,
};
use crate::solver_state::{SolverState, process_assignment};
use crate::stats::SolverStats;
use crate::utils::{DeterministicHashMap, DeterministicHashSet};
use cadical_sys::{CaDiCal, ExternalPropagator};
use std::cell::RefCell;
use std::rc::Rc;

#[derive(Clone, Copy)]
pub(crate) enum EagerQiMode {
    Disabled,
    Bounded { limit: usize, remaining: usize },
    FullRound { started: bool },
}

enum EagerQiAction {
    Bounded(usize),
    FullRound,
}

impl EagerQiMode {
    pub(crate) fn new(value: i32) -> Self {
        if value < 0 {
            Self::FullRound { started: false }
        } else if value == 0 {
            Self::Disabled
        } else {
            let limit = usize::try_from(value).expect("positive i32 must fit in usize");
            Self::Bounded {
                limit,
                remaining: limit,
            }
        }
    }

    fn next_action(&mut self) -> Option<EagerQiAction> {
        match self {
            Self::Disabled | Self::Bounded { remaining: 0, .. } => None,
            Self::Bounded { remaining, .. } => Some(EagerQiAction::Bounded(*remaining)),
            Self::FullRound { started: true } => None,
            Self::FullRound { started } => {
                *started = true;
                Some(EagerQiAction::FullRound)
            }
        }
    }

    fn consume(&mut self, count: usize) {
        if let Self::Bounded { remaining, .. } = self {
            *remaining -= count;
        }
    }

    fn reset(&mut self) {
        match self {
            Self::Disabled => {}
            Self::Bounded { limit, remaining } => *remaining = *limit,
            Self::FullRound { started } => *started = false,
        }
    }
}

/// Our implementation of a Cadical Propagator
pub struct CustomExternalPropagator<'a> {
    pub decision_level: usize,
    pub solver_state: &'a mut SolverState,
    pub disequalities: RefCell<Vec<Vec<i32>>>, // might be paying a bit of overhead for RefCell
    pub fixed_literals: DeterministicHashSet<i32>,
    pub proof_tracer: Rc<RefCell<SMTProofTracer>>,
    pub assignments: Vec<i32>, // maps abs(literal) -> (decision level assigned + 1) * sgn(literal)
    pub solver: *mut CaDiCal,
    pub arithmetic: ArithSolver, // whether we are doing arithmetic solving or not
    pub stats: SolverStats,
    pub pending: Option<PendingInstantiations>,
    pub(crate) eager_qi: EagerQiMode,
    /// Prevent nested QI while observing variables created by materialization.
    pub materializing_quantifiers: bool,
    /// Max number of arithmetic-model conflicts to collect per cb_check_found_model call.
    /// Once reached, stop probing further pairs even if unprobed pairs remain.
    pub max_arith_conflicts_per_round: usize,
    pub last_observed_var: i32,
    /// Max instantiations to materialize per complete-model check. 0 = unbounded.
    pub batch_cap: usize,
    /// Incremental Z3 arithmetic state — Some iff `arithmetic == ArithSolver::Z3Incremental`.
    #[cfg(feature = "z3-solver")]
    pub z3_incremental: Option<Z3IncrementalState>,
    // --trail-out logging (inert unless the writer is Some). Trails stream to
    // disk as they are refuted; the small |lit| -> atom map is held and flushed
    // at the end (only complete then, as new literals appear during the search).
    pub trail_writer: Option<std::io::BufWriter<std::fs::File>>,
    pub trail_atoms: std::collections::HashMap<i32, String>,
}

impl<'a> CustomExternalPropagator<'a> {
    #[cfg(feature = "z3-solver")]
    fn check_partial_arithmetic_trail(&mut self) {
        let Some(z3) = self.z3_incremental.as_mut() else {
            return;
        };
        match z3.check_partial_trail() {
            PartialCheckResult::Unchanged => {}
            PartialCheckResult::Sat => {
                self.stats.arith_checks += 1;
            }
            PartialCheckResult::Unsat(clause) => {
                self.stats.arith_checks += 1;
                debug_println!(
                    21,
                    0,
                    "PROPAGATOR: Partial arithmetic inconsistency detected: {:?}",
                    clause
                );
                self.queue_theory_clause(clause, Theory::QfLia);
                self.stats.conflicts += 1;
            }
        }
    }

    /// Stream one refuted model as a `t <signed lits>` line. A write error is
    /// reported once then the writer is dropped; it must never abort the solve.
    fn write_trail_line(&mut self, model: &[i32]) {
        use std::io::Write;
        let Some(w) = self.trail_writer.as_mut() else {
            return;
        };
        let mut line = String::with_capacity(model.len() * 5 + 2);
        line.push('t');
        for lit in model {
            use std::fmt::Write as _;
            let _ = write!(line, " {lit}");
        }
        if let Err(e) = writeln!(w, "{line}") {
            debug_println!(2, 0, "Failed to stream trail line: {}", e);
            self.trail_writer = None; // stop trying after the first failure
        }
    }

    /// Append the `m <id> <atom>` map (sorted by id) and close the trail log.
    /// Called once after the solve, when the literal set is finally complete.
    pub fn finish_trail_log(&mut self) {
        use std::io::Write;
        let Some(mut w) = self.trail_writer.take() else {
            return;
        };
        let mut ids: Vec<&i32> = self.trail_atoms.keys().collect();
        ids.sort();
        let res = (|| -> std::io::Result<()> {
            for id in ids {
                writeln!(w, "m {} {}", id, self.trail_atoms[id])?;
            }
            w.flush()
        })();
        if let Err(e) = res {
            debug_println!(2, 0, "Failed to write trail atom map: {}", e);
        }
    }

    /// Register any new CNF variables created since the last sync.
    pub fn sync_new_vars(&mut self) {
        let next = self.solver_state.cnf_cache.next_var;
        if next <= self.last_observed_var {
            return;
        }
        let start = self.last_observed_var;
        self.last_observed_var = next;
        for var in start..next {
            if let Some(&uid) = self.solver_state.cnf_cache.var_map_reverse.get(&var) {
                if self.solver_state.get_term_safe(uid).is_none() {
                    continue;
                }
                self.add_observed_variable(var);
                self.add_lit_to_proof_tracer(var);
            }
        }
    }

    pub fn add_lit_to_proof_tracer(&mut self, lit: i32) {
        let lit = lit.abs(); // only add the positive version
        if self.proof_tracer.borrow().is_lit_registered(lit) {
            debug_println!(
                19,
                0,
                "We have already added literal {lit} to the proof tracker"
            );
            return;
        }
        debug_println!(
            19,
            0,
            "Adding literal {lit} i.e. {} to proof tracker with uid {}",
            self.solver_state.get_term_from_lit(lit),
            self.solver_state.get_term_from_lit(lit).uid()
        );

        if let Some(id) = self.solver_state.cnf_cache.var_map_reverse.get(&lit) {
            if self.solver_state.get_term_safe(*id).is_none() {
                return;
            }
            let term = self.solver_state.get_term(*id);
            self.proof_tracer
                .borrow_mut()
                .register_term(lit, &term, true);
        } else if let Some(id) = self.solver_state.cnf_cache.var_map_reverse.get(&-lit) {
            if self.solver_state.get_term_safe(*id).is_none() {
                return;
            }
            let term = self.solver_state.get_term(*id);
            self.proof_tracer
                .borrow_mut()
                .register_term(-lit, &term, false);
        }
    }

    /// Add a literal as an observed variable to the solver
    fn add_observed_variable(&mut self, lit: i32) {
        let abs_lit = lit.abs();
        debug_println!(
            7,
            0,
            "Adding literal {} as observed variable to solver",
            abs_lit
        );
        unsafe {
            (*self.solver).add_observed_var(abs_lit);
        }
    }

    /// Emit `(x<y ∨ x>y ∨ x=y)` as a raw 3-literal clause (no Tseitin gate).
    /// No-op if this pair's trichotomy has already been emitted. The `true`
    /// on `insert_predecessor` is the `dynamic: true` flag — these atoms may
    /// exist elsewhere in the egraph and we want congruence to find them.
    fn emit_trichotomy_for_pair(&mut self, x: u64, y: u64) {
        if let Some((lt_term, gt_term, eq_term)) =
            nelson_oppen_trichotomy_terms(x, y, self.solver_state)
        {
            self.solver_state
                .insert_predecessor(&lt_term, None, None, true);
            self.solver_state
                .insert_predecessor(&gt_term, None, None, true);
            self.solver_state
                .insert_predecessor(&eq_term, None, None, true);
            let lt_lit = self.solver_state.get_or_allocate_lit_for_term(&lt_term);
            let gt_lit = self.solver_state.get_or_allocate_lit_for_term(&gt_term);
            let eq_lit = self.solver_state.get_or_allocate_lit_for_term(&eq_term);
            let clause = vec![lt_lit, gt_lit, eq_lit];
            self.sync_new_vars();
            self.queue_theory_clause(clause, Theory::QfLia);
        }
    }

    /// Queues a clause whose proof step has already been recorded.
    fn queue_external_clause(&self, clause: Vec<i32>) {
        self.proof_tracer
            .borrow_mut()
            .register_clause_for_cadical_callback(&clause);
        self.disequalities.borrow_mut().push(clause);
    }

    fn queue_theory_clause(&self, clause: Vec<i32>, theory: Theory) {
        self.proof_tracer
            .borrow_mut()
            .add_theory_clause(&clause, theory);
        self.queue_external_clause(clause);
    }

    pub fn sync_external_stats(&mut self) {
        self.stats.egraph_merges = self.solver_state.egraph.stats.merges;
        self.stats.bool_vars = (self.solver_state.cnf_cache.next_var - 1) as u64;
        self.stats.deleted_clauses = self.proof_tracer.borrow().deleted_clauses;
        self.stats.dt_accessor_ax = self.solver_state.stat_dt_accessor_ax;
        self.stats.dt_constructor_ax = self.solver_state.stat_dt_constructor_ax;
        self.stats.dt_splits = self.solver_state.stat_dt_splits;
    }

    fn apply_instances(
        &mut self,
        instances: &[crate::quantifiers::quantifier::QuantifierInstance],
    ) {
        for inst in instances {
            let clauses = match inst {
                Instantiation { clauses } => {
                    self.stats.instantiations += 1;
                    clauses
                }
                Skolemization { clauses } => clauses,
            };
            for clause in clauses {
                self.queue_external_clause(clause.clone());
            }
        }
        // Materializing an instance can enqueue arithmetic merges (via
        // `insert_predecessor`'s congruence closure). Drain them so the queue is
        // empty before control returns to CaDiCaL, as `notify_new_decision_level`
        // requires.
        #[cfg(feature = "z3-solver")]
        if let Some(z3) = self.z3_incremental.as_mut() {
            z3.drain_merge_queue(self.solver_state);
        }
        self.sync_new_vars();
    }

    /// Materialize up to `cap` items from the current matching round.
    /// A zero cap is unbounded.
    fn materialize_pending(&mut self, cap: usize) -> usize {
        let Some(mut pending) = self.pending.take() else {
            return 0;
        };
        debug_assert!(!self.materializing_quantifiers);
        self.materializing_quantifiers = true;

        let mut count = 0;
        while (cap == 0 || count < cap)
            && let Some(instances) =
                materialize_next(&mut pending, self.solver_state, &self.proof_tracer)
        {
            self.apply_instances(&instances);
            count += 1;
        }

        self.materializing_quantifiers = false;
        if pending.is_empty() {
            for i in pending.skolemized_quantifier_idxs() {
                self.solver_state.quantifiers[*i].skolemized = true;
            }
        } else {
            self.pending = Some(pending);
        }

        count
    }

    /// Refresh trigger matches only after every item from the previous matching
    /// round has been materialized.
    fn start_quantifier_instantiation_round(&mut self, allow_skolemization: bool) -> bool {
        debug_assert!(self.pending.is_none());
        let pending =
            instantiate_quantifiers(self.solver_state, &self.assignments, allow_skolemization);
        if pending.is_empty() {
            return false;
        }

        self.sync_external_stats();
        self.stats.begin_round();
        self.stats.instantiation_rounds += 1;
        self.pending = Some(pending);
        true
    }

    fn reset_eager_qi_for_level(&mut self) {
        self.eager_qi.reset();
    }

    /// Add instances from the current partial assignment according to the
    /// configured per-level eager mode. Skolemization remains a complete-model
    /// operation.
    fn eagerly_instantiate_quantifiers(&mut self) {
        if self.materializing_quantifiers || !self.disequalities.borrow().is_empty() {
            return;
        }

        match self.eager_qi.next_action() {
            None => {}
            Some(EagerQiAction::FullRound) => {
                // Work from an earlier matching round must not be discarded or
                // mixed with the one fresh round for this level.
                self.materialize_pending(0);
                if self.start_quantifier_instantiation_round(false) {
                    self.materialize_pending(0);
                }
            }
            Some(EagerQiAction::Bounded(budget)) => {
                if self.pending.is_none() && !self.start_quantifier_instantiation_round(false) {
                    return;
                }
                let materialized = self.materialize_pending(budget);
                self.eager_qi.consume(materialized);
            }
        }
    }
}

impl<'a> ExternalPropagator for CustomExternalPropagator<'a> {
    fn notify_assignment(&mut self, lits: &[i32]) {
        debug_println!(
            22,
            0,
            "PROPAGATOR: Processing assignments (level {}): {:?}",
            self.decision_level,
            lits
        );
        debug_println!(16, 0, "{}", self.solver_state.egraph);
        for lit in lits {
            debug_println!(
                7,
                0,
                "Assigning the literal {:?} (level {}) which is {}",
                lit,
                self.decision_level,
                self.solver_state.get_term_from_lit(*lit)
            );

            // adding the literal to the assignment
            // add with level (negatively if we learn its negation)
            while self.assignments.len() <= lit.unsigned_abs() as usize {
                self.assignments.resize(2 * self.assignments.len(), 0);
            }
            let lit_sign = if *lit > 0 { 1 } else { -1 };
            self.assignments[lit.unsigned_abs() as usize] =
                ((self.decision_level + 1) as i32) * lit_sign;

            if self.fixed_literals.contains(lit) {
                debug_println!(6, 0, "Skipping literal {lit} because it is fixed");
                continue;
            }

            self.add_lit_to_proof_tracer(*lit);

            let negated_model_or_datatype_constraints_opt =
                process_assignment(*lit, self.solver_state, self.decision_level);

            // Drain merges triggered by this assignment, then push the lit
            // itself if it's arithmetic.
            #[cfg(feature = "z3-solver")]
            {
                if let Some(z3) = self.z3_incremental.as_mut() {
                    z3.drain_merge_queue(self.solver_state);
                    z3.on_literal_assignment(*lit, self.solver_state);
                }
            }
            self.sync_new_vars();

            if let Some(negated_model_or_datatype_constraints) =
                negated_model_or_datatype_constraints_opt
            {
                for (constraint, theory) in negated_model_or_datatype_constraints {
                    // todo: deleting this ordering thing -> just for debugging
                    let mut constraint_ordered = constraint.clone();
                    constraint_ordered.sort();
                    debug_println!(
                        16,
                        0,
                        "[in notify_assignment] We have the following constraint: {:?}",
                        constraint_ordered
                    );
                    if is_important(12) {
                        for lit in constraint.clone() {
                            debug_println!(12, 4, "{}", self.solver_state.get_term_from_lit(lit));
                        }
                    }
                    let mut shrunk_constraint = vec![];
                    let mut already_considered = DeterministicHashSet::default();
                    for lit in constraint {
                        if already_considered.contains(&lit) {
                            // TODO: we are checking for repeats here, but we should fix this at the conflict clause level so that we never get repeats
                            // the repeats are coming from (= x y) and true being merged and x and y being merged
                            debug_println!(
                                2,
                                0,
                                "Skipping literal {lit} from negated model because it is repeated"
                            );
                        } else {
                            shrunk_constraint.push(lit);
                            already_considered.insert(lit);
                        }
                    }
                    // todo: deleting this ordering thing -> just for debugging
                    let mut shrunk_constraint_ordered = shrunk_constraint.clone();
                    shrunk_constraint_ordered.sort();
                    debug_println!(
                        16,
                        1,
                        "After shrinking [ in notify_assignment]: {:?}",
                        shrunk_constraint_ordered
                    );
                    debug_println!(11, 1, "This corresponds to ");
                    for lit in shrunk_constraint.iter() {
                        debug_println!(11, 1, "  {}", self.solver_state.get_term_from_lit(*lit));
                    }
                    self.sync_new_vars();

                    // Store the theory lemma with its proof steps
                    // TODO: I am not doing proof step stuff right now, but I need to add it back in
                    // let proof_steps = self.solver_state.egraph.get_proof_steps_for_lemma(&shrunk_constraint);

                    debug_println!(
                        14 - 3,
                        0,
                        "In case 1 currently disequalities: {:?}",
                        self.disequalities.borrow()
                    );

                    // let theory_reason = format!("congruence_closure_level_{}", self.decision_level);
                    self.queue_theory_clause(shrunk_constraint, theory);
                    debug_println!(
                        14 - 3,
                        0,
                        "We have the following disequalities: {:?}",
                        self.disequalities.borrow()
                    );
                }
            }
        }

        // Trigger matching, like incremental arithmetic above, can use a
        // partial assignment. Existing pending work is always consumed before
        // another matching round is created.
        self.eagerly_instantiate_quantifiers();
        #[cfg(feature = "z3-solver")]
        self.check_partial_arithmetic_trail();
    }

    fn notify_new_decision_level(&mut self) {
        self.stats.decisions += 1;
        debug_println!(
            11,
            0,
            "PROPAGATOR: New decision level {} -> {}",
            self.decision_level,
            self.decision_level + 1
        );
        self.decision_level += 1;
        self.reset_eager_qi_for_level();
        // Record solver hash at new level
        while self.decision_level >= self.solver_state.hash_at_level.len() {
            self.solver_state
                .hash_at_level
                .resize(self.solver_state.hash_at_level.len() * 2, 0);
        }
        self.solver_state.hash_at_level[self.decision_level] = self.solver_state.current_hash;

        self.solver_state.egraph.notify_new_decision_level();

        #[cfg(feature = "z3-solver")]
        if let Some(z3) = self.z3_incremental.as_mut() {
            z3.notify_new_decision_level();
        }
    }

    fn notify_backtrack(&mut self, level: usize) {
        self.stats.backtracks += 1;
        debug_println!(
            23,
            0,
            "PROPAGATOR: Backtracking from level {} to level {}",
            self.decision_level,
            level
        );

        // Reset solver-level assignments
        for i in 1..self.assignments.len() {
            if self.assignments[i].abs() > (level + 1) as i32 {
                self.assignments[i] = 0;
            }
        }

        // Bump solver hash on backtrack and invalidate higher levels
        self.solver_state.current_hash += 1;
        for i in level + 1..self.decision_level + 1 {
            if i < self.solver_state.hash_at_level.len() {
                self.solver_state.hash_at_level[i] = self.solver_state.current_hash;
            }
        }

        self.decision_level = level;
        self.reset_eager_qi_for_level();

        // `backtrack_to` clears the arithmetic queue at entry then re-fires
        // any congruence merges from `union_to_eclass` replay, so the queue
        // on return holds exactly the merges that survive at `level`.
        self.solver_state.egraph.backtrack_to(level);

        #[cfg(feature = "z3-solver")]
        {
            if let Some(z3) = self.z3_incremental.as_mut() {
                z3.notify_backtrack(level);
                z3.drain_merge_queue(self.solver_state);
            }
        }
        self.sync_new_vars();

        debug_println!(16, 0, "Ending backtracking at level {}", level);
        debug_println!(11, 0, "{}", self.solver_state.egraph);
    }

    fn cb_check_found_model(&mut self, model: &[i32]) -> bool {
        // --trail-out: every model seen here in a non-SAT run is refuted;
        // note any new literals in the atom map and stream the trail line.
        if self.trail_writer.is_some() {
            for &l in model {
                let id = l.unsigned_abs() as i32;
                if !self.trail_atoms.contains_key(&id) {
                    let atom = format!("{}", self.solver_state.get_term_from_lit(id));
                    self.trail_atoms.insert(id, atom);
                }
            }
            self.write_trail_line(model);
        }

        debug_println!(
            24,
            0,
            "PROPAGATOR: Checking model: {:?} [{:?}]",
            model,
            model
                .iter()
                .map(|x| self.solver_state.get_term_from_lit(*x))
                .collect::<Vec<_>>(),
        );

        if !self.disequalities.borrow_mut().is_empty() {
            debug_println!(
                24,
                0,
                "Trying to check model when the disequalities are not empty"
            );
            self.stats.conflicts += 1;
            return false;
        }

        // If we have pending instantiations from a previous round, materialize one
        // immediately without redoing arithmetic or datatype checks.
        if self.pending.is_some() && self.materialize_pending(1) > 0 {
            self.stats.conflicts += 1;
            return false;
        }

        for term in model {
            let (u64_val, polarity) = self.solver_state.get_u64_from_lit_with_polarity(*term);
            debug_println!(
                24,
                4,
                "{} [lit: {}] [u64: {} with polarity {}]",
                self.solver_state.get_term_from_lit(*term),
                term,
                u64_val,
                polarity
            );
        }
        debug_println!(24, 0, "{}", self.solver_state.egraph);

        // Check arithmetic consistency
        debug_println!(21, 0, "Starting arithmetic check",);
        self.stats.arith_checks += 1;

        // The incremental backend already saw every atom via notify_assignment
        // — just flush any post-hoc merges and call check(). Otherwise use the
        // eager entry point.
        #[cfg(feature = "z3-solver")]
        let arith_result = if let Some(z3) = self.z3_incremental.as_mut() {
            z3.drain_merge_queue(self.solver_state);
            z3.check(self.solver_state)
        } else {
            check_integer_constraints_satisfiable(&self.arithmetic, model, self.solver_state)
        };
        self.sync_new_vars();
        #[cfg(not(feature = "z3-solver"))]
        let arith_result =
            check_integer_constraints_satisfiable(&self.arithmetic, model, self.solver_state);

        match arith_result {
            ArithResult::Unsat(arithmetic_literals, arith_stats) => {
                self.stats.arith.accumulate(&arith_stats);
                {
                    debug_println!(
                        21,
                        0,
                        "PROPAGATOR: Arithmetic inconsistency detected: {:?}",
                        arithmetic_literals
                    );
                    self.queue_theory_clause(arithmetic_literals, Theory::QfLia);
                    self.stats.conflicts += 1;
                    return false;
                }
            }
            ArithResult::Sat(literals, arith_stats) => {
                self.stats.arith.accumulate(&arith_stats);
                debug_assert!(
                    self.max_arith_conflicts_per_round > 0,
                    "max_arith_conflicts_per_round must be > 0"
                );
                // Nelson-Oppen probe: try to merge every pair of terms Z3
                // gave the same model value. Each merge gets its own probe
                // level so a conflict can be undone without losing earlier
                // successful merges. Collect all conflicts, then backtrack
                // the whole probe stack.
                let base_level = self.decision_level;
                let mut probe_level = base_level;
                let mut conflicts: Vec<Conflict<u32>> = Vec::new();
                // Probed pairs, keyed by canonical (egraph_root, egraph_root).
                let mut probe_pair_uids: DeterministicHashMap<(u32, u32), (u64, u64)> =
                    DeterministicHashMap::default();

                'outer: for set in literals.values() {
                    let mut t = set.iter();
                    let first = t.next().unwrap();
                    for term in t {
                        let (x, y) = if first < term {
                            (*first, *term)
                        } else {
                            (*term, *first)
                        };
                        let x_root = self.solver_state.to_egraph_id(x);
                        let y_root = self.solver_state.to_egraph_id(y);
                        if self.solver_state.egraph.find(x_root)
                            == self.solver_state.egraph.find(y_root)
                        {
                            continue;
                        }
                        let (lo_root, hi_root) = if x_root < y_root {
                            (x_root, y_root)
                        } else {
                            (y_root, x_root)
                        };
                        probe_pair_uids.insert((lo_root, hi_root), (x, y));
                        // Bump the egraph's decision level so this speculative
                        // merge can be undone individually if it conflicts.
                        self.solver_state.egraph.notify_new_decision_level();
                        probe_level += 1;
                        let result = self.solver_state.egraph.assert_equal(x_root, y_root);
                        // Probe merges are speculative — discard queue entries
                        // so they don't leak into Z3IncrementalState.
                        let _ = self.solver_state.egraph.drain_arithmetic_equalities();
                        if let Some(c) = result.conflict {
                            self.solver_state.egraph.backtrack_to(probe_level - 1);
                            probe_level -= 1;
                            conflicts.push(c);
                            if conflicts.len() >= self.max_arith_conflicts_per_round {
                                break 'outer;
                            }
                        }
                    }
                }

                for conflict in &conflicts {
                    // Walk the proof path backward, pick the last probe-merged
                    // pair whose trichotomy hasn't been emitted yet. Emit at
                    // most one trichotomy per conflict; other probed pairs
                    // fall back on `make_eq` allocating a bare eq lit.
                    let fresh_probe_pair = conflict.equalities.iter().rev().find_map(|&(a, b)| {
                        let (lo_root, hi_root) = if a < b { (a, b) } else { (b, a) };
                        let (x_uid, y_uid) = *probe_pair_uids.get(&(lo_root, hi_root))?;
                        if self
                            .solver_state
                            .nelson_oppen_ineq_literals
                            .contains(&(x_uid, y_uid))
                        {
                            None
                        } else {
                            Some((x_uid, y_uid))
                        }
                    });
                    if let Some((x_uid, y_uid)) = fresh_probe_pair {
                        self.emit_trichotomy_for_pair(x_uid, y_uid);
                    }

                    let mut conflict_clause: Vec<i32> = conflict
                        .equalities
                        .iter()
                        .map(|(a, b)| -self.solver_state.make_eq(*a, *b))
                        .collect();
                    if let Some(lit) = conflict.diseq_lit {
                        conflict_clause.push(-lit);
                    }

                    self.queue_theory_clause(conflict_clause, Theory::Background);
                }
                self.sync_new_vars();

                // Undo remaining probe merges. `backtrack_to` may repopulate
                // the queue via `union_to_eclass` re-firing (e.g. from the
                // trichotomy terms just registered); drain those into Z3.
                self.solver_state.egraph.backtrack_to(base_level);
                #[cfg(feature = "z3-solver")]
                {
                    if let Some(z3) = self.z3_incremental.as_mut() {
                        z3.drain_merge_queue(self.solver_state);
                    } else {
                        self.solver_state.egraph.drain_arithmetic_equalities();
                    }
                }
                #[cfg(not(feature = "z3-solver"))]
                {
                    self.solver_state.egraph.drain_arithmetic_equalities();
                }
                self.sync_new_vars();
            }
            ArithResult::None => {}
        }

        if !self.disequalities.borrow().is_empty() {
            self.stats.conflicts += 1;
            return false;
        }

        // Occurs check for recursive datatypes (well-foundedness)
        if self.solver_state.datatype_info.has_recursive_datatype() {
            if let Some(conflict_clause) =
                crate::datatypes::occurs_check::datatype_occurs_check(self.solver_state)
            {
                self.queue_theory_clause(conflict_clause, Theory::Datatypes);
                self.stats.conflicts += 1;
                return false;
            }

            // Lazy case split: add tester clauses for uninitialized datatype terms
            let new_clauses =
                crate::datatypes::occurs_check::generate_deferred_tester_clauses(self.solver_state);
            if !new_clauses.is_empty() {
                for clause in new_clauses {
                    self.queue_theory_clause(clause, Theory::Datatypes);
                }
                self.sync_new_vars();
                self.stats.conflicts += 1;
                return false;
            }
        }

        debug_println!(11, 0, "Starting quantifier instantiations");
        if !self.start_quantifier_instantiation_round(true) {
            debug_println!(10, 0, "{}", self.solver_state.egraph);
            assert!(self.disequalities.borrow().is_empty());
            return true;
        }

        // Materialize up to `batch_cap` pending instances in this single check.
        // batch_cap == 0 means unbounded (materialize all).
        let materialized = self.materialize_pending(self.batch_cap);
        debug_assert!(materialized > 0);

        debug_println!(4, 0, "Returning false in cb_check_found_model");
        self.stats.conflicts += 1;
        false
    }

    fn cb_decide(&mut self) -> i32 {
        debug_println!(7, 0, "PROPAGATOR: Decision callback invoked");

        // For recursive datatypes, prefer base-case constructors to avoid infinite expansion
        if self.solver_state.datatype_info.has_recursive_datatype() {
            for &lit in &self.solver_state.base_case_tester_lits {
                let idx = lit.unsigned_abs() as usize;
                while idx >= self.assignments.len() {
                    self.assignments.resize(self.assignments.len() * 2, 0);
                }
                if self.assignments[idx] == 0 {
                    return lit;
                }
            }
        }

        0
    }

    fn cb_propagate(&mut self) -> i32 {
        debug_println!(7, 0, "PROPAGATOR: Propagation callback invoked");
        // For now, no propagation
        // This could deduce new assignments
        0
    }

    fn cb_add_reason_clause_lit(&mut self, _propagated_lit: i32) -> i32 {
        debug_println!(
            7,
            0,
            "PROPAGATOR: Adding reason clause for literal {}",
            _propagated_lit
        );
        // For now, no reason clauses
        // This could explain propagations
        0
    }

    fn cb_has_external_clause(&mut self, is_forgettable: &mut bool) -> bool {
        debug_println!(
            7,
            0,
            "PROPAGATOR: Checking for external clauses (forgettable: {})",
            is_forgettable
        );
        // For now, no external clauses
        if (*self.disequalities.borrow_mut()).is_empty() {
            false
        } else {
            // this is basically saying that the clause is not forgettable; cvc5 also does false
            *is_forgettable = false;
            let clause_len = self.disequalities.borrow().last().map_or(0, |c| c.len());
            match clause_len {
                0 | 1 => {} // don't count unit or empty clauses
                2 => self.stats.binary_clauses += 1,
                _ => self.stats.clauses += 1,
            }
            debug_println!(
                4,
                0,
                "In cb_has_external_clause: We have the following disequalities: {:?}",
                self.disequalities.borrow()[0]
            );
            true
        }
    }

    fn cb_add_external_clause_lit(&mut self) -> i32 {
        // For now, no external clauses
        let mut v = self.disequalities.borrow_mut();
        assert!(!v.is_empty());
        debug_println!(4, 0, "We start with the following disequalities: {:?}", v);
        let last_index = v.len() - 1;
        debug_println!(11, 0, "We have the next clause {:?}", v[last_index]);
        let literal = if v[last_index].is_empty() {
            v.pop();
            0
        } else {
            v[last_index].pop().unwrap()
        };
        drop(v);
        if literal != 0 {
            self.add_lit_to_proof_tracer(literal);
        }
        if let Some(term) = self.solver_state.get_term_from_lit_safe(literal) {
            debug_println!(
                11,
                0,
                "PROPAGATOR: Adding external clause literal (might be negated) {} which is term {}",
                literal,
                term
            );
        } else {
            debug_println!(11, 0, "END OF CLAUSE");
            assert!(literal == 0);
        }
        debug_println!(4, 0, "{}", self.solver_state.egraph);
        literal
    }
}
