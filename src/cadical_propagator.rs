// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::arithmetic::lp::{ArithResult, ArithSolver, check_integer_constraints_satisfiable};
use crate::arithmetic::nelsonoppen::nelson_oppen_trichotomy_terms;
#[cfg(feature = "z3-solver")]
use crate::arithmetic::z3incremental::{PartialCheckResult, Z3IncrementalState};
use crate::cnf::CNFConversion;
use crate::config::RelevancyLevel;
use crate::debug_println;
use crate::egraphs::EgraphTrait;
use crate::egraphs::traits::Conflict;
use crate::proof::{SMTProofTracer, Theory};
use crate::quantifiers::quantifier::QuantifierInstance::{Instantiation, Skolemization};
use crate::quantifiers::quantifier::{
    PendingInstantiations, TriggerMatchScope, instantiate_quantifiers, materialize_next,
};
use crate::relevancy::RelevancyTrait;
use crate::solver_state::{SolverState, process_assignment};
use crate::stats::SolverStats;
use crate::utils::{DeterministicHashMap, DeterministicHashSet};
use cadical_sys::{CaDiCal, ExternalPropagator, Learner};
use std::cell::RefCell;
use std::collections::{HashSet, VecDeque};
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, Ordering};
use yaspar_ir::ast::{ATerm, Repr, TermAllocator};

// --- QI Garbage Collection ---

static QI_GC_TRACE: AtomicBool = AtomicBool::new(false);
static QI_GC_PROFILE: AtomicBool = AtomicBool::new(false);

/// Start eager matching only after CaDiCaL has assigned almost all variables
/// from the original Boolean formula. This keeps QI-created variables from
/// taking over the decision order while still allowing work before final check.
const EAGER_UNASSIGNED_ORIGINAL_LIMIT: usize = 0;

pub(crate) fn init_qi_gc_trace() {
    QI_GC_TRACE.store(
        std::env::var("SUNDANCE_QI_GC_TRACE").is_ok(),
        Ordering::Relaxed,
    );
    QI_GC_PROFILE.store(
        std::env::var("SUNDANCE_QI_GC_PROFILE").is_ok(),
        Ordering::Relaxed,
    );
}

macro_rules! qi_gc_trace {
    ($($arg:tt)*) => {
        if QI_GC_TRACE.load(Ordering::Relaxed) {
            eprintln!("[qi-gc] {}", format!($($arg)*));
        }
    };
}

/// Shared mutable state for QI garbage collection, accessed by the Learner
/// callback, ProofTracer callbacks, and the propagator.
pub(crate) struct QiGcState {
    /// Current activation literal (positive). QI clauses are guarded by its negation.
    pub current_act: i32,
    /// All activation literals ever created (current + previous epochs).
    pub activation_lits: HashSet<i32>,
    /// Conflict clauses captured by the Learner that contain ¬act.
    pub learned_clauses: Vec<Vec<i32>>,
    /// Buffer for the clause currently being received literal-by-literal from Learner.
    pub learner_buf: Vec<i32>,
    /// Epoch counter.
    pub epoch: usize,
    /// QI clauses guarded in the current epoch and over the whole solve.
    pub epoch_guarded_clauses: u64,
    pub total_guarded_clauses: u64,
    /// Instantiations materialized in the current epoch and over the whole solve.
    pub epoch_instantiations: u64,
    pub total_epoch_instantiations: u64,
    /// Number of completed epoch transitions.
    pub transitions: u64,
}

fn retire_activation_unit(activation: i32) -> Vec<i32> {
    vec![-activation]
}

/// Implements CaDiCaL's `Learner` trait to capture conflict clauses containing ¬act.
///
/// CaDiCaL's Learner protocol: for each learned clause, CaDiCaL first calls
/// `learning(size)` — if we return true, it then calls `learn(lit)` for each
/// literal, terminated by `learn(0)`. On receiving 0 we have the full clause.
pub(crate) struct QiGcLearner {
    pub state: Rc<RefCell<QiGcState>>,
}

impl Learner for QiGcLearner {
    fn learning(&mut self, _size: i32) -> bool {
        true
    }

    /// Called by CaDiCaL with each literal of a learned clause, terminated by 0.
    /// On termination, if the clause contains ¬act, we save it — it's a conflict
    /// clause that was derived from QI clauses and must be promoted at epoch end.
    fn learn(&mut self, lit: i32) {
        let mut state = self.state.borrow_mut();
        if lit == 0 {
            let neg_act = -state.current_act;
            if state.learner_buf.contains(&neg_act) {
                qi_gc_trace!(
                    "epoch {}: captured conflict clause (len={}) containing ¬act={}",
                    state.epoch,
                    state.learner_buf.len(),
                    neg_act
                );
                let clause = state.learner_buf.clone();
                state.learned_clauses.push(clause);
            } else if QI_GC_TRACE.load(Ordering::Relaxed) && !state.learner_buf.is_empty() {
                eprintln!(
                    "[qi-gc] learner: clause (len={}) does NOT contain ¬act={}: {:?}",
                    state.learner_buf.len(),
                    neg_act,
                    &state.learner_buf[..state.learner_buf.len().min(5)]
                );
            }
            state.learner_buf.clear();
        } else {
            state.learner_buf.push(lit);
        }
    }
}

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

    fn is_disabled(&self) -> bool {
        matches!(self, Self::Disabled)
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
    /// SAT variables that existed after the original formula was loaded.
    pub(crate) eager_original_vars: Vec<bool>,
    /// Number of original variables that are currently unassigned.
    pub(crate) unassigned_eager_original_vars: usize,
    /// Allow at most one eager matching round before each complete-model check.
    pub(crate) eager_attempted_since_model: bool,
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
    // --- QI Garbage Collection ---
    pub qi_gc_state: Option<Rc<RefCell<QiGcState>>>,
    /// Separate queue for forgettable QI clauses (served with is_forgettable=true).
    pub forgettable_queue: Vec<Vec<i32>>,
    /// Whether the clause currently being drained via cb_add_external_clause_lit is forgettable.
    pub draining_forgettable: bool,
    /// Track whether the next notify_assignment is a decision literal.
    pub next_is_decision: bool,
    /// Flag: next cb_decide should force_backtrack(0) to trigger epoch transition.
    pub qi_gc_force_backtrack: bool,
    /// A root backtrack should perform exactly one requested epoch transition.
    /// Ordinary CaDiCaL backtracks to level zero do not collect QI state.
    pub qi_gc_transition_pending: bool,
    /// Decision level at which each currently assigned SAT literal was last
    /// applied to the theory solvers. A `None` entry means either irrelevant
    /// or waiting in `pending_relevant_assignments`.
    pub theory_processed_levels: Vec<Option<usize>>,
    /// Assigned literals that became relevant and still need theory work.
    pub pending_relevant_assignments: VecDeque<i32>,
    /// Queue-membership bits used to deduplicate pending work.
    pub theory_assignment_pending: Vec<bool>,
    /// Z3-style relevancy level controlling the assignment-to-theory gate.
    pub relevancy_level: RelevancyLevel,
}

impl<'a> CustomExternalPropagator<'a> {
    fn print_qi_gc_profile(&self, event: &str) {
        if !QI_GC_PROFILE.load(Ordering::Relaxed) {
            return;
        }

        let egraph = self.solver_state.egraph.gc_profile();
        let relevance = self.solver_state.relevancy.profile();
        let assigned = self
            .assignments
            .iter()
            .skip(1)
            .filter(|lit| **lit != 0)
            .count();
        let (epoch, transitions, epoch_instances, total_instances, epoch_clauses, total_clauses) =
            self.qi_gc_state.as_ref().map_or((0, 0, 0, 0, 0, 0), |gc| {
                let gc = gc.borrow();
                (
                    gc.epoch,
                    gc.transitions,
                    gc.epoch_instantiations,
                    gc.total_epoch_instantiations,
                    gc.epoch_guarded_clauses,
                    gc.total_guarded_clauses,
                )
            });

        eprintln!(
            "[qi-gc-profile] event={event} elapsed={:.3}s level={} assigned={} \
             decisions={} backtracks={} conflicts={} arith_checks={} \
             epoch={} transitions={} epoch_instances={} total_instances={} \
             epoch_clauses={} total_clauses={} qi_rounds={} pending_qi={}",
            self.stats.elapsed().as_secs_f64(),
            self.decision_level,
            assigned,
            self.stats.decisions,
            self.stats.backtracks,
            self.stats.conflicts,
            self.stats.arith_checks,
            epoch,
            transitions,
            epoch_instances,
            total_instances,
            epoch_clauses,
            total_clauses,
            self.stats.instantiation_rounds,
            self.pending.is_some(),
        );
        eprintln!(
            "[qi-gc-profile] egraph terms={} function_entries={} relevant_entries={} \
             active_relevant_terms={} predecessors={} qi_predecessors={} union_terms={} \
             signatures={} backtrack_entries={} merges={} match_calls={} \
             match_candidates={} relevant_match_candidates={} match_results={}",
            egraph.registered_terms,
            egraph.function_entries,
            egraph.relevant_function_entries,
            egraph.active_relevant_terms,
            egraph.predecessor_entries,
            egraph.qi_predecessor_entries,
            egraph.union_to_eclass_entries,
            egraph.signature_entries,
            egraph.backtrack_entries,
            egraph.merges,
            egraph.e_match_calls,
            egraph.e_match_candidates_scanned,
            egraph.e_match_relevant_candidates_scanned,
            egraph.e_match_results,
        );
        eprintln!(
            "[qi-gc-profile] relevance nodes={} literals={} terms={} classes={} \
             lit_watches={} cond_watches={} ite_watches={} queued={} trail={} \
             arithmetic_terms={} bool_vars={} clauses={} binary_clauses={} deleted_clauses={}",
            relevance.nodes,
            relevance.relevant_literals,
            relevance.relevant_terms,
            relevance.relevant_classes,
            relevance.literal_watches,
            relevance.conditional_watches,
            relevance.term_ite_watches,
            relevance.queued_events,
            relevance.trail_entries,
            self.solver_state.arithmetic_terms.len(),
            self.solver_state.cnf_cache.next_var.saturating_sub(1),
            self.stats.clauses,
            self.stats.binary_clauses,
            self.proof_tracer.borrow().deleted_clauses,
        );

        #[cfg(feature = "z3-solver")]
        if let Some(z3) = self.z3_incremental.as_ref() {
            let z3 = z3.gc_profile();
            eprintln!(
                "[qi-gc-profile] z3 variables={} trackers={} non_arithmetic_lits={} \
                 active_lits={} pushed_scopes={} level_variables={} level={} pending={}",
                z3.variables,
                z3.trackers,
                z3.non_arithmetic_literals,
                z3.active_literals,
                z3.pushed_scopes,
                z3.level_variables,
                z3.current_level,
                z3.pending_partial_assertions,
            );
        }
    }

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
        // Skip activation literals — they have no term mapping.
        if let Some(ref gc) = self.qi_gc_state {
            if gc.borrow().activation_lits.contains(&lit) {
                return;
            }
        }
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

    pub(crate) fn mark_current_vars_as_eager_originals(&mut self) {
        if self.eager_qi.is_disabled() {
            return;
        }
        self.eager_original_vars
            .resize(self.last_observed_var as usize, false);
        self.unassigned_eager_original_vars = 0;
        for var in 1..self.last_observed_var {
            let uid = self
                .solver_state
                .cnf_cache
                .var_map_reverse
                .get(&var)
                .or_else(|| self.solver_state.cnf_cache.var_map_reverse.get(&-var));
            let Some(&uid) = uid else {
                continue;
            };
            if self.solver_state.get_term_safe(uid).is_none()
                || self.solver_state.generation_of(uid) != 0
            {
                continue;
            }
            let idx = var as usize;
            self.eager_original_vars[idx] = true;
            if self.assignments.get(idx).copied().unwrap_or(0) == 0 {
                self.unassigned_eager_original_vars += 1;
            }
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
            let or_term = self.solver_state.context.or(vec![
                lt_term.clone(),
                gt_term.clone(),
                eq_term.clone(),
            ]);
            self.solver_state
                .insert_predecessor(&or_term, None, None, true);
            let cnf_formula = or_term.cnf_tseitin(self.solver_state);
            let cnf_lits: Vec<Vec<i32>> = cnf_formula
                .into_iter()
                .map(|c| c.into_iter().collect())
                .collect();

            // This is a permanent theory lemma. Z3's arithmetic theory marks
            // the atoms it creates as relevant instead of filtering the
            // lemma structurally. Keep the marks at level 0 so they survive
            // backtracking together with the clause.
            self.solver_state.relevancy_register_term(&lt_term, 0);
            self.solver_state.relevancy_register_term(&gt_term, 0);
            self.solver_state.relevancy_register_term(&eq_term, 0);

            self.sync_new_vars();
            for clause in cnf_lits {
                self.queue_theory_clause(clause, Theory::QfLia);
            }
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
            let (clauses, pre_nnf_body, is_instantiation) = match inst {
                Instantiation {
                    clauses,
                    pre_nnf_body,
                } => {
                    self.stats.instantiations += 1;
                    (clauses, pre_nnf_body, true)
                }
                Skolemization {
                    clauses,
                    pre_nnf_body,
                } => (clauses, pre_nnf_body, false),
            };
            if is_instantiation && let Some(ref gc) = self.qi_gc_state {
                let mut gc = gc.borrow_mut();
                gc.epoch_instantiations += 1;
                gc.total_epoch_instantiations += 1;
            }
            // Register the pre-NNF instance body with relevancy so structural
            // rules see the original connectives (Iff/ITE/Implies) before
            // NNF flattens them into Or/And.
            //
            // Register at level 0: QI clauses are permanent in SAT (they
            // survive backtracks), so their relevancy roots must persist
            // too. Registering at `self.decision_level` would leave a
            // gap where the clauses are live but relevancy has forgotten
            // the root after a backtrack past this level.
            self.solver_state.relevancy_register_term(pre_nnf_body, 0);
            for clause in clauses {
                if let Some(ref gc) = self.qi_gc_state {
                    let mut gc = gc.borrow_mut();
                    let neg_act = -gc.current_act;
                    gc.epoch_guarded_clauses += 1;
                    gc.total_guarded_clauses += 1;
                    let epoch = gc.epoch;
                    drop(gc);
                    let mut guarded = clause.clone();
                    guarded.push(neg_act);
                    if QI_GC_TRACE.load(Ordering::Relaxed) {
                        let terms: Vec<String> = clause
                            .iter()
                            .map(|&lit| {
                                if self
                                    .solver_state
                                    .cnf_cache
                                    .var_map_reverse
                                    .contains_key(&lit.abs())
                                {
                                    format!("{}", self.solver_state.get_term_from_lit(lit))
                                } else {
                                    format!("?{}", lit)
                                }
                            })
                            .collect();
                        eprintln!("[qi-gc] QI clause (epoch {}): {:?}", epoch, terms);
                    }
                    self.proof_tracer
                        .borrow_mut()
                        .register_clause_for_cadical_callback(&guarded);
                    self.forgettable_queue.push(guarded);
                } else {
                    self.queue_external_clause(clause.clone());
                }
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
        let started = std::time::Instant::now();
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

        // Registering an instance root can make literals from the existing SAT
        // trail relevant. Their assignments were already reported by CaDiCaL,
        // so no later callback is guaranteed to process their theory effects.
        // Drain those relevance events after materialization is complete and
        // re-entrancy through quantifier materialization is disabled.
        self.process_pending_relevant_assignments();

        // Single-item materialization is the common model-refutation path.
        // Reporting every such item distorts the benchmark and produces
        // megabytes of output; the next matching/periodic snapshot contains
        // the cumulative state. Large batches are useful checkpoint events.
        if QI_GC_PROFILE.load(Ordering::Relaxed) && count > 1 {
            eprintln!(
                "[qi-gc-profile] materialize count={} duration={:.6}s cap={}",
                count,
                started.elapsed().as_secs_f64(),
                cap
            );
            self.print_qi_gc_profile("materialize-complete");
        }

        count
    }

    /// Refresh trigger matches only after every item from the previous matching
    /// round has been materialized.
    fn start_quantifier_instantiation_round(
        &mut self,
        allow_skolemization: bool,
        require_quantifier_relevance: bool,
        trigger_match_scope: TriggerMatchScope,
        generation_limit: Option<u32>,
        instantiation_limit: Option<usize>,
    ) -> bool {
        debug_assert!(self.pending.is_none());
        self.print_qi_gc_profile("qi-match-start");
        let started = std::time::Instant::now();
        let pending = instantiate_quantifiers(
            self.solver_state,
            &self.assignments,
            allow_skolemization,
            require_quantifier_relevance,
            trigger_match_scope,
            generation_limit,
            instantiation_limit,
        );
        if QI_GC_PROFILE.load(Ordering::Relaxed) {
            eprintln!(
                "[qi-gc-profile] qi-match duration={:.6}s produced_work={}",
                started.elapsed().as_secs_f64(),
                !pending.is_empty()
            );
            self.print_qi_gc_profile("qi-match-complete");
        }
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

    fn eager_instantiation_frontier_reached(&self) -> bool {
        self.unassigned_eager_original_vars <= EAGER_UNASSIGNED_ORIGINAL_LIMIT
    }

    /// Epoch transition for QI garbage collection. Called on backtrack to level 0.
    /// Promotes conflict clauses and their QI dependencies to permanent status,
    /// then starts a new epoch with a fresh activation literal.
    fn trigger_epoch_transition(&mut self, gc_state: &Rc<RefCell<QiGcState>>) {
        let gc = gc_state.borrow_mut();
        let old_act = gc.current_act;
        let neg_old_act = -old_act;
        let epoch = gc.epoch;

        qi_gc_trace!(
            "epoch {}: backtrack to level 0, triggering epoch transition",
            epoch
        );
        drop(gc);
        self.print_qi_gc_profile("epoch-transition-start");

        // 1. Permanently retire the old epoch. QI clauses have the shape
        // `¬act ∨ instance`, so asserting `¬act` satisfies any clause CaDiCaL
        // has not physically forgotten.
        let conflict_count = gc_state.borrow().learned_clauses.len();
        self.queue_theory_clause(retire_activation_unit(old_act), Theory::Background);

        // 2. Re-learn captured conflict clauses without ¬act
        let mut gc = gc_state.borrow_mut();
        let learned: Vec<Vec<i32>> = gc.learned_clauses.drain(..).collect();
        drop(gc);
        for clause in learned {
            let promoted: Vec<i32> = clause
                .into_iter()
                .filter(|&lit| lit != neg_old_act)
                .collect();
            if QI_GC_TRACE.load(Ordering::Relaxed) {
                let terms: Vec<String> = promoted
                    .iter()
                    .map(|&lit| {
                        if self
                            .solver_state
                            .cnf_cache
                            .var_map_reverse
                            .contains_key(&lit.abs())
                        {
                            format!("{}", self.solver_state.get_term_from_lit(lit))
                        } else {
                            format!("?{}", lit)
                        }
                    })
                    .collect();
                eprintln!(
                    "[qi-gc] epoch {}: promoting conflict clause: {:?}",
                    epoch, terms
                );
            }
            // A learned unit `¬act` promotes to the empty clause: the QI epoch
            // proved the permanent problem UNSAT. Dropping it would discard
            // the proof and restart an unbounded instantiation sequence.
            self.queue_theory_clause(promoted, Theory::Background);
        }

        // 3. Clear added_instantiations so QI can be re-generated in the next epoch
        let mut gc = gc_state.borrow_mut();
        let cleared_count = self.solver_state.added_instantiations.len();
        self.solver_state.added_instantiations.clear();
        qi_gc_trace!(
            "epoch {}: cleared {} added_instantiations",
            epoch,
            cleared_count
        );

        // 4. Start new epoch
        gc.epoch += 1;
        gc.transitions += 1;
        gc.epoch_guarded_clauses = 0;
        gc.epoch_instantiations = 0;

        // 5. Allocate new activation literal
        let new_act = self.solver_state.cnf_cache.next_var;
        self.solver_state.cnf_cache.next_var += 1;
        gc.current_act = new_act;
        gc.activation_lits.insert(new_act);
        let new_epoch = gc.epoch;
        drop(gc);

        // Observe the new activation literal so CaDiCaL knows it exists.
        unsafe {
            (*self.solver).add_observed_var(new_act);
        }

        qi_gc_trace!(
            "epoch {}: transition complete. promoted {} conflict clauses. new act={}",
            new_epoch,
            conflict_count,
            new_act
        );
        self.print_qi_gc_profile("epoch-transition-complete");
    }

    /// Add instances from the current partial assignment according to the
    /// configured per-level eager mode. Skolemization remains a complete-model
    /// operation.
    fn eagerly_instantiate_quantifiers(&mut self) {
        if self.materializing_quantifiers || !self.disequalities.borrow().is_empty() {
            return;
        }
        if self.pending.is_none()
            && (self.eager_attempted_since_model || !self.eager_instantiation_frontier_reached())
        {
            return;
        }

        match self.eager_qi.next_action() {
            None => {}
            Some(EagerQiAction::FullRound) => {
                self.eager_attempted_since_model = true;
                // Work from an earlier matching round must not be discarded or
                // mixed with the one fresh round for this level.
                self.materialize_pending(0);
                if self.start_quantifier_instantiation_round(
                    false,
                    true,
                    TriggerMatchScope::RelevantClasses,
                    Some(1),
                    None,
                ) {
                    self.materialize_pending(0);
                }
            }
            Some(EagerQiAction::Bounded(budget)) => {
                self.eager_attempted_since_model = true;
                if self.pending.is_none()
                    && !self.start_quantifier_instantiation_round(
                        false,
                        true,
                        TriggerMatchScope::RelevantClasses,
                        Some(1),
                        Some(budget),
                    )
                {
                    return;
                }
                let materialized = self.materialize_pending(budget);
                self.eager_qi.consume(materialized);
            }
        }
    }

    fn ensure_theory_assignment_capacity(&mut self, idx: usize) {
        if idx < self.assignments.len() {
            return;
        }
        let new_len = (idx + 1).max(self.assignments.len() * 2).max(64);
        self.assignments.resize(new_len, 0);
        self.theory_processed_levels.resize(new_len, None);
        self.theory_assignment_pending.resize(new_len, false);
    }

    fn record_sat_assignment(&mut self, lit: i32) {
        let idx = lit.unsigned_abs() as usize;
        self.ensure_theory_assignment_capacity(idx);
        let sign = if lit > 0 { 1 } else { -1 };
        let encoded = ((self.decision_level + 1) as i32) * sign;
        let old = self.assignments[idx];
        debug_assert!(
            old == 0 || old.signum() == encoded.signum(),
            "SAT variable {} was assigned both polarities without a backtrack",
            idx
        );
        if old == 0 && self.eager_original_vars.get(idx).copied().unwrap_or(false) {
            self.unassigned_eager_original_vars -= 1;
        }
        if old == 0 || encoded.abs() < old.abs() {
            self.assignments[idx] = encoded;
        }
    }

    /// Theory atoms can produce useful conflicts from a partial assignment
    /// even when their Boolean context is currently irrelevant. Relevancy
    /// filtering still suppresses pure Boolean/Tseitin structure and inactive
    /// quantifiers, which have no independent theory effect.
    fn is_theory_atom(&mut self, lit: i32) -> bool {
        let term = self.solver_state.get_term_from_lit(lit.abs());
        !matches!(
            term.repr(),
            ATerm::And(_)
                | ATerm::Or(_)
                | ATerm::Not(_)
                | ATerm::Implies(_, _)
                | ATerm::Ite(_, _, _)
                | ATerm::Xor(_)
                | ATerm::Forall(_, _)
                | ATerm::Exists(_, _)
        )
    }

    fn queue_relevant_assignment(&mut self, lit: i32) {
        let idx = lit.unsigned_abs() as usize;
        if self
            .qi_gc_state
            .as_ref()
            .is_some_and(|gc| gc.borrow().activation_lits.contains(&(idx as i32)))
        {
            return;
        }
        self.ensure_theory_assignment_capacity(idx);
        let assignment = self.assignments[idx];
        if assignment == 0
            || self.theory_processed_levels[idx].is_some()
            || self.theory_assignment_pending[idx]
        {
            return;
        }
        let assigned_lit = if assignment > 0 {
            idx as i32
        } else {
            -(idx as i32)
        };
        if self.fixed_literals.contains(&assigned_lit)
            || !self.solver_state.is_lit_relevant(assigned_lit)
        {
            return;
        }
        self.theory_assignment_pending[idx] = true;
        self.pending_relevant_assignments.push_back(assigned_lit);
    }

    fn queue_newly_relevant_assignments(&mut self) {
        self.solver_state.propagate_relevancy();
        let events = self.solver_state.drain_newly_relevant_lits();
        for event in events {
            self.queue_relevant_assignment(event.lit);
        }
    }

    fn apply_theory_assignment(&mut self, lit: i32) {
        self.add_lit_to_proof_tracer(lit);

        let constraints_opt = process_assignment(lit, self.solver_state, self.decision_level);

        self.solver_state.propagate_class_relevancy_from_merges();

        #[cfg(feature = "z3-solver")]
        {
            if let Some(z3) = self.z3_incremental.as_mut() {
                z3.drain_merge_queue(self.solver_state);
                z3.on_literal_assignment(lit, self.solver_state);
            }
        }
        self.sync_new_vars();

        if let Some(constraints) = constraints_opt {
            for (constraint, theory) in constraints {
                let mut shrunk_constraint = Vec::new();
                let mut already_considered = DeterministicHashSet::default();
                for constraint_lit in constraint {
                    if already_considered.insert(constraint_lit) {
                        shrunk_constraint.push(constraint_lit);
                    }
                }
                self.queue_theory_clause(shrunk_constraint, theory);
            }
        }
    }

    fn process_pending_relevant_assignments(&mut self) {
        self.queue_newly_relevant_assignments();
        while let Some(lit) = self.pending_relevant_assignments.pop_front() {
            let idx = lit.unsigned_abs() as usize;
            self.ensure_theory_assignment_capacity(idx);
            self.theory_assignment_pending[idx] = false;

            let assignment = self.assignments[idx];
            if assignment == 0 || self.theory_processed_levels[idx].is_some() {
                continue;
            }
            let assigned_lit = if assignment > 0 {
                idx as i32
            } else {
                -(idx as i32)
            };
            if assigned_lit != lit || !self.solver_state.is_lit_relevant(lit) {
                continue;
            }

            self.apply_theory_assignment(lit);
            self.theory_processed_levels[idx] = Some(self.decision_level);
            self.queue_newly_relevant_assignments();
        }
    }

    #[cfg(debug_assertions)]
    fn assert_relevant_assignments_processed(&mut self) {
        debug_assert!(self.pending_relevant_assignments.is_empty());
        for (idx, assignment) in self.assignments.iter().copied().enumerate().skip(1) {
            if assignment == 0 {
                continue;
            }
            let lit = if assignment > 0 {
                idx as i32
            } else {
                -(idx as i32)
            };
            if self
                .qi_gc_state
                .as_ref()
                .is_some_and(|gc| gc.borrow().activation_lits.contains(&(idx as i32)))
                || self.fixed_literals.contains(&lit)
                || !(self
                    .solver_state
                    .cnf_cache
                    .var_map_reverse
                    .contains_key(&(idx as i32))
                    || self
                        .solver_state
                        .cnf_cache
                        .var_map_reverse
                        .contains_key(&-(idx as i32)))
                || !self.solver_state.is_lit_relevant(lit)
            {
                continue;
            }
            debug_assert!(
                self.theory_processed_levels[idx].is_some(),
                "assigned relevant literal was not processed: lit={} term={}",
                lit,
                self.solver_state.get_term_from_lit(lit)
            );
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
            // Skip activation literals — they have no term in the egraph.
            if let Some(ref gc) = self.qi_gc_state {
                if gc.borrow().activation_lits.contains(&lit.abs()) {
                    self.record_sat_assignment(*lit);
                    continue;
                }
            }

            debug_println!(
                7,
                0,
                "Assigning the literal {:?} (level {}) which is {}",
                lit,
                self.decision_level,
                self.solver_state.get_term_from_lit(*lit)
            );

            // Log decisions
            if self.next_is_decision && QI_GC_TRACE.load(Ordering::Relaxed) {
                self.next_is_decision = false;
                eprintln!(
                    "[qi-gc] decision level {}: lit={} term={}",
                    self.decision_level,
                    lit,
                    self.solver_state.get_term_from_lit(*lit)
                );
            }

            self.record_sat_assignment(*lit);

            // Relevancy propagation always sees the SAT assignment. Any
            // literal that transitions to relevant is emitted as an event;
            // if it is already assigned, the event queues its theory work.
            let structural = self
                .solver_state
                .relevancy
                .notify_assignment(*lit, self.decision_level);
            self.solver_state.propagate_relevancy();
            let is_relevant = structural || self.solver_state.is_lit_relevant(*lit);
            self.queue_newly_relevant_assignments();

            if QI_GC_TRACE.load(Ordering::Relaxed)
                && self
                    .solver_state
                    .cnf_cache
                    .var_map_reverse
                    .contains_key(&lit.abs())
            {
                eprintln!(
                    "[qi-gc] notify_assignment lit={} term={} structural={} is_relevant={}",
                    lit,
                    self.solver_state.get_term_from_lit(*lit),
                    structural,
                    is_relevant
                );
            }

            if self.fixed_literals.contains(lit) {
                debug_println!(6, 0, "Skipping literal {lit} because it is fixed");
                continue;
            }

            if is_relevant {
                self.queue_relevant_assignment(*lit);
            } else if self.relevancy_level.eagerly_processes_irrelevant_atoms()
                && self.is_theory_atom(*lit)
            {
                let idx = lit.unsigned_abs() as usize;
                self.apply_theory_assignment(*lit);
                self.theory_processed_levels[idx] = Some(self.decision_level);
                self.queue_newly_relevant_assignments();
            } else if QI_GC_TRACE.load(Ordering::Relaxed)
                && self
                    .solver_state
                    .cnf_cache
                    .var_map_reverse
                    .contains_key(&lit.abs())
            {
                eprintln!(
                    "[qi-gc] deferred irrelevant lit={} term={}",
                    lit,
                    self.solver_state.get_term_from_lit(*lit)
                );
            }
            self.process_pending_relevant_assignments();
        }

        self.process_pending_relevant_assignments();

        // Trigger matching, like incremental arithmetic above, can use a
        // partial assignment. Existing pending work is always consumed before
        // another matching round is created.
        self.eagerly_instantiate_quantifiers();
        #[cfg(feature = "z3-solver")]
        self.check_partial_arithmetic_trail();
    }

    fn notify_new_decision_level(&mut self) {
        self.stats.decisions += 1;
        if self.stats.decisions % 10_000 == 0 {
            self.print_qi_gc_profile("periodic-decisions");
        }
        debug_println!(
            11,
            0,
            "PROPAGATOR: New decision level {} -> {}",
            self.decision_level,
            self.decision_level + 1
        );
        self.decision_level += 1;
        self.next_is_decision = true;
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
        qi_gc_trace!(
            "backtrack: level {} -> level {}",
            self.decision_level,
            level
        );
        debug_println!(
            23,
            0,
            "PROPAGATOR: Backtracking from level {} to level {}",
            self.decision_level,
            level
        );

        // Undo relevancy marks above this level (structural + class-level)
        self.solver_state.relevancy.backtrack_to(level);

        self.pending_relevant_assignments.clear();
        self.theory_assignment_pending.fill(false);

        // Reset assignments that SAT removed. Theory work performed above the
        // target level is invalidated even when the underlying assignment
        // survives, so it will be re-queued after the egraph backtrack.
        for i in 1..self.assignments.len() {
            if self.assignments[i].abs() > (level + 1) as i32 {
                if self.eager_original_vars.get(i).copied().unwrap_or(false) {
                    self.unassigned_eager_original_vars += 1;
                }
                self.assignments[i] = 0;
                self.theory_processed_levels[i] = None;
            } else if self.theory_processed_levels[i].is_some_and(|p| p > level) {
                self.theory_processed_levels[i] = None;
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
        self.solver_state.propagate_class_relevancy_from_merges();

        #[cfg(feature = "z3-solver")]
        {
            if let Some(z3) = self.z3_incremental.as_mut() {
                z3.notify_backtrack(level);
                z3.drain_merge_queue(self.solver_state);
            }
        }
        self.sync_new_vars();

        let surviving_unprocessed: Vec<i32> = self
            .assignments
            .iter()
            .enumerate()
            .skip(1)
            .filter_map(|(idx, assignment)| {
                (*assignment != 0 && self.theory_processed_levels[idx].is_none()).then_some(
                    if *assignment > 0 {
                        idx as i32
                    } else {
                        -(idx as i32)
                    },
                )
            })
            .collect();
        for lit in surviving_unprocessed {
            self.queue_relevant_assignment(lit);
        }

        // A learned clause containing `¬act` that reaches level zero requests
        // a mandatory transition so its activation-independent consequence can
        // be promoted. Other transitions are resource-threshold driven.
        let root_qi_conflict = level == 0
            && self
                .qi_gc_state
                .as_ref()
                .is_some_and(|gc| !gc.borrow().learned_clauses.is_empty());
        if level == 0 && (self.qi_gc_transition_pending || root_qi_conflict) {
            self.qi_gc_transition_pending = false;
            self.qi_gc_force_backtrack = false;
            if let Some(gc_state) = self.qi_gc_state.clone() {
                self.trigger_epoch_transition(&gc_state);
            }
        }

        debug_println!(16, 0, "Ending backtracking at level {}", level);
        debug_println!(11, 0, "{}", self.solver_state.egraph);
    }

    fn cb_check_found_model(&mut self, model: &[i32]) -> bool {
        self.eager_attempted_since_model = false;
        self.reset_eager_qi_for_level();

        // --trail-out: every model seen here in a non-SAT run is refuted;
        // note any new literals in the atom map and stream the trail line.
        if self.trail_writer.is_some() {
            for &l in model {
                let id = l.unsigned_abs() as i32;
                if let Some(ref gc) = self.qi_gc_state {
                    if gc.borrow().activation_lits.contains(&id) {
                        continue;
                    }
                }
                if !self.trail_atoms.contains_key(&id) {
                    let atom = format!("{}", self.solver_state.get_term_from_lit(id));
                    self.trail_atoms.insert(id, atom);
                }
            }
            self.write_trail_line(model);
        }

        if crate::log::is_important(24) {
            let model_terms: Vec<_> = model
                .iter()
                .filter_map(|x| {
                    if let Some(ref gc) = self.qi_gc_state {
                        if gc.borrow().activation_lits.contains(&x.abs()) {
                            return None;
                        }
                    }
                    Some(self.solver_state.get_term_from_lit(*x))
                })
                .collect();
            debug_println!(
                24,
                0,
                "PROPAGATOR: Checking model: {:?} [{:?}]",
                model,
                model_terms
            );
        }

        self.process_pending_relevant_assignments();
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

        #[cfg(debug_assertions)]
        self.assert_relevant_assignments_processed();

        for term in model {
            // Skip activation literals (current and previous) — they have no term.
            if let Some(ref gc) = self.qi_gc_state {
                if gc.borrow().activation_lits.contains(&term.abs()) {
                    continue;
                }
            }
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

        // Relevance events have already sent every required atom to the
        // incremental backend and shaped the egraph. Flush any post-hoc merges
        // and call check(); the eager backend checks the relevant model.
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
        // Eager rounds use relevant classes as a cheap source of likely useful
        // instances. At a complete-model check, widen to all trigger classes:
        // a filtered round can keep producing a small stream of instances and
        // indefinitely postpone terms that are needed to refute the model.
        if !self.start_quantifier_instantiation_round(
            true,
            false,
            TriggerMatchScope::AllClasses,
            None,
            None,
        ) {
            debug_println!(10, 0, "{}", self.solver_state.egraph);
            assert!(self.disequalities.borrow().is_empty());
            qi_gc_trace!("cb_check_found_model: no new QI instances, returning true (SAT)");
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

        // QI GC: force backtrack to level 0 if scheduled (triggers epoch transition)
        if self.qi_gc_force_backtrack {
            self.qi_gc_force_backtrack = false;
            self.qi_gc_transition_pending = true;
            qi_gc_trace!(
                "force_backtrack(0) from cb_decide at level {}",
                self.decision_level
            );
            unsafe {
                (*self.solver).force_backtrack(0);
            }
            // After force_backtrack, notify_backtrack(0) will fire and trigger
            // epoch transition. CaDiCaL will re-call cb_decide at level 0.
            return 0;
        }

        // QI GC: at level 0, decide the activation literal (becomes level 1)
        if self.decision_level == 0 {
            if let Some(ref gc) = self.qi_gc_state {
                let act = gc.borrow().current_act;
                let idx = act.unsigned_abs() as usize;
                while idx >= self.assignments.len() {
                    self.assignments.resize(self.assignments.len() * 2, 0);
                }
                debug_assert!(
                    self.assignments[idx] == 0,
                    "activation literal must be unassigned at level 0"
                );
                qi_gc_trace!("epoch {}: deciding act={}", gc.borrow().epoch, act);
                return act;
            }
        }

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

        // Serve guarded QI clauses as forgettable.
        if !self.forgettable_queue.is_empty() {
            *is_forgettable = true;
            self.draining_forgettable = true;
            let clause_len = self.forgettable_queue.last().map_or(0, |c| c.len());
            match clause_len {
                0 | 1 => {}
                2 => self.stats.binary_clauses += 1,
                _ => self.stats.clauses += 1,
            }
            return true;
        }

        self.draining_forgettable = false;

        if (*self.disequalities.borrow_mut()).is_empty() {
            false
        } else {
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
        // Serve from the forgettable queue if that's what we're draining
        if self.draining_forgettable {
            assert!(!self.forgettable_queue.is_empty());
            let last_index = self.forgettable_queue.len() - 1;
            let literal = if self.forgettable_queue[last_index].is_empty() {
                self.forgettable_queue.pop();
                0
            } else {
                self.forgettable_queue[last_index].pop().unwrap()
            };
            if literal != 0 {
                self.add_lit_to_proof_tracer(literal);
            }
            return literal;
        }

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
        } else if literal == 0 {
            debug_println!(11, 0, "END OF CLAUSE");
        } else {
            // QI GC activation literal has no term — that's expected.
            debug_assert!(
                self.qi_gc_state.is_some(),
                "non-zero literal {literal} has no term and QI GC is not active"
            );
        }
        debug_println!(4, 0, "{}", self.solver_state.egraph);
        literal
    }
}

#[cfg(test)]
mod qi_gc_tests {
    use super::retire_activation_unit;

    #[test]
    fn retiring_activation_satisfies_negatively_guarded_epoch_clauses() {
        assert_eq!(retire_activation_unit(17), vec![-17]);
    }
}
