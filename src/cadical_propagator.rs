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
use crate::qi_gc::{
    QiCollectibleInstanceGroup, QiGcPlan, QiGcTracker, QiInstantiationKey, QiRetainedInstance,
};
use crate::quantifiers::quantifier::QuantifierInstance::{Instantiation, Skolemization};
use crate::quantifiers::quantifier::{
    PendingInstantiations, TriggerMatchScope, instantiate_quantifiers, materialize_next,
    rematerialize_instantiation,
};
use crate::relevancy::RelevancyTrait;
use crate::solver_state::{SolverState, process_assignment};
use crate::stats::SolverStats;
use crate::utils::{DeterministicHashMap, DeterministicHashSet};
use cadical_sys::{CaDiCal, ExternalPropagator, Learner};
use std::cell::{Cell, RefCell};
use std::collections::{HashSet, VecDeque};
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant};
use yaspar_ir::ast::{ATerm, Repr, TermAllocator};

// --- QI Garbage Collection ---

static QI_GC_TRACE: AtomicBool = AtomicBool::new(false);
static QI_GC_PROFILE: AtomicBool = AtomicBool::new(false);
static QI_GC_PROFILE_PERIODIC: AtomicBool = AtomicBool::new(false);

/// Start eager matching only after CaDiCaL has assigned almost all variables
/// from the original Boolean formula. This keeps QI-created variables from
/// taking over the decision order while still allowing work before final check.
const EAGER_UNASSIGNED_ORIGINAL_LIMIT: usize = 0;

/// Targeted collection is in-place and does not reset the search. Wait for a
/// substantial batch so the clause-arena traversal is amortized.
const QI_GC_MIN_EPOCH_CLAUSES: u64 = 10_000;
const QI_GC_MIN_RECLAIMED_CLAUSES: usize = 2_000;
const QI_GC_MIN_RECLAIMED_TERMS: usize = QI_GC_MIN_RECLAIMED_CLAUSES;
const QI_GC_MIN_RETIRED_SAT_VARS_FOR_REBUILD: usize = QI_GC_MIN_RECLAIMED_TERMS;
/// A proportional collection still has fixed clause-arena and solver-rebuild
/// costs. Require at least a quarter of the normal absolute batch before the
/// garbage/live ratio is allowed to trigger collection.
const QI_GC_MIN_PROPORTIONAL_RECLAIMED_CLAUSES: usize = QI_GC_MIN_RECLAIMED_CLAUSES / 4;
/// Once garbage is at least half the size of the surviving QI source set,
/// rebuilding reduces that set by at least one third. This is the collector's
/// amortization rule; it prevents dead ownership from growing indefinitely
/// just below the absolute batch threshold.
const QI_GC_MAX_LIVE_TO_GARBAGE_RATIO: usize = 2;
const QI_GC_THEORY_KINDS: usize = 7;
const QI_GC_DATATYPE_CLAUSE_ORIGINS: usize = 3;

fn theory_profile_index(theory: Theory) -> usize {
    match theory {
        Theory::QfUf => 0,
        Theory::QfLra => 1,
        Theory::QfLia => 2,
        Theory::QfLira => 3,
        Theory::Datatypes => 4,
        Theory::Boolean => 5,
        Theory::Background => 6,
    }
}

#[derive(Clone, Copy)]
enum TheoryClauseOrigin {
    Other,
    DatatypeAssignment,
    DatatypeOccursCheck,
    DatatypeDeferredTester,
}

impl TheoryClauseOrigin {
    fn datatype_profile_index(self) -> Option<usize> {
        match self {
            Self::Other => None,
            Self::DatatypeAssignment => Some(0),
            Self::DatatypeOccursCheck => Some(1),
            Self::DatatypeDeferredTester => Some(2),
        }
    }
}

pub(crate) fn init_qi_gc_trace() {
    QI_GC_TRACE.store(
        std::env::var("SUNDANCE_QI_GC_TRACE").is_ok(),
        Ordering::Relaxed,
    );
    QI_GC_PROFILE.store(
        std::env::var("SUNDANCE_QI_GC_PROFILE").is_ok(),
        Ordering::Relaxed,
    );
    QI_GC_PROFILE_PERIODIC.store(
        std::env::var("SUNDANCE_QI_GC_PROFILE_PERIODIC").is_ok(),
        Ordering::Relaxed,
    );
}

pub(crate) fn qi_gc_profile_enabled() -> bool {
    QI_GC_PROFILE.load(Ordering::Relaxed)
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
    /// Learned clauses that cannot depend on the current guarded QI
    /// generation (resolution cannot remove `-act` in this encoding).  A SAT
    /// rebuild replays these clauses so collection does not discard search
    /// knowledge unrelated to the retired epoch.
    pub safe_learned_clauses: Vec<Vec<i32>>,
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
    /// Exact QI-clause ancestry for the current epoch.
    pub tracker: QiGcTracker,
    /// Cumulative transition results.
    pub total_retained_qi_clauses: u64,
    pub total_retired_qi_clauses: u64,
    pub total_promoted_derived_clauses: u64,
    pub total_retired_terms: u64,
    pub total_retired_sat_vars: u64,
    /// SAT variables whose Sundance terms have been retired. CaDiCaL only
    /// permits removing the external-propagator observation between solve
    /// calls, so root-level term GC queues them for the maintenance boundary.
    pub pending_unobserve_sat_vars: DeterministicHashSet<i32>,
    pub total_unobserved_sat_vars: u64,
    /// Old guarded QI clauses that still physically exist inside CaDiCaL
    /// after their activation was retired, and the number later deleted by
    /// ordinary SAT clause-database reduction.
    pub pending_retired_qi_clause_ids: HashSet<u64>,
    pub pending_retired_qi_clause_contents: DeterministicHashMap<Vec<i32>, usize>,
    /// Complete instance groups represented by the pending clause IDs.
    pub pending_retired_qi_group_ids: DeterministicHashSet<u64>,
    pub total_physically_collected_qi_clauses: u64,
    pub total_physically_collected_qi_clause_ids: u64,
    pub total_physically_collected_qi_clause_contents: u64,
    /// Forgettable theory lemmas requested alongside a QI collection because
    /// they pin terms owned by the retiring epoch.
    pub pending_requested_theory_clause_ids: HashSet<u64>,
    pub total_requested_theory_clauses: u64,
    pub total_physically_collected_theory_clauses: u64,
    pub total_reclaimed_qi_instances: u64,
    pub total_permanently_satisfied_qi_instances: u64,
    /// Legacy physically absent instances that still retain old clause
    /// obligations for direct model evaluation.
    pub retired_qi_instances: Vec<QiRetainedInstance>,
    /// Fully compacted instances represented only by quantifier/substitution.
    /// Their duplicate-suppression keys remain live during ordinary search.
    /// Complete-model matching temporarily releases them and reactivates only
    /// substitutions whose triggers still match.
    pub compact_qi_obligations: HashSet<QiInstantiationKey>,
    pub total_resurrected_qi_instances: u64,
    /// Restored substitutions that complete-model checking proved must stay
    /// materialized for the remainder of the current collection epoch.
    pub total_gc_protected_qi_instances: u64,
    /// Activation literals retired by permanent `-act` units.  Tracking the
    /// first root assignment and every deleted clause that still contains a
    /// retired activation distinguishes delayed SAT collection from stale
    /// clause-ID bookkeeping.
    pub retired_activations: HashSet<i32>,
    pub observed_retirement_units: HashSet<i32>,
    pub total_deleted_retired_activation_clauses: u64,
    /// Wall-clock accounting for a collection requested inside CaDiCaL's
    /// active CDCL loop.
    pub in_search_collection_started: Option<Instant>,
    pub in_search_collection_expected_qi_clauses: usize,
    /// Epoch-owned terms are currently eligible for e-graph retirement.
    /// Source-clause collection can expose more terms, but pure Boolean
    /// structure may already be collectible while its SAT clauses remain.
    /// E-graph retirement is performed only at a natural level-zero backtrack.
    pub targeted_term_gc_pending: bool,
    /// Predecessor compaction is folded into actual term collection at an
    /// existing level-zero safepoint; these counters measure its effect.
    pub total_predecessor_compactions: u64,
    pub total_predecessor_entries_removed: u64,
    /// A completed matching round added enough guarded clauses that the next
    /// safe SAT decision callback should evaluate an exact collection plan.
    pub collection_check_pending: bool,
    /// Per-epoch theory-clause ownership diagnostics, indexed as
    /// QfUf/QfLra/QfLia/QfLira/Datatypes/Boolean/Background.
    pub theory_clauses_by_kind: [u64; QI_GC_THEORY_KINDS],
    pub theory_clauses_touching_epoch_terms_by_kind: [u64; QI_GC_THEORY_KINDS],
    pub newly_pinned_epoch_term_references_by_kind: [u64; QI_GC_THEORY_KINDS],
    pub theory_unit_clauses_by_kind: [u64; QI_GC_THEORY_KINDS],
    pub theory_unit_clauses_touching_epoch_terms_by_kind: [u64; QI_GC_THEORY_KINDS],
    pub newly_pinned_epoch_term_references_from_units_by_kind: [u64; QI_GC_THEORY_KINDS],
    pub theory_empty_clauses_by_kind: [u64; QI_GC_THEORY_KINDS],
    /// Datatype theory-clause diagnostics, indexed as
    /// assignment/occurs-check/deferred-tester.
    pub datatype_clauses_by_origin: [u64; QI_GC_DATATYPE_CLAUSE_ORIGINS],
    pub datatype_units_by_origin: [u64; QI_GC_DATATYPE_CLAUSE_ORIGINS],
    pub datatype_epoch_units_by_origin: [u64; QI_GC_DATATYPE_CLAUSE_ORIGINS],
    pub deduplicated_theory_units_by_kind: [u64; QI_GC_THEORY_KINDS],
    pub deduplicated_datatype_units_by_origin: [u64; QI_GC_DATATYPE_CLAUSE_ORIGINS],
    pub datatype_unit_literals: HashSet<i32>,
    pub datatype_epoch_unit_literals: HashSet<i32>,
    /// Learned-clause term closure held only while a fresh SAT replay is being
    /// constructed. Surviving clauses receive fresh clause-ID ownership;
    /// absent clauses release these pins before solving resumes.
    pub rebuild_learned_term_uids: DeterministicHashSet<u64>,
}

#[derive(Debug, Clone, Copy)]
struct QiGcCollectionAnalysis {
    observed_qi: usize,
    support_qi: usize,
    retained_qi: usize,
    promoted_derived: usize,
    collectible_instances: usize,
    collectible_qi: usize,
    root_satisfied_instances: usize,
    root_satisfied_qi: usize,
    collectible_theory: usize,
    reclaimable_qi: usize,
    epoch_owned_terms: usize,
    candidate_terms: usize,
    term_analysis_skipped: bool,
    worthwhile: bool,
    term_gc_worthwhile: bool,
    trigger: QiGcCollectionTrigger,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum QiGcCollectionTrigger {
    EpochTooSmall,
    BatchTooSmall,
    AbsoluteBatch,
    GarbageToLiveRatio,
}

fn retire_activation_unit(activation: i32) -> Vec<i32> {
    vec![-activation]
}

fn normalize_clause(clause: &[i32]) -> Vec<i32> {
    let mut normalized = clause.to_vec();
    normalized.sort_unstable();
    normalized.dedup();
    normalized
}

fn deduplicate_clauses(clauses: impl IntoIterator<Item = Vec<i32>>) -> Vec<Vec<i32>> {
    let mut seen = HashSet::new();
    clauses
        .into_iter()
        .filter(|clause| seen.insert(normalize_clause(clause)))
        .collect()
}

fn remove_clause_multiset(target: &mut Vec<Vec<i32>>, removed: &[Vec<i32>]) -> usize {
    let mut counts = DeterministicHashMap::<Vec<i32>, usize>::default();
    for clause in removed {
        let mut normalized = clause.clone();
        normalized.sort_unstable();
        normalized.dedup();
        *counts.entry(normalized).or_default() += 1;
    }
    let before = target.len();
    target.retain(|clause| {
        let mut normalized = clause.clone();
        normalized.sort_unstable();
        normalized.dedup();
        let Some(count) = counts.get_mut(&normalized) else {
            return true;
        };
        if *count == 0 {
            return true;
        }
        *count -= 1;
        false
    });
    before - target.len()
}

fn clause_is_satisfied_by_model(clause: &[i32], model_values: &[i8]) -> bool {
    clause.iter().any(|lit| {
        model_values
            .get(lit.unsigned_abs() as usize)
            .is_some_and(|value| *value != 0 && (*value > 0) == (*lit > 0))
    })
}

fn root_assignment_falsifies(assignments: &[i32], lit: i32) -> bool {
    let assignment = assignments
        .get(lit.unsigned_abs() as usize)
        .copied()
        .unwrap_or(0);
    assignment.abs() == 1 && (assignment > 0) != (lit > 0)
}

fn root_assignment_satisfies(assignments: &[i32], lit: i32) -> bool {
    let assignment = assignments
        .get(lit.unsigned_abs() as usize)
        .copied()
        .unwrap_or(0);
    assignment.abs() == 1 && (assignment > 0) == (lit > 0)
}

fn clause_is_satisfied_at_root(assignments: &[i32], clause: &[i32]) -> bool {
    clause
        .iter()
        .any(|lit| root_assignment_satisfies(assignments, *lit))
}

fn instance_group_is_satisfied_at_root(
    assignments: &[i32],
    group: &QiCollectibleInstanceGroup,
) -> bool {
    group
        .clauses
        .iter()
        .all(|(_, clause)| clause_is_satisfied_at_root(assignments, clause))
}

fn activation_consequence_is_false_at_root(
    assignments: &[i32],
    clause: &[i32],
    activation: i32,
) -> bool {
    clause
        .iter()
        .copied()
        .filter(|lit| *lit != -activation)
        .all(|lit| root_assignment_falsifies(assignments, lit))
}

fn qi_gc_collection_trigger(
    epoch_clauses: u64,
    observed_qi: usize,
    collectible_qi: usize,
) -> QiGcCollectionTrigger {
    if epoch_clauses < QI_GC_MIN_EPOCH_CLAUSES {
        return QiGcCollectionTrigger::EpochTooSmall;
    }
    if collectible_qi >= QI_GC_MIN_RECLAIMED_CLAUSES {
        return QiGcCollectionTrigger::AbsoluteBatch;
    }
    if collectible_qi < QI_GC_MIN_PROPORTIONAL_RECLAIMED_CLAUSES {
        return QiGcCollectionTrigger::BatchTooSmall;
    }

    let live_qi = observed_qi.saturating_sub(collectible_qi);
    if collectible_qi.saturating_mul(QI_GC_MAX_LIVE_TO_GARBAGE_RATIO) >= live_qi {
        QiGcCollectionTrigger::GarbageToLiveRatio
    } else {
        QiGcCollectionTrigger::BatchTooSmall
    }
}

fn qi_gc_term_reduction_is_worthwhile(epoch_clauses: u64, candidate_terms: usize) -> bool {
    epoch_clauses >= QI_GC_MIN_EPOCH_CLAUSES && candidate_terms >= QI_GC_MIN_RECLAIMED_TERMS
}

fn qi_gc_pinned_term_uids(gc: &QiGcState, solver_state: &SolverState) -> DeterministicHashSet<u64> {
    let mut pinned = gc.tracker.permanent_term_uids();
    pinned.extend(gc.tracker.gc_protected_term_uids());
    let live_source_clauses: Vec<Vec<i32>> = gc
        .tracker
        .live_qi_clauses()
        .into_iter()
        .map(|(_, clause)| clause)
        .collect();
    solver_state.collect_clause_theory_term_closure(&live_source_clauses, &mut pinned);
    solver_state
        .collect_clause_theory_term_closure(&gc.tracker.live_derived_clauses(), &mut pinned);
    for instance in gc
        .retired_qi_instances
        .iter()
        .filter(|instance| !instance.clauses.is_empty())
    {
        solver_state.collect_clause_theory_term_closure(&instance.clauses, &mut pinned);
    }
    for term in gc.tracker.live_substitution_terms().into_iter().chain(
        gc.retired_qi_instances
            .iter()
            .filter(|instance| !instance.clauses.is_empty())
            .flat_map(|instance| instance.key.substitution.values().cloned()),
    ) {
        solver_state.collect_registered_term_closure(&term, &mut pinned);
    }
    solver_state.collect_quantifier_term_closure(&mut pinned);
    pinned.extend(gc.rebuild_learned_term_uids.iter().copied());
    pinned
}

fn qi_gc_collection_analysis(
    gc: &QiGcState,
    solver_state: &SolverState,
    collectible_instances: usize,
    collectible_qi: usize,
    root_satisfied_instances: usize,
    root_satisfied_qi: usize,
    collectible_theory: usize,
    allow_term_analysis: bool,
) -> QiGcCollectionAnalysis {
    let analysis_started = Instant::now();
    let summary_started = Instant::now();
    let observed_qi = gc.tracker.observed_qi_clause_count();
    let support_qi = if QI_GC_PROFILE.load(Ordering::Relaxed) {
        gc.tracker.retained_qi_clause_count()
    } else {
        0
    };
    let promoted_derived = gc.tracker.live_derived_clause_count();
    let epoch_owned_terms = gc.tracker.epoch_owned_term_count();
    let summary_duration = summary_started.elapsed();
    let retained_qi = observed_qi.saturating_sub(collectible_qi);
    let (candidate_terms, pinning_duration, candidate_duration) = if allow_term_analysis {
        let pinning_started = Instant::now();
        let transition_pinned_terms = qi_gc_pinned_term_uids(gc, solver_state);
        let pinning_duration = pinning_started.elapsed();
        let candidate_started = Instant::now();
        let candidate_terms = gc
            .tracker
            .unpinned_epoch_owned_term_count(&transition_pinned_terms);
        (
            candidate_terms,
            pinning_duration,
            candidate_started.elapsed(),
        )
    } else {
        (0, Duration::ZERO, Duration::ZERO)
    };
    let trigger = qi_gc_collection_trigger(gc.epoch_guarded_clauses, observed_qi, collectible_qi);
    let analysis = QiGcCollectionAnalysis {
        observed_qi,
        support_qi,
        retained_qi,
        promoted_derived,
        collectible_instances,
        collectible_qi,
        root_satisfied_instances,
        root_satisfied_qi,
        collectible_theory,
        reclaimable_qi: collectible_qi,
        epoch_owned_terms,
        candidate_terms,
        term_analysis_skipped: !allow_term_analysis,
        worthwhile: matches!(
            trigger,
            QiGcCollectionTrigger::AbsoluteBatch | QiGcCollectionTrigger::GarbageToLiveRatio
        ),
        term_gc_worthwhile: allow_term_analysis
            && qi_gc_term_reduction_is_worthwhile(gc.epoch_guarded_clauses, candidate_terms),
        trigger,
    };
    if QI_GC_PROFILE.load(Ordering::Relaxed) {
        eprintln!(
            "[qi-gc-profile] collection-analysis-timing summary_duration={:.6}s \
             pinning_duration={:.6}s candidate_duration={:.6}s \
             term_analysis_skipped={} total_duration={:.6}s",
            summary_duration.as_secs_f64(),
            pinning_duration.as_secs_f64(),
            candidate_duration.as_secs_f64(),
            !allow_term_analysis,
            analysis_started.elapsed().as_secs_f64(),
        );
    }
    analysis
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
            } else if !state.learner_buf.is_empty() {
                let clause = state.learner_buf.clone();
                state.safe_learned_clauses.push(clause);
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

#[derive(Debug)]
pub(crate) struct QueuedExternalClause {
    literals: Vec<i32>,
    forgettable: bool,
    tracked_terms: Option<DeterministicHashSet<u64>>,
    ownership_registered: bool,
}

impl QueuedExternalClause {
    fn untracked(literals: Vec<i32>) -> Self {
        Self {
            literals,
            forgettable: false,
            tracked_terms: None,
            ownership_registered: false,
        }
    }

    fn theory(
        literals: Vec<i32>,
        forgettable: bool,
        tracked_terms: Option<DeterministicHashSet<u64>>,
    ) -> Self {
        Self {
            literals,
            forgettable,
            tracked_terms,
            ownership_registered: false,
        }
    }
}

/// Our implementation of a Cadical Propagator
pub struct CustomExternalPropagator<'a> {
    pub decision_level: usize,
    pub solver_state: &'a mut SolverState,
    pub disequalities: RefCell<Vec<QueuedExternalClause>>, // might be paying a bit of overhead for RefCell
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
    /// Once a theory unit has been queued, re-emitting it after backtracking
    /// cannot strengthen the current SAT solver. Keep the first proof step
    /// and avoid repeated clause and ownership processing.
    pub queued_theory_unit_literals: RefCell<HashSet<i32>>,
    /// Separate queue for forgettable QI clauses (served with is_forgettable=true).
    pub forgettable_queue: Vec<Vec<i32>>,
    /// Complete current-epoch clauses, retained after the callback queue has
    /// destructively drained them. A fresh CaDiCaL instance replays exactly
    /// this set after dropping the old redundant clause database.
    pub active_forgettable_clauses: Vec<Vec<i32>>,
    /// Short activation-independent learned clauses replayed only across the
    /// current rebuild. They are intentionally generational: the next solver
    /// exports a fresh useful subset rather than accumulating them forever.
    pub rebuild_learned_clauses: Vec<Vec<i32>>,
    pub rebuild_learned_clause_terms: DeterministicHashMap<Vec<i32>, DeterministicHashSet<u64>>,
    /// Whether the clause currently being drained via cb_add_external_clause_lit is forgettable.
    pub draining_forgettable: bool,
    /// Track whether the next notify_assignment is a decision literal.
    pub next_is_decision: bool,
    /// Flag: next cb_decide should force_backtrack(0) to trigger epoch transition.
    pub qi_gc_force_backtrack: bool,
    /// A root backtrack should perform exactly one requested epoch transition.
    /// Ordinary CaDiCaL backtracks to level zero do not collect QI state.
    pub qi_gc_transition_pending: bool,
    /// Shared stop request consumed by the outer solve loop. The transition is
    /// completed inside callbacks, then CaDiCaL is replaced between solve calls.
    pub qi_gc_rebuild_requested: Option<Rc<Cell<bool>>>,
    /// The outer CDCL loop is currently replacing CaDiCaL. Its explicit
    /// Sundance backtrack must not start another collection or retire more SAT
    /// variables after the rebuild snapshot has already been taken.
    pub qi_gc_maintenance_in_progress: bool,
    /// Root assignments hardened into a rebuilt solver. Their theory effects
    /// already exist at level zero and must not be applied a second time if
    /// the fresh solver reports one of these fixed assignments. CaDiCaL does
    /// not promise callbacks for units added before solving, so this is
    /// duplicate suppression rather than a replay-completion protocol.
    pub qi_gc_preserved_root_assignments: Vec<i8>,
    /// Last polarity CaDiCaL assigned to each external variable. CaDiCaL's
    /// public `copy` operation preserves clauses and preprocessing flags but
    /// not phase-saving state, so a physical rebuild replays these hints.
    pub qi_gc_phase_hints: Vec<i8>,
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

#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct ReplayedLearnedOwnershipProfile {
    pub(crate) candidate_clause_shapes: usize,
    pub(crate) replayed_clause_shapes: usize,
    pub(crate) dropped_clause_shapes: usize,
    pub(crate) replayed_term_uids: usize,
}

impl<'a> CustomExternalPropagator<'a> {
    fn print_qi_gc_profile(&self, event: &str) {
        if !QI_GC_PROFILE.load(Ordering::Relaxed) {
            return;
        }
        if event == "periodic-decisions" && !QI_GC_PROFILE_PERIODIC.load(Ordering::Relaxed) {
            return;
        }

        let egraph = self.solver_state.egraph.gc_profile();
        let relevance = self.solver_state.relevancy.profile();
        let (
            pending_released_instantiations,
            released_instantiation_events,
            rediscovered_instantiation_events,
        ) = self.solver_state.qi_gc_instantiation_churn_profile();
        let assigned = self
            .assignments
            .iter()
            .skip(1)
            .filter(|lit| **lit != 0)
            .count();
        let (
            epoch,
            transitions,
            epoch_instances,
            total_instances,
            epoch_clauses,
            total_clauses,
            retained_qi,
            retired_qi,
            promoted_derived,
            retired_terms,
            retired_sat_vars,
            pending_unobserve_sat_vars,
            total_unobserved_sat_vars,
            pending_sat_gc,
            pending_sat_gc_contents,
            physically_collected_qi,
            physically_collected_qi_ids,
            physically_collected_qi_contents,
            retired_activations,
            observed_retirement_units,
            deleted_retired_activation_clauses,
            tracked_qi,
            ancestry_nodes,
            ancestry_edges,
            live_derived,
            instance_groups,
            permanent_terms,
        ) = self.qi_gc_state.as_ref().map_or(
            (
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ),
            |gc| {
                let gc = gc.borrow();
                let tracker = gc.tracker.profile();
                (
                    gc.epoch,
                    gc.transitions,
                    gc.epoch_instantiations,
                    gc.total_epoch_instantiations,
                    gc.epoch_guarded_clauses,
                    gc.total_guarded_clauses,
                    gc.total_retained_qi_clauses,
                    gc.total_retired_qi_clauses,
                    gc.total_promoted_derived_clauses,
                    gc.total_retired_terms,
                    gc.total_retired_sat_vars,
                    gc.pending_unobserve_sat_vars.len(),
                    gc.total_unobserved_sat_vars,
                    gc.pending_retired_qi_clause_ids.len(),
                    gc.pending_retired_qi_clause_contents
                        .values()
                        .sum::<usize>(),
                    gc.total_physically_collected_qi_clauses,
                    gc.total_physically_collected_qi_clause_ids,
                    gc.total_physically_collected_qi_clause_contents,
                    gc.retired_activations.len(),
                    gc.observed_retirement_units.len(),
                    gc.total_deleted_retired_activation_clauses,
                    tracker.qi_clauses,
                    tracker.antecedent_nodes,
                    tracker.antecedent_edges,
                    tracker.live_derived,
                    tracker.instance_groups,
                    tracker.permanent_term_uids,
                )
            },
        );

        eprintln!(
            "[qi-gc-profile] event={event} elapsed={:.3}s level={} assigned={} \
             decisions={} backtracks={} conflicts={} arith_checks={} \
             quantifiers={} \
             epoch={} transitions={} epoch_instances={} total_instances={} \
             epoch_clauses={} total_clauses={} retained_qi={} retired_qi={} \
             promoted_derived={} retired_terms={} retired_sat_vars={} \
             tracked_qi={} pending_unobserve_sat_vars={} \
             total_unobserved_sat_vars={} \
             pending_sat_gc_ids={} pending_sat_gc_contents={} \
             physically_collected_qi={} physically_collected_qi_ids={} \
             physically_collected_qi_contents={} retired_activations={} \
             observed_retirement_units={} deleted_retired_activation_clauses={} \
             ancestry_nodes={} ancestry_edges={} \
             live_derived={} instance_groups={} permanent_terms={} \
             pending_released_instantiations={} released_instantiation_events={} \
             rediscovered_instantiation_events={} \
             qi_rounds={} pending_qi={}",
            self.stats.elapsed().as_secs_f64(),
            self.decision_level,
            assigned,
            self.stats.decisions,
            self.stats.backtracks,
            self.stats.conflicts,
            self.stats.arith_checks,
            self.solver_state.quantifiers.len(),
            epoch,
            transitions,
            epoch_instances,
            total_instances,
            epoch_clauses,
            total_clauses,
            retained_qi,
            retired_qi,
            promoted_derived,
            retired_terms,
            retired_sat_vars,
            tracked_qi,
            pending_unobserve_sat_vars,
            total_unobserved_sat_vars,
            pending_sat_gc,
            pending_sat_gc_contents,
            physically_collected_qi,
            physically_collected_qi_ids,
            physically_collected_qi_contents,
            retired_activations,
            observed_retirement_units,
            deleted_retired_activation_clauses,
            ancestry_nodes,
            ancestry_edges,
            live_derived,
            instance_groups,
            permanent_terms,
            pending_released_instantiations,
            released_instantiation_events,
            rediscovered_instantiation_events,
            self.stats.instantiation_rounds,
            self.pending.is_some(),
        );
        eprintln!(
            "[qi-gc-profile] egraph terms={} reusable_ids={} retired_terms={} reused_term_ids={} \
             function_entries={} relevant_entries={} \
             active_relevant_terms={} predecessors={} predecessor_trail={} qi_predecessors={} \
             union_terms={} signatures={} signature_trail={} backtrack_entries={} merges={} \
             predecessor_gc_runs={} predecessor_gc_removed={} predecessor_gc_restored={} match_calls={} \
             match_candidates={} relevant_match_candidates={} match_results={}",
            egraph.registered_terms,
            egraph.reusable_ids,
            egraph.retired_terms,
            egraph.reused_term_ids,
            egraph.function_entries,
            egraph.relevant_function_entries,
            egraph.active_relevant_terms,
            egraph.predecessor_entries,
            egraph.predecessor_trail_entries,
            egraph.qi_predecessor_entries,
            egraph.union_to_eclass_entries,
            egraph.signature_entries,
            egraph.signature_trail_entries,
            egraph.backtrack_entries,
            egraph.merges,
            egraph.predecessor_gc_runs,
            egraph.predecessor_gc_removed,
            egraph.predecessor_gc_restored,
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
        if let Some(gc) = &self.qi_gc_state {
            let gc = gc.borrow();
            let tracker = gc.tracker.profile();
            eprintln!(
                "[qi-gc-profile] permanent-clause-ownership pending_clauses={} \
                 live_clauses={} live_forgettable_theory_clauses={} \
                 clause_pinned_terms={} pending_requested_theory={} \
                 total_requested_theory={} physically_collected_theory={} \
                 permanently_satisfied_instances={} gc_protected_instances={} \
                 total_gc_protected_instances={}",
                tracker.pending_permanent_clauses,
                tracker.live_permanent_clauses,
                tracker.live_forgettable_theory_clauses,
                tracker.clause_pinned_term_uids,
                gc.pending_requested_theory_clause_ids.len(),
                gc.total_requested_theory_clauses,
                gc.total_physically_collected_theory_clauses,
                gc.total_permanently_satisfied_qi_instances,
                tracker.gc_protected_instances,
                gc.total_gc_protected_qi_instances,
            );
            eprintln!(
                "[qi-gc-profile] predecessor-gc total_compactions={} \
                 total_entries_removed={}",
                gc.total_predecessor_compactions, gc.total_predecessor_entries_removed,
            );
            eprintln!(
                "[qi-gc-profile] theory-clause-ownership \
                 clauses={:?} touching_epoch_terms={:?} \
                 newly_pinned_epoch_term_references={:?} units={:?} \
                 units_touching_epoch_terms={:?} \
                 newly_pinned_epoch_term_references_from_units={:?} empty={:?}",
                gc.theory_clauses_by_kind,
                gc.theory_clauses_touching_epoch_terms_by_kind,
                gc.newly_pinned_epoch_term_references_by_kind,
                gc.theory_unit_clauses_by_kind,
                gc.theory_unit_clauses_touching_epoch_terms_by_kind,
                gc.newly_pinned_epoch_term_references_from_units_by_kind,
                gc.theory_empty_clauses_by_kind,
            );
            let mut datatype_uninitialized = 0usize;
            let mut datatype_valid_constructors = 0usize;
            let mut datatype_stale_constructors = 0usize;
            let mut datatype_epoch_entries = 0usize;
            for (uid, constructor) in &self.solver_state.term_constructors {
                if gc.tracker.is_epoch_owned_term(*uid) {
                    datatype_epoch_entries += 1;
                }
                match constructor {
                    crate::solver_types::ConstructorType::Uninitialized => {
                        datatype_uninitialized += 1;
                    }
                    crate::solver_types::ConstructorType::Constructor { hash, level, .. } => {
                        if self.solver_state.is_valid_hash(*hash, *level) {
                            datatype_valid_constructors += 1;
                        } else {
                            datatype_stale_constructors += 1;
                        }
                    }
                }
            }
            eprintln!(
                "[qi-gc-profile] datatype-gc clauses_by_origin={:?} \
                 units_by_origin={:?} epoch_units_by_origin={:?} \
                 deduplicated_units_by_theory={:?} \
                 deduplicated_datatype_units_by_origin={:?} \
                 unique_unit_literals={} repeated_unit_emissions={} \
                 unique_epoch_unit_literals={} epoch_entries={} \
                 constructors_total={} uninitialized={} valid={} stale={} dt_splits={}",
                gc.datatype_clauses_by_origin,
                gc.datatype_units_by_origin,
                gc.datatype_epoch_units_by_origin,
                gc.deduplicated_theory_units_by_kind,
                gc.deduplicated_datatype_units_by_origin,
                gc.datatype_unit_literals.len(),
                gc.theory_unit_clauses_by_kind[theory_profile_index(Theory::Datatypes) as usize]
                    .saturating_sub(gc.datatype_unit_literals.len() as u64),
                gc.datatype_epoch_unit_literals.len(),
                datatype_epoch_entries,
                self.solver_state.term_constructors.len(),
                datatype_uninitialized,
                datatype_valid_constructors,
                datatype_stale_constructors,
                self.solver_state.stat_dt_splits,
            );
        }

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
        if self.solver_state.is_retired_sat_var(lit) {
            return;
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
        self.disequalities
            .borrow_mut()
            .push(QueuedExternalClause::untracked(clause));
    }

    fn queue_theory_clause(&self, clause: Vec<i32>, theory: Theory) {
        self.queue_theory_clause_with_origin(clause, theory, TheoryClauseOrigin::Other);
    }

    fn queue_theory_clause_with_origin(
        &self,
        clause: Vec<i32>,
        theory: Theory,
        origin: TheoryClauseOrigin,
    ) {
        if clause.len() == 1
            && !self
                .queued_theory_unit_literals
                .borrow_mut()
                .insert(clause[0])
        {
            if let Some(gc) = &self.qi_gc_state {
                let mut gc = gc.borrow_mut();
                gc.deduplicated_theory_units_by_kind[theory_profile_index(theory)] += 1;
                if let Some(origin) = origin.datatype_profile_index() {
                    gc.deduplicated_datatype_units_by_origin[origin] += 1;
                }
            }
            return;
        }

        let mut pinned = DeterministicHashSet::default();
        self.solver_state
            .collect_clause_term_closure(std::slice::from_ref(&clause), &mut pinned);
        let forgettable = self.qi_gc_state.is_some() && clause.len() >= 2;
        if let Some(gc) = &self.qi_gc_state {
            let mut gc = gc.borrow_mut();
            let kind = theory_profile_index(theory);
            let epoch_references = gc.tracker.count_epoch_owned_terms(&pinned);
            let new_epoch_pins = gc.tracker.count_collectible_epoch_terms(&pinned);
            gc.theory_clauses_by_kind[kind] += 1;
            if epoch_references != 0 {
                gc.theory_clauses_touching_epoch_terms_by_kind[kind] += 1;
                gc.newly_pinned_epoch_term_references_by_kind[kind] += new_epoch_pins as u64;
            }
            if let Some(origin) = origin.datatype_profile_index() {
                gc.datatype_clauses_by_origin[origin] += 1;
            }
            match clause.len() {
                0 => gc.theory_empty_clauses_by_kind[kind] += 1,
                1 => {
                    gc.theory_unit_clauses_by_kind[kind] += 1;
                    if theory == Theory::Datatypes {
                        gc.datatype_unit_literals.insert(clause[0]);
                    }
                    if let Some(origin) = origin.datatype_profile_index() {
                        gc.datatype_units_by_origin[origin] += 1;
                    }
                    if epoch_references != 0 {
                        gc.theory_unit_clauses_touching_epoch_terms_by_kind[kind] += 1;
                        gc.newly_pinned_epoch_term_references_from_units_by_kind[kind] +=
                            new_epoch_pins as u64;
                        if theory == Theory::Datatypes {
                            gc.datatype_epoch_unit_literals.insert(clause[0]);
                        }
                        if let Some(origin) = origin.datatype_profile_index() {
                            gc.datatype_epoch_units_by_origin[origin] += 1;
                        }
                    }
                }
                _ => {}
            }
        }
        self.proof_tracer
            .borrow_mut()
            .add_theory_clause(&clause, theory);
        self.proof_tracer
            .borrow_mut()
            .register_clause_for_cadical_callback(&clause);
        self.disequalities
            .borrow_mut()
            .push(QueuedExternalClause::theory(
                clause,
                forgettable,
                Some(pinned),
            ));
    }

    pub fn sync_external_stats(&mut self) {
        self.stats.egraph_merges = self.solver_state.egraph.stats.merges;
        self.stats.bool_vars = (self.solver_state.cnf_cache.next_var - 1) as u64;
        self.stats.deleted_clauses = self.proof_tracer.borrow().deleted_clauses;
        self.stats.dt_accessor_ax = self.solver_state.stat_dt_accessor_ax;
        self.stats.dt_constructor_ax = self.solver_state.stat_dt_constructor_ax;
        self.stats.dt_splits = self.solver_state.stat_dt_splits;
    }

    /// Prepare the propagator for replacement of the SAT solver. Every
    /// current root assignment is a sound consequence of the old level-zero
    /// clause database, so harden it as a unit in the new solver. Activation
    /// literals have no theory meaning and are intentionally omitted.
    pub fn prepare_for_solver_rebuild(&mut self) -> Vec<i32> {
        // CaDiCaL checks its terminator periodically, so it can enter a few
        // decision levels after the transition requested a stop. The old SAT
        // solver is about to be discarded; explicitly return every Sundance
        // theory component to the root before snapshotting the replay units.
        if self.decision_level != 0 {
            if QI_GC_PROFILE.load(Ordering::Relaxed) {
                eprintln!(
                    "[qi-gc-profile] sat-rebuild-backtrack from_level={}",
                    self.decision_level
                );
            }
            ExternalPropagator::notify_backtrack(self, 0);
        }
        debug_assert_eq!(self.decision_level, 0);

        let activation_lits = self
            .qi_gc_state
            .as_ref()
            .map(|gc| gc.borrow().activation_lits.clone())
            .unwrap_or_default();
        self.qi_gc_preserved_root_assignments.clear();
        self.qi_gc_preserved_root_assignments
            .resize(self.assignments.len(), 0);

        let mut root_units = Vec::new();
        for idx in 1..self.assignments.len() {
            if activation_lits.contains(&(idx as i32)) {
                self.assignments[idx] = 0;
                self.theory_processed_levels[idx] = None;
                self.theory_assignment_pending[idx] = false;
                continue;
            }
            let assignment = self.assignments[idx];
            if assignment.abs() != 1
                || (self.solver_state.is_retired_sat_var(idx as i32)
                    && !self.solver_state.is_retired_sat_only_var(idx as i32))
            {
                continue;
            }
            let sign = assignment.signum() as i8;
            self.qi_gc_preserved_root_assignments[idx] = sign;
            root_units.push(if sign > 0 { idx as i32 } else { -(idx as i32) });
        }

        self.pending_relevant_assignments.clear();
        self.theory_assignment_pending.fill(false);
        if let Some(gc_state) = self.qi_gc_state.clone() {
            let current_act = gc_state.borrow().current_act;
            assert_eq!(
                current_act, 0,
                "selective SAT rebuild currently requires targeted unguarded QI collection"
            );
            let retired_sat_vars = gc_state.borrow().pending_unobserve_sat_vars.clone();
            let nonreplayable_retired_sat_vars: DeterministicHashSet<i32> = retired_sat_vars
                .iter()
                .copied()
                .filter(|var| !self.solver_state.is_retired_sat_only_var(*var))
                .collect();
            let mut rebuild = gc_state
                .borrow_mut()
                .tracker
                .prepare_for_solver_rebuild(&self.assignments, &nonreplayable_retired_sat_vars);
            assert!(
                rebuild.source_clauses.iter().all(|clause| clause
                    .iter()
                    .all(|lit| !self.solver_state.is_retired_sat_var(*lit)
                        || self.solver_state.is_retired_sat_only_var(*lit))),
                "live QI source clause references a retired theory SAT variable during rebuild"
            );
            let replay_source_sat_only_literals = rebuild
                .source_clauses
                .iter()
                .flatten()
                .filter(|lit| self.solver_state.is_retired_sat_only_var(**lit))
                .count();
            let learned_clauses_before = rebuild.learned_clauses.len();
            rebuild.learned_clauses.retain(|clause| {
                clause
                    .iter()
                    .all(|lit| !self.solver_state.is_retired_sat_var(*lit))
            });
            let dropped_learned_clauses =
                learned_clauses_before.saturating_sub(rebuild.learned_clauses.len());

            let root_satisfied_compact_instances = rebuild.root_satisfied_instances.len();
            gc_state
                .borrow_mut()
                .compact_qi_obligations
                .extend(std::mem::take(&mut rebuild.root_satisfied_instances));
            let retired_source_instances = rebuild.retired_instances.len();
            let released_source_instance_keys = rebuild
                .retired_instances
                .iter()
                .filter(|instance| {
                    self.solver_state.forget_added_instantiation(
                        instance.key.quantifier_id,
                        &instance.key.substitution,
                    )
                })
                .count();
            {
                let mut gc = gc_state.borrow_mut();
                gc.total_reclaimed_qi_instances += retired_source_instances as u64;
            }
            self.rebuild_learned_clause_terms.clear();
            let mut learned_term_uids = DeterministicHashSet::default();
            for clause in &rebuild.learned_clauses {
                let mut clause_terms = DeterministicHashSet::default();
                self.solver_state.collect_clause_theory_term_closure(
                    std::slice::from_ref(clause),
                    &mut clause_terms,
                );
                learned_term_uids.extend(clause_terms.iter().copied());
                self.rebuild_learned_clause_terms
                    .entry(normalize_clause(clause))
                    .or_default()
                    .extend(clause_terms);
            }
            gc_state.borrow_mut().rebuild_learned_term_uids = learned_term_uids.clone();

            self.active_forgettable_clauses = rebuild.source_clauses;
            self.rebuild_learned_clauses = deduplicate_clauses(rebuild.learned_clauses);
            self.forgettable_queue = self.active_forgettable_clauses.clone();
            {
                let mut tracer = self.proof_tracer.borrow_mut();
                for clause in &self.forgettable_queue {
                    tracer.register_clause_for_cadical_callback(clause);
                }
            }
            if QI_GC_PROFILE.load(Ordering::Relaxed) {
                eprintln!(
                    "[qi-gc-profile] sat-rebuild-prepare source_clauses_before={} \
                     replay_source_clauses={} root_satisfied_source_clauses={} \
                     root_satisfied_instance_groups={} \
                     root_satisfied_compact_instances={} replay_learned_clauses={} \
                     dropped_learned_clauses={} \
                     retired_source_instances={} released_source_instance_keys={} \
                     retired_instance_source_clauses={} \
                     permanent_clause_owners_awaiting_rekey={} \
                     learned_term_pins={} retired_sat_vars={} \
                     nonreplayable_retired_sat_vars={} \
                     replay_source_sat_only_literals={} root_units={}",
                    rebuild.source_clauses_before,
                    self.active_forgettable_clauses.len(),
                    rebuild.root_satisfied_source_clauses,
                    rebuild.root_satisfied_instance_groups,
                    root_satisfied_compact_instances,
                    self.rebuild_learned_clauses.len(),
                    dropped_learned_clauses,
                    retired_source_instances,
                    released_source_instance_keys,
                    rebuild.retired_instance_source_clauses,
                    rebuild.permanent_clause_owners_awaiting_rekey,
                    learned_term_uids.len(),
                    retired_sat_vars.len(),
                    nonreplayable_retired_sat_vars.len(),
                    replay_source_sat_only_literals,
                    root_units.len(),
                );
            }
        } else {
            self.forgettable_queue = self.active_forgettable_clauses.clone();
            self.forgettable_queue
                .extend(self.rebuild_learned_clauses.iter().cloned());
        }
        self.draining_forgettable = false;
        self.next_is_decision = false;
        root_units
    }

    pub fn register_replayed_learned_clause_ownership(
        &mut self,
        replay_clauses: &[Vec<i32>],
    ) -> ReplayedLearnedOwnershipProfile {
        let replay_shapes: DeterministicHashSet<Vec<i32>> = replay_clauses
            .iter()
            .map(|clause| normalize_clause(clause))
            .collect();
        let candidates = std::mem::take(&mut self.rebuild_learned_clause_terms);
        let candidate_clause_shapes = candidates.len();
        let mut replayed_clause_shapes = 0usize;
        let mut dropped_clause_shapes = 0usize;
        let mut replayed_term_uids = DeterministicHashSet::default();

        if let Some(gc_state) = self.qi_gc_state.clone() {
            let mut gc = gc_state.borrow_mut();
            for (clause, term_uids) in candidates {
                if replay_shapes.contains(&clause) {
                    replayed_clause_shapes += 1;
                    replayed_term_uids.extend(term_uids.iter().copied());
                    gc.tracker
                        .register_pending_permanent_clause(&clause, term_uids);
                } else {
                    dropped_clause_shapes += 1;
                }
            }
            gc.rebuild_learned_term_uids.clear();
        }

        ReplayedLearnedOwnershipProfile {
            candidate_clause_shapes,
            replayed_clause_shapes,
            dropped_clause_shapes,
            replayed_term_uids: replayed_term_uids.len(),
        }
    }

    pub fn begin_qi_gc_maintenance(&mut self) {
        assert!(
            !self.qi_gc_maintenance_in_progress,
            "nested QI GC maintenance"
        );
        self.qi_gc_maintenance_in_progress = true;
    }

    pub fn finish_qi_gc_maintenance(&mut self) {
        assert!(
            self.qi_gc_maintenance_in_progress,
            "QI GC maintenance finished without being started"
        );
        self.qi_gc_maintenance_in_progress = false;
    }

    /// Point callback-side operations at the fresh solver and observe only
    /// live Sundance terms plus the current activation literal.
    pub fn attach_rebuilt_solver(&mut self, solver: &mut CaDiCal) {
        self.solver = solver as *mut CaDiCal;
        self.last_observed_var = 1;
        self.sync_new_vars();
        if let Some(ref gc) = self.qi_gc_state {
            let current_act = gc.borrow().current_act;
            if current_act != 0 {
                solver.add_observed_var(current_act);
            }
        }
    }

    pub fn replay_sat_phase_hints(&self, solver: &mut CaDiCal) -> usize {
        let activation_lits = self
            .qi_gc_state
            .as_ref()
            .map(|gc| gc.borrow().activation_lits.clone())
            .unwrap_or_default();
        let limit = self.qi_gc_phase_hints.len().min(solver.vars() as usize + 1);
        let mut replayed = 0;
        for idx in 1..limit {
            let sign = self.qi_gc_phase_hints[idx];
            if sign == 0
                || activation_lits.contains(&(idx as i32))
                || self.solver_state.is_retired_sat_var(idx as i32)
            {
                continue;
            }
            solver.phase(if sign > 0 { idx as i32 } else { -(idx as i32) });
            replayed += 1;
        }
        replayed
    }

    pub fn queued_retired_activation_clauses(&self) -> usize {
        let retired_activations = self
            .qi_gc_state
            .as_ref()
            .map(|gc| gc.borrow().retired_activations.clone())
            .unwrap_or_default();
        let contains_retired_activation = |clause: &&Vec<i32>| {
            clause
                .iter()
                .any(|lit| retired_activations.contains(&lit.abs()))
        };
        self.forgettable_queue
            .iter()
            .filter(contains_retired_activation)
            .count()
            + self
                .disequalities
                .borrow()
                .iter()
                .filter(|clause| {
                    clause
                        .literals
                        .iter()
                        .any(|lit| retired_activations.contains(&lit.abs()))
                })
                .count()
    }

    pub fn drain_retirement_units_for_in_place_gc(&mut self) -> Vec<Vec<i32>> {
        let retired_activations = self
            .qi_gc_state
            .as_ref()
            .map(|gc| gc.borrow().retired_activations.clone())
            .unwrap_or_default();
        let mut queued = self.disequalities.borrow_mut();
        let clauses = std::mem::take(&mut *queued);
        let (retirement_units, remaining): (Vec<_>, Vec<_>) =
            clauses.into_iter().partition(|clause| {
                clause.literals.len() == 1
                    && retired_activations.contains(&clause.literals[0].abs())
            });
        *queued = remaining;
        retirement_units
            .into_iter()
            .map(|clause| clause.literals)
            .collect()
    }

    fn consume_preserved_root_assignment(&mut self, lit: i32) -> bool {
        if self.decision_level != 0 {
            return false;
        }
        let idx = lit.unsigned_abs() as usize;
        let Some(expected) = self.qi_gc_preserved_root_assignments.get_mut(idx) else {
            return false;
        };
        if *expected == 0 {
            return false;
        }
        assert_eq!(
            *expected,
            lit.signum() as i8,
            "rebuilt CaDiCaL replayed root variable {} with the opposite polarity",
            idx
        );
        *expected = 0;
        true
    }

    fn apply_instances(
        &mut self,
        instances: &[crate::quantifiers::quantifier::QuantifierInstance],
    ) {
        for inst in instances {
            let (clauses, pre_nnf_body, instantiation_key) = match inst {
                Instantiation {
                    clauses,
                    pre_nnf_body,
                    key,
                    created_terms,
                    clause_terms,
                } => {
                    self.stats.instantiations += 1;
                    (
                        clauses,
                        pre_nnf_body,
                        Some((key, created_terms, clause_terms)),
                    )
                }
                Skolemization {
                    clauses,
                    pre_nnf_body,
                } => (clauses, pre_nnf_body, None),
            };
            if let Some((key, created_terms, clause_terms)) = instantiation_key
                && let Some(ref gc) = self.qi_gc_state
            {
                let mut gc = gc.borrow_mut();
                if gc.compact_qi_obligations.remove(key)
                    && gc.tracker.protect_instance_from_collection(key)
                {
                    gc.total_gc_protected_qi_instances += 1;
                }
                gc.epoch_instantiations += 1;
                gc.total_epoch_instantiations += 1;
                let activation = gc.current_act;
                gc.tracker.register_instance(
                    key.clone(),
                    clauses,
                    activation,
                    created_terms,
                    clause_terms,
                );
            }
            if instantiation_key.is_none()
                && let Some(ref gc) = self.qi_gc_state
            {
                let mut pinned = DeterministicHashSet::default();
                self.solver_state
                    .collect_registered_term_closure(pre_nnf_body, &mut pinned);
                self.solver_state
                    .collect_clause_term_closure(clauses, &mut pinned);
                gc.borrow_mut().tracker.pin_permanent_terms(pinned);
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
                if instantiation_key.is_some()
                    && let Some(ref gc) = self.qi_gc_state
                {
                    let mut gc = gc.borrow_mut();
                    let activation = gc.current_act;
                    gc.epoch_guarded_clauses += 1;
                    gc.total_guarded_clauses += 1;
                    let epoch = gc.epoch;
                    drop(gc);
                    let mut guarded = clause.clone();
                    if activation != 0 {
                        guarded.push(-activation);
                    }
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
                    self.active_forgettable_clauses.push(guarded.clone());
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
        let round_complete = pending.is_empty();
        if round_complete {
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

        // Collection planning is proportional to the current dependency
        // graph. Evaluate it once after a complete matching round, when all
        // instance groups are stable, rather than at every SAT decision.
        if round_complete
            && count > 0
            && let Some(ref gc) = self.qi_gc_state
        {
            let mut gc = gc.borrow_mut();
            if gc.epoch_guarded_clauses >= QI_GC_MIN_EPOCH_CLAUSES {
                gc.collection_check_pending = true;
            }
        }

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
        if QI_GC_PROFILE.load(Ordering::Relaxed) {
            eprintln!(
                "[qi-gc-profile] qi-match-config scope={:?} require_quantifier_relevance={} \
                 allow_skolemization={} generation_limit={:?} instantiation_limit={:?}",
                trigger_match_scope,
                require_quantifier_relevance,
                allow_skolemization,
                generation_limit,
                instantiation_limit,
            );
        }
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
    /// Promotes activation-free consequences, rebuilds the SAT solver without
    /// the old guarded clauses, and retires terms owned only by the old epoch.
    fn trigger_epoch_transition(&mut self, gc_state: &Rc<RefCell<QiGcState>>) {
        let gc = gc_state.borrow_mut();
        let old_act = gc.current_act;
        let neg_old_act = -old_act;
        let epoch = gc.epoch;
        let theory_clauses_by_kind = gc.theory_clauses_by_kind;
        let theory_clauses_touching_epoch_terms_by_kind =
            gc.theory_clauses_touching_epoch_terms_by_kind;
        let newly_pinned_epoch_term_references_by_kind =
            gc.newly_pinned_epoch_term_references_by_kind;

        qi_gc_trace!(
            "epoch {}: backtrack to level 0, triggering epoch transition",
            epoch
        );
        drop(gc);
        self.print_qi_gc_profile("epoch-transition-start");
        debug_assert!(!self.materializing_quantifiers);
        let dropped_pending_qi = self.pending.take().map_or(0, |pending| pending.len());
        if dropped_pending_qi != 0 {
            qi_gc_trace!(
                "epoch {}: discarded {} old-generation pending QI items",
                epoch,
                dropped_pending_qi
            );
            if QI_GC_PROFILE.load(Ordering::Relaxed) {
                eprintln!(
                    "[qi-gc-profile] transition-discarded-pending epoch={} items={}",
                    epoch, dropped_pending_qi
                );
            }
        }

        let QiGcPlan {
            retained_instances,
            retained_orphan_clauses,
            derived_clauses,
            observed_qi_clauses,
            retained_qi_clause_ids: _,
            antecedent_edges,
            retained_term_uids,
            permanent_term_uids,
            epoch_owned_term_uids,
        } = gc_state.borrow().tracker.plan();
        let live_qi_clauses = gc_state.borrow().tracker.live_qi_clauses();
        let live_qi_clause_count = live_qi_clauses.len();
        let support_instance_count = retained_instances.len();
        let retained_orphan_count = retained_orphan_clauses.len();
        let support_qi_count = retained_instances
            .iter()
            .map(|instance| instance.clauses.len())
            .sum::<usize>()
            + retained_orphan_count;
        // Every live activation-dependent consequence is compressed below
        // into a clause guarded by the next epoch's activation. The old
        // instance clauses themselves can therefore all be retired.
        let retained_qi_count = 0;
        let retired_qi_count = observed_qi_clauses;
        let support_term_count = retained_term_uids.difference(&permanent_term_uids).count();
        let permanent_epoch_terms_before = permanent_term_uids
            .intersection(&epoch_owned_term_uids)
            .count();

        // Keep every live activation-dependent learned clause. The proof
        // tracer sees all derived clauses and deletions; the Learner is a
        // fallback for any 1-UIP clause not present in those callbacks.
        let (learner_derived, safe_learned) = {
            let gc = gc_state.borrow();
            (
                gc.learned_clauses
                    .iter()
                    .map(|clause| {
                        clause
                            .iter()
                            .copied()
                            .filter(|lit| *lit != neg_old_act)
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>(),
                gc.safe_learned_clauses.clone(),
            )
        };
        let safe_learned_count = safe_learned.len();
        let promoted_derived =
            deduplicate_clauses(derived_clauses.into_iter().chain(learner_derived));
        let promoted_derived_count = promoted_derived.len();
        let migrated_derived: Vec<Vec<i32>> = promoted_derived
            .iter()
            .filter(|clause| !clause.is_empty())
            .cloned()
            .collect();
        let migrated_derived_count = migrated_derived.len();
        let promotes_empty_clause = migrated_derived_count != promoted_derived_count;
        // Activation-free clauses already resident in CaDiCaL outlive this
        // epoch, so their terms must become permanent. The migrated summaries
        // are guarded by the next epoch and therefore need only survive this
        // transition; leave those terms epoch-owned so a later collection can
        // still reclaim them.
        let mut permanent_pinned_term_uids = permanent_term_uids.clone();
        let mut safe_learned_term_uids = DeterministicHashSet::default();
        self.solver_state
            .collect_clause_term_closure(&safe_learned, &mut safe_learned_term_uids);
        permanent_pinned_term_uids.extend(safe_learned_term_uids.iter().copied());
        let mut transition_pinned_term_uids = permanent_pinned_term_uids.clone();
        let mut migrated_summary_term_uids = DeterministicHashSet::default();
        self.solver_state
            .collect_clause_term_closure(&promoted_derived, &mut migrated_summary_term_uids);
        transition_pinned_term_uids.extend(migrated_summary_term_uids.iter().copied());
        let permanent_epoch_terms_after = permanent_pinned_term_uids
            .intersection(&epoch_owned_term_uids)
            .count();
        let mut retired_candidate_term_uids = epoch_owned_term_uids.clone();
        retired_candidate_term_uids.retain(|uid| !transition_pinned_term_uids.contains(uid));

        qi_gc_trace!(
            "epoch {}: dependency plan observed_qi={} migrated_qi={} retired_qi={} \
             support_instances={} support_qi={} migrated_orphans={} support_clause_terms={} \
             epoch_owned_terms={} permanent_terms={} permanent_epoch_terms_before={} \
             permanent_epoch_terms_after={} pinned_terms={} retire_term_candidates={} \
             promoted_derived={} migrated_derived={} migrated_summary_terms={} safe_learned={} \
             live_qi_in_sat={} promotes_empty={} ancestry_edges={} \
             theory_clauses={:?} theory_clauses_touching_epoch_terms={:?} \
             newly_pinned_epoch_term_references={:?}",
            epoch,
            observed_qi_clauses,
            retained_qi_count,
            retired_qi_count,
            support_instance_count,
            support_qi_count,
            retained_orphan_count,
            support_term_count,
            epoch_owned_term_uids.len(),
            permanent_term_uids.len(),
            permanent_epoch_terms_before,
            permanent_epoch_terms_after,
            transition_pinned_term_uids.len(),
            retired_candidate_term_uids.len(),
            promoted_derived_count,
            migrated_derived_count,
            migrated_summary_term_uids.len(),
            safe_learned_count,
            live_qi_clause_count,
            promotes_empty_clause,
            antecedent_edges,
            theory_clauses_by_kind,
            theory_clauses_touching_epoch_terms_by_kind,
            newly_pinned_epoch_term_references_by_kind,
        );
        if QI_GC_PROFILE.load(Ordering::Relaxed) {
            eprintln!(
                "[qi-gc-profile] migration-plan epoch={} observed_qi={} migrated_qi={} \
                 retired_qi={} support_instances={} support_qi={} migrated_orphans={} \
                 support_clause_terms={} epoch_owned_terms={} permanent_terms={} \
                 permanent_epoch_terms_before={} permanent_epoch_terms_after={} \
                 pinned_terms={} retire_term_candidates={} promoted_derived={} \
                 migrated_derived={} migrated_summary_terms={} safe_learned={} live_qi_in_sat={} \
                 promotes_empty={} ancestry_edges={} theory_clauses={:?} \
                 theory_clauses_touching_epoch_terms={:?} \
                 newly_pinned_epoch_term_references={:?}",
                epoch,
                observed_qi_clauses,
                retained_qi_count,
                retired_qi_count,
                support_instance_count,
                support_qi_count,
                retained_orphan_count,
                support_term_count,
                epoch_owned_term_uids.len(),
                permanent_term_uids.len(),
                permanent_epoch_terms_before,
                permanent_epoch_terms_after,
                transition_pinned_term_uids.len(),
                retired_candidate_term_uids.len(),
                promoted_derived_count,
                migrated_derived_count,
                migrated_summary_term_uids.len(),
                safe_learned_count,
                live_qi_clause_count,
                promotes_empty_clause,
                antecedent_edges,
                theory_clauses_by_kind,
                theory_clauses_touching_epoch_terms_by_kind,
                newly_pinned_epoch_term_references_by_kind,
            );
        }

        // 1. Retire the old epoch in place. Fixing `-act` at level zero makes
        // every old guarded clause satisfied; the outer solve loop then asks
        // CaDiCaL to simplify and physically collect that dead generation
        // without replacing the solver and losing its search state.
        self.queue_theory_clause(retire_activation_unit(old_act), Theory::Background);

        // 2. A promoted empty clause is a permanent UNSAT proof. Non-empty
        // consequences are re-guarded by the next activation below, which
        // preserves current search knowledge without making this generation
        // immortal.
        if promotes_empty_clause {
            self.queue_theory_clause(Vec::new(), Theory::Background);
        }
        for promoted in &migrated_derived {
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
                    "[qi-gc] epoch {}: migrating conflict clause: {:?}",
                    epoch, terms
                );
            }
        }

        // 3. Reclaim the solver/egraph state owned only by discarded
        // instances. The egraph performs a second structural safety check and
        // returns only isolated terms that were physically tombstoned.
        let term_gc = self
            .solver_state
            .retire_qi_terms(&retired_candidate_term_uids, &transition_pinned_term_uids);
        for var in &term_gc.retired_sat_vars {
            let idx = *var as usize;
            if idx < self.assignments.len() {
                self.assignments[idx] = 0;
                self.theory_processed_levels[idx] = None;
                self.theory_assignment_pending[idx] = false;
            }
            self.fixed_literals.remove(var);
            self.fixed_literals.remove(&-*var);
        }
        self.pending_relevant_assignments
            .retain(|lit| !self.solver_state.is_retired_sat_var(*lit));
        let activation_lits = gc_state.borrow().activation_lits.clone();
        self.rebuild_learned_clauses = deduplicate_clauses(
            migrated_derived
                .iter()
                .filter(|clause| {
                    clause.iter().all(|lit| {
                        !activation_lits.contains(&lit.abs())
                            && !self.solver_state.is_retired_sat_var(*lit)
                    })
                })
                .cloned(),
        );

        #[cfg(feature = "z3-solver")]
        let z3_rebuild = if self.z3_incremental.is_some() {
            let root_literals: Vec<i32> = self
                .assignments
                .iter()
                .enumerate()
                .skip(1)
                .filter_map(|(idx, assignment)| {
                    (*assignment != 0
                        && self.theory_processed_levels[idx] == Some(0)
                        && !self.solver_state.is_retired_sat_var(idx as i32)
                        && (self
                            .solver_state
                            .cnf_cache
                            .var_map_reverse
                            .contains_key(&(idx as i32))
                            || self
                                .solver_state
                                .cnf_cache
                                .var_map_reverse
                                .contains_key(&-(idx as i32))))
                    .then_some(if *assignment > 0 {
                        idx as i32
                    } else {
                        -(idx as i32)
                    })
                })
                .collect();
            let arithmetic_equalities = self.solver_state.egraph.arithmetic_root_equalities();
            let (rebuilt, profile) = Z3IncrementalState::rebuild_from_root(
                &root_literals,
                &arithmetic_equalities,
                self.solver_state,
            );
            self.z3_incremental = Some(rebuilt);
            Some(profile)
        } else {
            None
        };

        qi_gc_trace!(
            "epoch {}: term GC requested={} candidate_classes={} fully_candidate_classes={} \
             retired_classes={} pruned_mixed_classes={} pruned_mixed_class_terms={} \
             retired_terms={} retired_sat_vars={} \
             predecessors_before={} predecessors_after_compaction={} \
             predecessors_after_retirement={} blocked_mixed_class_roots={} \
             blocked_live_parent_terms={} blocked_proof_reference_terms={} \
             blocked_disequality_terms={} blocked_pattern_terms={} \
             blocked_trigger_head_terms={} blocked_pending_event_terms={} missing={}",
            epoch,
            term_gc.requested,
            term_gc.candidate_classes,
            term_gc.fully_candidate_classes,
            term_gc.retired_classes,
            term_gc.pruned_mixed_classes,
            term_gc.pruned_mixed_class_terms,
            term_gc.retired_terms,
            term_gc.retired_sat_vars.len(),
            term_gc.predecessor_entries_before,
            term_gc.predecessor_entries_after_compaction,
            term_gc.predecessor_entries_after_retirement,
            term_gc.blocked_mixed_class_roots,
            term_gc.blocked_live_parent_terms,
            term_gc.blocked_proof_reference_terms,
            term_gc.blocked_disequality_terms,
            term_gc.blocked_pattern_terms,
            term_gc.blocked_trigger_head_terms,
            term_gc.blocked_pending_event_terms,
            term_gc.missing
        );
        #[cfg(feature = "z3-solver")]
        if (QI_GC_TRACE.load(Ordering::Relaxed) || QI_GC_PROFILE.load(Ordering::Relaxed))
            && let Some(profile) = z3_rebuild
        {
            eprintln!(
                "[qi-gc-profile] z3-rebuild root_literals={} arithmetic_equalities={}",
                profile.replayed_root_literals, profile.replayed_arithmetic_equalities
            );
        }
        if QI_GC_PROFILE.load(Ordering::Relaxed) {
            eprintln!(
                "[qi-gc-profile] term-gc requested={} candidate_classes={} \
                 fully_candidate_classes={} retired_classes={} pruned_mixed_classes={} \
                 pruned_mixed_class_terms={} retired_terms={} retired_sat_vars={} \
                 predecessors_before={} predecessors_after_compaction={} \
                 predecessors_after_retirement={} blocked_mixed_class_roots={} \
                 blocked_live_parent_terms={} blocked_proof_reference_terms={} \
                 blocked_disequality_terms={} blocked_pattern_terms={} \
                 blocked_trigger_head_terms={} blocked_pending_event_terms={} missing={}",
                term_gc.requested,
                term_gc.candidate_classes,
                term_gc.fully_candidate_classes,
                term_gc.retired_classes,
                term_gc.pruned_mixed_classes,
                term_gc.pruned_mixed_class_terms,
                term_gc.retired_terms,
                term_gc.retired_sat_vars.len(),
                term_gc.predecessor_entries_before,
                term_gc.predecessor_entries_after_compaction,
                term_gc.predecessor_entries_after_retirement,
                term_gc.blocked_mixed_class_roots,
                term_gc.blocked_live_parent_terms,
                term_gc.blocked_proof_reference_terms,
                term_gc.blocked_disequality_terms,
                term_gc.blocked_pattern_terms,
                term_gc.blocked_trigger_head_terms,
                term_gc.blocked_pending_event_terms,
                term_gc.missing
            );
        }

        let retired_term_uids: DeterministicHashSet<u64> =
            term_gc.retired_term_uids.iter().copied().collect();
        let mut carried_epoch_term_uids = epoch_owned_term_uids;
        carried_epoch_term_uids.retain(|uid| {
            !retired_term_uids.contains(uid) && !permanent_pinned_term_uids.contains(uid)
        });

        // 4. Start a new generation. Terms that the egraph conservatively
        // refused to retire remain owned by this new epoch so a later
        // collection can try again.
        let mut gc = gc_state.borrow_mut();
        gc.learned_clauses.clear();
        gc.safe_learned_clauses.clear();
        gc.tracker.clear_epoch();
        gc.tracker
            .pin_permanent_terms(permanent_pinned_term_uids.iter().copied());
        gc.tracker
            .set_epoch_owned_terms(carried_epoch_term_uids.iter().copied());
        gc.total_retained_qi_clauses += retained_qi_count as u64;
        gc.total_retired_qi_clauses += retired_qi_count as u64;
        gc.total_promoted_derived_clauses += promoted_derived_count as u64;
        gc.total_retired_terms += term_gc.retired_terms as u64;
        gc.total_retired_sat_vars += term_gc.retired_sat_vars.len() as u64;
        gc.retired_activations.insert(old_act);
        for (id, clause) in live_qi_clauses {
            gc.pending_retired_qi_clause_ids.insert(id);
            *gc.pending_retired_qi_clause_contents
                .entry(clause)
                .or_default() += 1;
        }
        let previous_instantiations: usize = self
            .solver_state
            .added_instantiations
            .values()
            .map(HashSet::len)
            .sum();
        self.solver_state.added_instantiations.clear();
        let preserved_instantiations: usize = self
            .solver_state
            .added_instantiations
            .values()
            .map(HashSet::len)
            .sum();
        qi_gc_trace!(
            "epoch {}: preserved {} of {} added_instantiations",
            epoch,
            preserved_instantiations,
            previous_instantiations
        );

        // 5. Allocate and initialize the new epoch.
        gc.epoch += 1;
        gc.transitions += 1;
        let migrated_clause_count = self.rebuild_learned_clauses.len();
        gc.epoch_guarded_clauses = migrated_clause_count as u64;
        gc.total_guarded_clauses += migrated_clause_count as u64;
        gc.epoch_instantiations = 0;
        gc.collection_check_pending = false;
        gc.theory_clauses_by_kind = [0; QI_GC_THEORY_KINDS];
        gc.theory_clauses_touching_epoch_terms_by_kind = [0; QI_GC_THEORY_KINDS];
        gc.newly_pinned_epoch_term_references_by_kind = [0; QI_GC_THEORY_KINDS];
        gc.theory_unit_clauses_by_kind = [0; QI_GC_THEORY_KINDS];
        gc.theory_unit_clauses_touching_epoch_terms_by_kind = [0; QI_GC_THEORY_KINDS];
        gc.newly_pinned_epoch_term_references_from_units_by_kind = [0; QI_GC_THEORY_KINDS];
        gc.theory_empty_clauses_by_kind = [0; QI_GC_THEORY_KINDS];

        let new_act = self.solver_state.cnf_cache.next_var;
        self.solver_state.cnf_cache.next_var += 1;
        gc.current_act = new_act;
        gc.activation_lits.insert(new_act);
        let new_epoch = gc.epoch;
        let pending_registrations = gc.tracker.pending_clause_registrations();
        drop(gc);

        // 6. Guard the compressed live consequences with the new activation.
        // They are treated as orphan QI clauses by the dependency tracker:
        // if they produce no live consequence in this epoch, the next
        // transition can discard them and their terms.
        let migrated_guarded_clauses: Vec<Vec<i32>> = self
            .rebuild_learned_clauses
            .iter()
            .map(|clause| {
                let mut guarded = clause.clone();
                guarded.push(-new_act);
                guarded
            })
            .collect();
        debug_assert_eq!(migrated_guarded_clauses.len(), migrated_clause_count);
        self.active_forgettable_clauses = migrated_guarded_clauses.clone();
        for guarded in migrated_guarded_clauses {
            self.proof_tracer
                .borrow_mut()
                .register_clause_for_cadical_callback(&guarded);
            self.forgettable_queue.push(guarded);
        }

        // Observe the new activation literal so CaDiCaL knows it exists.
        unsafe {
            (*self.solver).add_observed_var(new_act);
        }

        qi_gc_trace!(
            "epoch {}: transition complete. migrated {} QI clauses and {} derived clauses, \
             retired {}, carried {} epoch terms, pending registrations={}. new act={}",
            new_epoch,
            retained_qi_count,
            migrated_derived_count,
            retired_qi_count,
            carried_epoch_term_uids.len(),
            pending_registrations,
            new_act
        );
        if QI_GC_PROFILE.load(Ordering::Relaxed) {
            eprintln!(
                "[qi-gc-profile] migration-complete epoch={} migrated_qi={} \
                 migrated_derived={} retired_qi={} promotes_empty={} carried_epoch_terms={} \
                 retained_learned={} pending_registrations={} new_act={}",
                new_epoch,
                retained_qi_count,
                migrated_derived_count,
                retired_qi_count,
                promotes_empty_clause,
                carried_epoch_term_uids.len(),
                self.rebuild_learned_clauses.len(),
                pending_registrations,
                new_act
            );
        }
        self.print_qi_gc_profile("epoch-transition-complete");
        {
            let mut gc = gc_state.borrow_mut();
            gc.in_search_collection_started = Some(Instant::now());
            gc.in_search_collection_expected_qi_clauses = live_qi_clause_count;
        }
        // The retirement unit and migrated summaries are waiting in the
        // external-clause queues. CaDiCaL consumes them before returning from
        // external propagation, then services this request at the next safe
        // point in its live CDCL loop.
        unsafe {
            (*self.solver).request_garbage_collection();
        }
    }

    /// A tainted learned clause `-act ∨ C` forces `-act` at level zero when
    /// every literal in `C` is already false there. In this case the epoch's
    /// activation-independent consequence must be promoted immediately.
    fn qi_gc_requires_root_transition(&self, gc: &QiGcState) -> bool {
        if gc.current_act == 0 {
            return false;
        }
        gc.learned_clauses.iter().any(|clause| {
            activation_consequence_is_false_at_root(&self.assignments, clause, gc.current_act)
        })
    }

    /// Complete bookkeeping only after CaDiCaL has reported deletion of every
    /// source clause in the requested instance groups.
    fn finish_targeted_qi_collection_if_ready(&mut self) -> bool {
        let Some(gc_state) = self.qi_gc_state.clone() else {
            return false;
        };
        let (epoch, finalized) = {
            let mut gc = gc_state.borrow_mut();
            if gc.pending_retired_qi_group_ids.is_empty()
                || !gc.pending_retired_qi_clause_ids.is_empty()
                || !gc.pending_retired_qi_clause_contents.is_empty()
            {
                return false;
            }
            let group_ids = std::mem::take(&mut gc.pending_retired_qi_group_ids);
            let activation = gc.current_act;
            let finalized = gc
                .tracker
                .finalize_collected_instance_groups(&group_ids, activation);
            gc.total_reclaimed_qi_instances += finalized.len() as u64;
            (gc.epoch, finalized)
        };
        let permanently_satisfied: Vec<_> = finalized
            .iter()
            .filter(|instance| {
                instance
                    .clauses
                    .iter()
                    .all(|clause| clause_is_satisfied_at_root(&self.assignments, clause))
            })
            .collect();
        let compact_obligations = finalized
            .iter()
            .map(|instance| instance.key.clone())
            .collect::<Vec<_>>();
        {
            let mut gc = gc_state.borrow_mut();
            gc.total_permanently_satisfied_qi_instances += permanently_satisfied.len() as u64;
            gc.compact_qi_obligations.extend(compact_obligations);
            gc.targeted_term_gc_pending = true;
        }

        let clauses: Vec<Vec<i32>> = finalized
            .iter()
            .flat_map(|instance| instance.clauses.iter().cloned())
            .collect();
        let removed_active = remove_clause_multiset(&mut self.active_forgettable_clauses, &clauses);
        let removed_queued = remove_clause_multiset(&mut self.forgettable_queue, &clauses);

        qi_gc_trace!(
            "epoch {}: completed targeted collection groups={} clauses={} \
             permanently_satisfied={} pending_key_releases={} \
             removed_active={} removed_queued={}",
            epoch,
            finalized.len(),
            clauses.len(),
            permanently_satisfied.len(),
            finalized.len() - permanently_satisfied.len(),
            removed_active,
            removed_queued
        );
        if QI_GC_PROFILE.load(Ordering::Relaxed) {
            eprintln!(
                "[qi-gc-profile] targeted-collection-complete epoch={} groups={} clauses={} \
                 permanently_satisfied={} pending_key_releases={} \
                 removed_active={} removed_queued={}",
                epoch,
                finalized.len(),
                clauses.len(),
                permanently_satisfied.len(),
                finalized.len() - permanently_satisfied.len(),
                removed_active,
                removed_queued
            );
        }
        true
    }

    fn compact_qi_obligations(&self) -> usize {
        self.qi_gc_state
            .as_ref()
            .map_or(0, |gc| gc.borrow().compact_qi_obligations.len())
    }

    fn release_compact_qi_obligations_for_model_matching(&mut self) -> usize {
        let Some(gc_state) = self.qi_gc_state.clone() else {
            return 0;
        };
        let keys: Vec<QiInstantiationKey> = gc_state
            .borrow()
            .compact_qi_obligations
            .iter()
            .cloned()
            .collect();
        let released = keys
            .iter()
            .filter(|key| {
                self.solver_state
                    .forget_added_instantiation(key.quantifier_id, &key.substitution)
            })
            .count();
        if QI_GC_PROFILE.load(Ordering::Relaxed) && !keys.is_empty() {
            eprintln!(
                "[qi-gc-profile] compact-model-reactivation candidates={} released_keys={}",
                keys.len(),
                released,
            );
        }
        released
    }

    /// Restore a legacy clause obligation when the model violates it. Compact
    /// obligations retain no old SAT or e-graph closure, so their model value
    /// cannot be checked directly. They are rematerialized only when
    /// `include_compact` is true, after the ordinary complete-model
    /// quantifier round has saturated.
    fn resurrect_violated_retired_qi_instances(
        &mut self,
        model: &[i32],
        include_compact: bool,
    ) -> usize {
        let started = Instant::now();
        let Some(gc_state) = self.qi_gc_state.clone() else {
            return 0;
        };
        let has_retired = {
            let gc = gc_state.borrow();
            !gc.retired_qi_instances.is_empty()
                || (include_compact && !gc.compact_qi_obligations.is_empty())
        };
        if !has_retired {
            return 0;
        }

        let max_var = model
            .iter()
            .map(|lit| lit.unsigned_abs() as usize)
            .max()
            .unwrap_or(0);
        let mut model_values = vec![0i8; max_var + 1];
        for lit in model {
            model_values[lit.unsigned_abs() as usize] = if *lit > 0 { 1 } else { -1 };
        }

        let limit = if self.batch_cap == 0 {
            usize::MAX
        } else {
            self.batch_cap
        };
        let (epoch, activation, resurrected, remaining) = {
            let mut gc = gc_state.borrow_mut();
            let epoch = gc.epoch;
            let activation = gc.current_act;
            let compact_ready = include_compact && !gc.targeted_term_gc_pending;
            let mut resurrected = Vec::new();
            let mut remaining = Vec::new();
            for instance in std::mem::take(&mut gc.retired_qi_instances) {
                let requires_restoration = instance
                    .clauses
                    .iter()
                    .any(|clause| !clause_is_satisfied_by_model(clause, &model_values));
                if requires_restoration && resurrected.len() < limit {
                    resurrected.push(instance);
                } else {
                    remaining.push(instance);
                }
            }
            gc.retired_qi_instances = remaining;
            if compact_ready && resurrected.len() < limit {
                let compact_keys: Vec<QiInstantiationKey> = gc
                    .compact_qi_obligations
                    .iter()
                    .take(limit - resurrected.len())
                    .cloned()
                    .collect();
                for key in compact_keys {
                    assert!(gc.compact_qi_obligations.remove(&key));
                    resurrected.push(QiRetainedInstance {
                        key,
                        clauses: Vec::new(),
                        created_terms: DeterministicHashSet::default(),
                        clause_terms: DeterministicHashSet::default(),
                    });
                }
            }
            gc.total_resurrected_qi_instances += resurrected.len() as u64;
            (
                epoch,
                activation,
                resurrected,
                gc.retired_qi_instances.len() + gc.compact_qi_obligations.len(),
            )
        };
        if resurrected.is_empty() {
            return 0;
        }

        let resurrected_instances = resurrected.len();
        let mut restored_clauses = 0usize;
        let mut rematerialized_instances = 0usize;
        let mut newly_gc_protected = 0usize;
        for instance in resurrected {
            let compact_obligation = instance.clauses.is_empty();
            self.solver_state.remember_added_instantiation(
                instance.key.quantifier_id,
                &instance.key.substitution,
            );
            {
                let mut gc = gc_state.borrow_mut();
                if gc.tracker.protect_instance_from_collection(&instance.key) {
                    newly_gc_protected += 1;
                    gc.total_gc_protected_qi_instances += 1;
                }
            }
            if compact_obligation {
                let materialized = rematerialize_instantiation(
                    &instance.key,
                    self.solver_state,
                    &self.proof_tracer,
                );
                restored_clauses += materialized
                    .iter()
                    .map(|instance| match instance {
                        Instantiation { clauses, .. } | Skolemization { clauses, .. } => {
                            clauses.len()
                        }
                    })
                    .sum::<usize>();
                rematerialized_instances += 1;
                self.apply_instances(&materialized);
                continue;
            }

            {
                let mut gc = gc_state.borrow_mut();
                gc.epoch_guarded_clauses += instance.clauses.len() as u64;
                gc.total_guarded_clauses += instance.clauses.len() as u64;
                gc.tracker
                    .register_retained_instance(instance.clone(), activation);
            }
            restored_clauses += instance.clauses.len();
            for clause in instance.clauses {
                let mut restored = clause;
                if activation != 0 {
                    restored.push(-activation);
                }
                self.proof_tracer
                    .borrow_mut()
                    .register_clause_for_cadical_callback(&restored);
                self.active_forgettable_clauses.push(restored.clone());
                self.forgettable_queue.push(restored);
            }
        }

        qi_gc_trace!(
            "epoch {}: resurrected {} retired instances \
             (clauses={}, rematerialized={}, newly_gc_protected={}, remaining={})",
            epoch,
            resurrected_instances,
            restored_clauses,
            rematerialized_instances,
            newly_gc_protected,
            remaining
        );
        if QI_GC_PROFILE.load(Ordering::Relaxed) {
            eprintln!(
                "[qi-gc-profile] retired-model-check epoch={} include_compact={} \
                 resurrected_instances={} \
                 restored_clauses={} rematerialized_instances={} newly_gc_protected={} \
                 remaining_retired_instances={} duration={:.6}s",
                epoch,
                include_compact,
                resurrected_instances,
                restored_clauses,
                rematerialized_instances,
                newly_gc_protected,
                remaining,
                started.elapsed().as_secs_f64(),
            );
        }
        restored_clauses
    }

    /// Compact the level-zero e-graph and retire epoch-owned terms that are no
    /// longer referenced by active clauses, learned consequences, permanent
    /// theory state, or model-checked retired obligations.
    fn run_targeted_qi_term_gc_if_pending(&mut self) {
        if self.decision_level != 0 || self.qi_gc_maintenance_in_progress {
            return;
        }
        self.run_targeted_qi_term_gc(false);
    }

    /// Re-evaluate term ownership after SAT rebuild preparation has removed
    /// root-satisfied and stale source clauses. Collect the newly exposed
    /// terms before replaying into the fresh solver so they do not require a
    /// second replacement immediately afterward.
    pub fn run_targeted_qi_term_gc_during_maintenance(&mut self) {
        assert_eq!(
            self.decision_level, 0,
            "maintenance term GC requires a root backtrack"
        );
        assert!(
            self.qi_gc_maintenance_in_progress,
            "maintenance term GC requires an active SAT rebuild"
        );
        let Some(gc_state) = self.qi_gc_state.clone() else {
            return;
        };
        gc_state.borrow_mut().targeted_term_gc_pending = true;
        self.run_targeted_qi_term_gc(true);
    }

    fn run_targeted_qi_term_gc(&mut self, during_maintenance: bool) {
        let gc_started = Instant::now();
        let Some(gc_state) = self.qi_gc_state.clone() else {
            return;
        };
        let (epoch, epoch_owned, mut pinned) = {
            let gc = gc_state.borrow();
            if !gc.targeted_term_gc_pending
                || !gc.pending_retired_qi_clause_ids.is_empty()
                || !gc.pending_retired_qi_clause_contents.is_empty()
                || !gc.pending_requested_theory_clause_ids.is_empty()
            {
                return;
            }
            let plan = gc.tracker.plan();
            (
                gc.epoch,
                plan.epoch_owned_term_uids,
                qi_gc_pinned_term_uids(&gc, self.solver_state),
            )
        };
        // `QiGcTracker` sees an external source clause only after CaDiCaL
        // requests it and the proof callback assigns it an ID. The complete
        // current source generation also lives in `active_forgettable_clauses`
        // while clauses are waiting in the callback queue, so include it in
        // the ownership closure before reclaiming theory-bearing terms.
        self.solver_state
            .collect_clause_theory_term_closure(&self.active_forgettable_clauses, &mut pinned);
        let mut candidates = epoch_owned.clone();
        candidates.retain(|uid| !pinned.contains(uid));
        if candidates.is_empty() {
            gc_state.borrow_mut().targeted_term_gc_pending = false;
            let compact_qi_obligations = self.compact_qi_obligations();
            if QI_GC_PROFILE.load(Ordering::Relaxed) {
                eprintln!(
                    "[qi-gc-profile] targeted-term-gc-skipped epoch={} \
                     reason=no-unpinned-candidates epoch_owned={} pinned={} \
                     compact_qi_obligations={} \
                     candidate_selection_duration={:.6}s total_duration={:.6}s",
                    epoch,
                    epoch_owned.len(),
                    pinned.len(),
                    compact_qi_obligations,
                    gc_started.elapsed().as_secs_f64(),
                    gc_started.elapsed().as_secs_f64(),
                );
            }
            return;
        }
        let candidate_selection_duration = gc_started.elapsed();

        // Root-level SAT synchronization can register fresh terms after the
        // most recent notify_backtrack callback. Fold those level-zero
        // signature/proof entries into the persistent baseline before the
        // collector checks its quiescence invariant.
        let quiesce_started = Instant::now();
        let before_quiesce = self.solver_state.egraph.gc_profile();
        self.solver_state.egraph.backtrack_to(0);
        let _ = self.solver_state.egraph.collect_backtracked_predecessors();
        let after_quiesce = self.solver_state.egraph.gc_profile();
        let quiesce_duration = quiesce_started.elapsed();
        if QI_GC_PROFILE.load(Ordering::Relaxed) {
            eprintln!(
                "[qi-gc-profile] term-gc-quiesce proof_entries_before={} \
                 proof_entries_after={} signature_trail_before={} \
                 signature_trail_after={} duration={:.6}s",
                before_quiesce.backtrack_entries,
                after_quiesce.backtrack_entries,
                before_quiesce.signature_trail_entries,
                after_quiesce.signature_trail_entries,
                quiesce_duration.as_secs_f64(),
            );
        }

        let retire_started = Instant::now();
        let term_gc = self.solver_state.retire_qi_terms(&candidates, &pinned);
        let retire_duration = retire_started.elapsed();
        let post_retire_started = Instant::now();
        for var in &term_gc.retired_sat_vars {
            let idx = *var as usize;
            if idx < self.assignments.len() {
                self.assignments[idx] = 0;
                self.theory_processed_levels[idx] = None;
                self.theory_assignment_pending[idx] = false;
            }
            self.fixed_literals.remove(var);
            self.fixed_literals.remove(&-*var);
        }
        self.pending_relevant_assignments
            .retain(|lit| !self.solver_state.is_retired_sat_var(*lit));

        #[cfg(feature = "z3-solver")]
        let z3_rebuild = if term_gc.retired_terms != 0 && self.z3_incremental.is_some() {
            let snapshot_started = Instant::now();
            let root_literals: Vec<i32> = self
                .assignments
                .iter()
                .enumerate()
                .skip(1)
                .filter_map(|(idx, assignment)| {
                    (*assignment != 0
                        && self.theory_processed_levels[idx] == Some(0)
                        && !self.solver_state.is_retired_sat_var(idx as i32)
                        && (self
                            .solver_state
                            .cnf_cache
                            .var_map_reverse
                            .contains_key(&(idx as i32))
                            || self
                                .solver_state
                                .cnf_cache
                                .var_map_reverse
                                .contains_key(&-(idx as i32))))
                    .then_some(if *assignment > 0 {
                        idx as i32
                    } else {
                        -(idx as i32)
                    })
                })
                .collect();
            let arithmetic_equalities = self.solver_state.egraph.arithmetic_root_equalities();
            let snapshot_duration = snapshot_started.elapsed();
            let rebuild_started = Instant::now();
            let (rebuilt, profile) = Z3IncrementalState::rebuild_from_root(
                &root_literals,
                &arithmetic_equalities,
                self.solver_state,
            );
            let rebuild_duration = rebuild_started.elapsed();
            self.z3_incremental = Some(rebuilt);
            Some((profile, snapshot_duration, rebuild_duration))
        } else {
            None
        };

        let retired_term_uids: DeterministicHashSet<u64> =
            term_gc.retired_term_uids.iter().copied().collect();
        let mut remaining_epoch_terms = epoch_owned;
        remaining_epoch_terms.retain(|uid| !retired_term_uids.contains(uid));
        {
            let mut gc = gc_state.borrow_mut();
            gc.tracker
                .set_epoch_owned_terms(remaining_epoch_terms.iter().copied());
            gc.total_retired_terms += term_gc.retired_terms as u64;
            gc.total_retired_sat_vars += term_gc.retired_sat_vars.len() as u64;
            gc.pending_unobserve_sat_vars
                .extend(term_gc.retired_sat_vars.iter().copied());
            gc.targeted_term_gc_pending = false;
            gc.total_predecessor_compactions += 1;
            gc.total_predecessor_entries_removed += term_gc
                .predecessor_entries_before
                .saturating_sub(term_gc.predecessor_entries_after_retirement)
                as u64;
        }
        let compact_qi_obligations = self.compact_qi_obligations();
        let pending_unobserve_sat_vars = gc_state.borrow().pending_unobserve_sat_vars.len();
        if !during_maintenance
            && pending_unobserve_sat_vars >= QI_GC_MIN_RETIRED_SAT_VARS_FOR_REBUILD
            && let Some(requested) = &self.qi_gc_rebuild_requested
        {
            // `remove_observed_var` is only legal between CaDiCaL solve
            // calls. Ask the terminator to yield only after enough dormant
            // variables have accumulated to amortize a full solver rebuild.
            requested.set(true);
        } else if !during_maintenance
            && !term_gc.retired_sat_vars.is_empty()
            && QI_GC_PROFILE.load(Ordering::Relaxed)
        {
            eprintln!(
                "[qi-gc-profile] sat-rebuild-deferred newly_retired_sat_vars={} \
                 pending_unobserve_sat_vars={} threshold={}",
                term_gc.retired_sat_vars.len(),
                pending_unobserve_sat_vars,
                QI_GC_MIN_RETIRED_SAT_VARS_FOR_REBUILD,
            );
        }
        let post_retire_duration = post_retire_started.elapsed();
        let total_duration = gc_started.elapsed();

        qi_gc_trace!(
            "epoch {}: targeted term GC requested={} candidate_classes={} \
             fully_candidate_classes={} retired_classes={} pruned_mixed_classes={} \
             pruned_mixed_class_terms={} retired_terms={} retired_sat_vars={} \
             retired_sat_only_vars={} \
             predecessors_before={} predecessors_after_compaction={} \
             predecessors_after_retirement={} blocked_mixed_class_roots={} \
             blocked_live_parent_terms={} blocked_proof_reference_terms={} \
             blocked_disequality_terms={} blocked_pattern_terms={} \
             blocked_trigger_head_terms={} blocked_pending_event_terms={} missing={} \
             compact_qi_obligations={}",
            epoch,
            term_gc.requested,
            term_gc.candidate_classes,
            term_gc.fully_candidate_classes,
            term_gc.retired_classes,
            term_gc.pruned_mixed_classes,
            term_gc.pruned_mixed_class_terms,
            term_gc.retired_terms,
            term_gc.retired_sat_vars.len(),
            term_gc.retired_sat_only_vars.len(),
            term_gc.predecessor_entries_before,
            term_gc.predecessor_entries_after_compaction,
            term_gc.predecessor_entries_after_retirement,
            term_gc.blocked_mixed_class_roots,
            term_gc.blocked_live_parent_terms,
            term_gc.blocked_proof_reference_terms,
            term_gc.blocked_disequality_terms,
            term_gc.blocked_pattern_terms,
            term_gc.blocked_trigger_head_terms,
            term_gc.blocked_pending_event_terms,
            term_gc.missing,
            compact_qi_obligations,
        );
        if QI_GC_PROFILE.load(Ordering::Relaxed) {
            eprintln!(
                "[qi-gc-profile] targeted-term-gc epoch={} maintenance={} \
                 requested={} candidate_classes={} \
                 fully_candidate_classes={} retired_classes={} pruned_mixed_classes={} \
                 pruned_mixed_class_terms={} retired_terms={} retired_sat_vars={} \
                 retired_sat_only_vars={} \
                 predecessors_before={} \
                 predecessors_after_compaction={} predecessors_after_retirement={} \
                 blocked_mixed_class_roots={} blocked_live_parent_terms={} \
                 blocked_proof_reference_terms={} blocked_disequality_terms={} \
                 blocked_pattern_terms={} blocked_trigger_head_terms={} \
                 blocked_pending_event_terms={} missing={} compact_qi_obligations={} \
                 candidate_selection_duration={:.6}s quiesce_duration={:.6}s \
                 retire_duration={:.6}s post_retire_duration={:.6}s \
                total_duration={:.6}s",
                epoch,
                during_maintenance,
                term_gc.requested,
                term_gc.candidate_classes,
                term_gc.fully_candidate_classes,
                term_gc.retired_classes,
                term_gc.pruned_mixed_classes,
                term_gc.pruned_mixed_class_terms,
                term_gc.retired_terms,
                term_gc.retired_sat_vars.len(),
                term_gc.retired_sat_only_vars.len(),
                term_gc.predecessor_entries_before,
                term_gc.predecessor_entries_after_compaction,
                term_gc.predecessor_entries_after_retirement,
                term_gc.blocked_mixed_class_roots,
                term_gc.blocked_live_parent_terms,
                term_gc.blocked_proof_reference_terms,
                term_gc.blocked_disequality_terms,
                term_gc.blocked_pattern_terms,
                term_gc.blocked_trigger_head_terms,
                term_gc.blocked_pending_event_terms,
                term_gc.missing,
                compact_qi_obligations,
                candidate_selection_duration.as_secs_f64(),
                quiesce_duration.as_secs_f64(),
                retire_duration.as_secs_f64(),
                post_retire_duration.as_secs_f64(),
                total_duration.as_secs_f64(),
            );
        }
        #[cfg(feature = "z3-solver")]
        if QI_GC_PROFILE.load(Ordering::Relaxed)
            && let Some((profile, snapshot_duration, rebuild_duration)) = z3_rebuild
        {
            eprintln!(
                "[qi-gc-profile] targeted-z3-rebuild root_literals={} \
                 arithmetic_equalities={} snapshot_duration={:.6}s \
                 rebuild_duration={:.6}s",
                profile.replayed_root_literals,
                profile.replayed_arithmetic_equalities,
                snapshot_duration.as_secs_f64(),
                rebuild_duration.as_secs_f64(),
            );
        }
    }

    /// Evaluate a requested collection at a callback where all external
    /// clauses from the completed matching round have been consumed. If the
    /// exact dependency plan is sufficiently compressible, schedule one root
    /// restart; otherwise wait for another completed matching round.
    fn schedule_qi_gc_transition_if_worthwhile(&mut self) {
        self.finish_targeted_qi_collection_if_ready();
        if self.qi_gc_maintenance_in_progress {
            if QI_GC_PROFILE.load(Ordering::Relaxed)
                && self
                    .qi_gc_state
                    .as_ref()
                    .is_some_and(|gc| gc.borrow().collection_check_pending)
            {
                eprintln!("[qi-gc-profile] collection-check-deferred reason=sat-maintenance");
            }
            return;
        }
        // Root term collection can retire SAT variables and request a solver
        // rebuild from this same callback. Do not enqueue a fresh batch of
        // clause-ID deletions into the old solver after that request: the
        // terminator may return before CaDiCaL services them, leaving the
        // rebuild with outstanding collection callbacks. Preserve
        // `collection_check_pending` so the fresh solver evaluates the batch.
        if self
            .qi_gc_rebuild_requested
            .as_ref()
            .is_some_and(|requested| requested.get())
        {
            if QI_GC_PROFILE.load(Ordering::Relaxed)
                && self
                    .qi_gc_state
                    .as_ref()
                    .is_some_and(|gc| gc.borrow().collection_check_pending)
            {
                eprintln!("[qi-gc-profile] collection-check-deferred reason=sat-rebuild-pending");
            }
            return;
        }
        let Some(gc_state) = self.qi_gc_state.clone() else {
            return;
        };
        let (
            epoch,
            epoch_clauses,
            pending_registrations,
            analysis,
            term_gc_scheduled,
            collection_in_flight,
        ) = {
            let mut gc = gc_state.borrow_mut();
            if !gc.collection_check_pending {
                return;
            }
            let pending_registrations = gc.tracker.pending_clause_registrations();
            if pending_registrations != 0 {
                if QI_GC_PROFILE.load(Ordering::Relaxed) {
                    eprintln!(
                        "[qi-gc-profile] collection-check-deferred epoch={} \
                         pending_clause_registrations={}",
                        gc.epoch, pending_registrations
                    );
                }
                return;
            }
            gc.collection_check_pending = false;
            let collection_in_flight = !gc.pending_retired_qi_clause_ids.is_empty()
                || !gc.pending_retired_qi_clause_contents.is_empty()
                || !gc.pending_requested_theory_clause_ids.is_empty();
            let candidates = gc
                .tracker
                .collectible_instance_groups()
                .into_iter()
                .filter(|group| !gc.pending_retired_qi_group_ids.contains(&group.group_id))
                .collect::<Vec<_>>();
            let root_satisfied_instances = candidates
                .iter()
                .filter(|group| instance_group_is_satisfied_at_root(&self.assignments, group))
                .count();
            let collectible_qi = candidates
                .iter()
                .map(|group| group.clauses.len())
                .sum::<usize>();
            let root_satisfied_qi = candidates
                .iter()
                .filter(|group| instance_group_is_satisfied_at_root(&self.assignments, group))
                .map(|group| group.clauses.len())
                .sum::<usize>();
            let collectible_theory = gc.tracker.collectible_forgettable_theory_clause_ids().len();
            let analysis = qi_gc_collection_analysis(
                &gc,
                self.solver_state,
                candidates.len(),
                collectible_qi,
                root_satisfied_instances,
                root_satisfied_qi,
                collectible_theory,
                !collection_in_flight,
            );
            // Term ownership is independent from source-clause ancestry:
            // terms outside every live clause/theory closure can be reclaimed
            // even when the source database itself is not yet compressible.
            // Use the same fixed-work batch as clause collection so a solver
            // rebuild is amortized without returning to the old every-round
            // term-GC behavior.
            let term_gc_scheduled = analysis.term_gc_worthwhile && !collection_in_flight;
            if term_gc_scheduled {
                gc.targeted_term_gc_pending = true;
            }
            (
                gc.epoch,
                gc.epoch_guarded_clauses,
                pending_registrations,
                analysis,
                term_gc_scheduled,
                collection_in_flight,
            )
        };

        if QI_GC_PROFILE.load(Ordering::Relaxed) {
            eprintln!(
                "[qi-gc-profile] collection-check epoch={} level={} epoch_clauses={} \
                 observed_qi={} support_qi={} retained_qi={} reclaimable_qi={} promoted_derived={} \
                 collectible_instances={} collectible_qi={} root_satisfied_instances={} \
                 root_satisfied_qi={} collectible_theory={} epoch_owned_terms={} \
                 candidate_terms={} \
                 pending_clause_registrations={} worthwhile={} term_gc_worthwhile={} \
                 term_analysis_skipped={} collection_in_flight={} trigger={:?}",
                epoch,
                self.decision_level,
                epoch_clauses,
                analysis.observed_qi,
                analysis.support_qi,
                analysis.retained_qi,
                analysis.reclaimable_qi,
                analysis.promoted_derived,
                analysis.collectible_instances,
                analysis.collectible_qi,
                analysis.root_satisfied_instances,
                analysis.root_satisfied_qi,
                analysis.collectible_theory,
                analysis.epoch_owned_terms,
                analysis.candidate_terms,
                pending_registrations,
                analysis.worthwhile,
                analysis.term_gc_worthwhile,
                analysis.term_analysis_skipped,
                collection_in_flight,
                analysis.trigger,
            );
            if term_gc_scheduled {
                eprintln!(
                    "[qi-gc-profile] term-gc-scheduled epoch={} level={} candidate_terms={} \
                     source_collection_worthwhile={}",
                    epoch, self.decision_level, analysis.candidate_terms, analysis.worthwhile,
                );
            }
        }
        if !analysis.worthwhile {
            if term_gc_scheduled {
                if self.decision_level != 0 {
                    self.qi_gc_force_backtrack = true;
                    if QI_GC_PROFILE.load(Ordering::Relaxed) {
                        eprintln!(
                            "[qi-gc-profile] term-gc-root-request epoch={} level={} \
                             candidate_terms={} epoch_owned_terms={}",
                            epoch,
                            self.decision_level,
                            analysis.candidate_terms,
                            analysis.epoch_owned_terms,
                        );
                    }
                }
            } else if analysis.candidate_terms != 0 && QI_GC_PROFILE.load(Ordering::Relaxed) {
                eprintln!(
                    "[qi-gc-profile] term-gc-deferred epoch={} level={} \
                     candidate_terms={} epoch_owned_terms={} reason=below-term-batch",
                    epoch,
                    self.decision_level,
                    analysis.candidate_terms,
                    analysis.epoch_owned_terms,
                );
            }
            return;
        }

        // CaDiCaL services explicit collection requests at a safe CDCL-loop
        // point and protects every clause that is still a reason. QI source
        // clauses are redundant theory lemmas, so non-reason sources can be
        // forgotten without changing satisfiability. Any reason-protected
        // source remains pending and is retried after a later backtrack.
        //
        // Keep term retirement separate: deleting a source clause may release
        // its ownership, but e-graph terms and observed SAT variables are
        // reclaimed only by the existing level-zero maintenance path.
        //
        // A learned SAT clause derived from QI source clauses is itself a
        // valid consequence of the quantified input. Keep that learned
        // clause in CaDiCaL, but make it a new dependency root so historical
        // source instances no longer stay alive solely for proof ancestry.
        // Recompute the exact collection plan after promotion.
        let (
            promoted_derived_roots,
            candidates,
            analysis,
            term_gc_scheduled_after_promotion,
            derived_size_histogram,
        ) = {
            let mut gc = gc_state.borrow_mut();
            let derived_size_histogram = gc.tracker.derived_clause_size_histogram();
            let promoted_derived_roots = gc.tracker.promote_live_derived_roots();
            gc.total_promoted_derived_clauses += promoted_derived_roots as u64;
            let all_candidates = gc
                .tracker
                .collectible_instance_groups()
                .into_iter()
                .filter(|group| !gc.pending_retired_qi_group_ids.contains(&group.group_id))
                .collect::<Vec<_>>();
            let collectible_qi = all_candidates
                .iter()
                .map(|group| group.clauses.len())
                .sum::<usize>();
            let root_satisfied_instances = all_candidates
                .iter()
                .filter(|group| instance_group_is_satisfied_at_root(&self.assignments, group))
                .count();
            let root_satisfied_qi = all_candidates
                .iter()
                .filter(|group| instance_group_is_satisfied_at_root(&self.assignments, group))
                .map(|group| group.clauses.len())
                .sum::<usize>();
            let collectible_theory = gc.tracker.collectible_forgettable_theory_clause_ids().len();
            let collection_in_flight = !gc.pending_retired_qi_clause_ids.is_empty()
                || !gc.pending_retired_qi_clause_contents.is_empty()
                || !gc.pending_requested_theory_clause_ids.is_empty();
            let analysis = qi_gc_collection_analysis(
                &gc,
                self.solver_state,
                all_candidates.len(),
                collectible_qi,
                root_satisfied_instances,
                root_satisfied_qi,
                collectible_theory,
                !collection_in_flight,
            );
            let term_gc_scheduled = analysis.term_gc_worthwhile && !collection_in_flight;
            if term_gc_scheduled {
                gc.targeted_term_gc_pending = true;
            }
            (
                promoted_derived_roots,
                all_candidates,
                analysis,
                term_gc_scheduled,
                derived_size_histogram,
            )
        };
        let targets: Vec<(u64, Vec<i32>)> = candidates
            .iter()
            .flat_map(|group| group.clauses.iter().cloned())
            .collect();
        let theory_targets = {
            let gc = gc_state.borrow();
            gc.tracker
                .collectible_forgettable_theory_clause_ids()
                .into_iter()
                .filter(|id| !gc.pending_requested_theory_clause_ids.contains(id))
                .collect::<Vec<_>>()
        };
        if targets.is_empty() && theory_targets.is_empty() {
            return;
        }
        {
            let mut gc = gc_state.borrow_mut();
            gc.total_retired_qi_clauses += targets.len() as u64;
            if !targets.is_empty() {
                gc.in_search_collection_started = Some(Instant::now());
                gc.in_search_collection_expected_qi_clauses = targets.len();
            }
            gc.pending_retired_qi_group_ids
                .extend(candidates.iter().map(|group| group.group_id));
            for (id, clause) in &targets {
                gc.pending_retired_qi_clause_ids.insert(*id);
                *gc.pending_retired_qi_clause_contents
                    .entry(clause.clone())
                    .or_default() += 1;
            }
            gc.total_requested_theory_clauses += theory_targets.len() as u64;
            gc.pending_requested_theory_clause_ids
                .extend(theory_targets.iter().copied());
        }
        qi_gc_trace!(
            "epoch {}: targeted collection requested at level {} \
             (promoted_derived_roots={}, target_instances={}, target_qi={}, \
             target_theory={}, reclaimable_qi={}, candidate_terms={})",
            epoch,
            self.decision_level,
            promoted_derived_roots,
            candidates.len(),
            targets.len(),
            theory_targets.len(),
            analysis.reclaimable_qi,
            analysis.candidate_terms
        );
        if QI_GC_PROFILE.load(Ordering::Relaxed) {
            eprintln!(
                "[qi-gc-profile] targeted-collection-request epoch={} level={} \
                 promoted_derived_roots={} target_instances={} target_qi={} \
                 target_theory={} reclaimable_qi={} candidate_terms={}",
                epoch,
                self.decision_level,
                promoted_derived_roots,
                candidates.len(),
                targets.len(),
                theory_targets.len(),
                analysis.reclaimable_qi,
                analysis.candidate_terms
            );
            if term_gc_scheduled_after_promotion {
                eprintln!(
                    "[qi-gc-profile] term-gc-scheduled-after-promotion epoch={} \
                     candidate_terms={}",
                    epoch, analysis.candidate_terms
                );
            }
            eprintln!(
                "[qi-gc-profile] derived-clause-size-histogram epoch={} sizes={:?}",
                epoch, derived_size_histogram
            );
        }
        for (id, _) in targets {
            unsafe {
                (*self.solver).request_clause_garbage_collection(id);
            }
        }
        for id in theory_targets {
            unsafe {
                (*self.solver).request_clause_garbage_collection(id);
            }
        }
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
        self.qi_gc_phase_hints.resize(new_len, 0);
    }

    fn record_sat_assignment(&mut self, lit: i32) {
        let idx = lit.unsigned_abs() as usize;
        self.ensure_theory_assignment_capacity(idx);
        let sign = if lit > 0 { 1 } else { -1 };
        self.qi_gc_phase_hints[idx] = sign as i8;
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

    fn trace_first_observed_assignment_after_decision(&mut self, lit: i32) {
        if !self.next_is_decision {
            return;
        }
        self.next_is_decision = false;
        if !QI_GC_TRACE.load(Ordering::Relaxed) {
            return;
        }

        let is_activation = self
            .qi_gc_state
            .as_ref()
            .is_some_and(|gc| gc.borrow().activation_lits.contains(&lit.abs()));
        if is_activation {
            eprintln!(
                "[qi-gc] first observed assignment after decision level {}: lit={} term=<activation>",
                self.decision_level, lit,
            );
        } else if self.solver_state.is_retired_sat_var(lit) {
            eprintln!(
                "[qi-gc] first observed assignment after decision level {}: lit={} term=<retired>",
                self.decision_level, lit,
            );
        } else {
            eprintln!(
                "[qi-gc] first observed assignment after decision level {}: lit={} term={} relevant={}",
                self.decision_level,
                lit,
                self.solver_state.get_term_from_lit(lit),
                self.solver_state.is_lit_relevant(lit),
            );
        }
    }

    /// Theory atoms can produce useful conflicts from a partial assignment
    /// even when their Boolean context is currently irrelevant. Relevancy
    /// filtering still suppresses pure Boolean/Tseitin structure and inactive
    /// quantifiers, which have no independent theory effect.
    fn is_theory_atom(&mut self, lit: i32) -> bool {
        if self.solver_state.is_retired_sat_var(lit) {
            return false;
        }
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
        if self.solver_state.is_retired_sat_var(lit) {
            return;
        }
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
                let origin = if theory == Theory::Datatypes {
                    TheoryClauseOrigin::DatatypeAssignment
                } else {
                    TheoryClauseOrigin::Other
                };
                self.queue_theory_clause_with_origin(shrunk_constraint, theory, origin);
            }
        }
    }

    fn process_pending_relevant_assignments(&mut self) {
        self.queue_newly_relevant_assignments();
        while let Some(lit) = self.pending_relevant_assignments.pop_front() {
            let idx = lit.unsigned_abs() as usize;
            self.ensure_theory_assignment_capacity(idx);
            self.theory_assignment_pending[idx] = false;
            if self.solver_state.is_retired_sat_var(lit) {
                continue;
            }

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
            self.trace_first_observed_assignment_after_decision(*lit);
            if self.consume_preserved_root_assignment(*lit) {
                continue;
            }
            // Skip activation literals — they have no term in the egraph.
            if let Some(ref gc) = self.qi_gc_state {
                if gc.borrow().activation_lits.contains(&lit.abs()) {
                    let mut gc = gc.borrow_mut();
                    if *lit < 0
                        && gc.retired_activations.contains(&lit.abs())
                        && gc.observed_retirement_units.insert(lit.abs())
                        && QI_GC_PROFILE.load(Ordering::Relaxed)
                    {
                        eprintln!(
                            "[qi-gc-profile] retirement-unit-observed act={} lit={} level={}",
                            lit.abs(),
                            lit,
                            self.decision_level
                        );
                    }
                    drop(gc);
                    self.record_sat_assignment(*lit);
                    continue;
                }
            }
            if self.solver_state.is_retired_sat_var(*lit) {
                self.record_sat_assignment(*lit);
                continue;
            }

            debug_println!(
                7,
                0,
                "Assigning the literal {:?} (level {}) which is {}",
                lit,
                self.decision_level,
                self.solver_state.get_term_from_lit(*lit)
            );

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
        let _ = self.solver_state.egraph.collect_backtracked_predecessors();
        self.solver_state.propagate_class_relevancy_from_merges();

        #[cfg(feature = "z3-solver")]
        {
            if let Some(z3) = self.z3_incremental.as_mut() {
                z3.notify_backtrack(level);
                z3.drain_merge_queue(self.solver_state);
            }
        }
        // `drain_merge_queue` calls `make_eq`, which can itself merge newly
        // registered equality terms and enqueue class-relevancy events.
        // Consume those events before root GC snapshots class member ranges;
        // otherwise the collector must conservatively pin every pending range.
        self.solver_state.propagate_class_relevancy_from_merges();
        if level == 0 {
            self.finish_targeted_qi_collection_if_ready();
            self.run_targeted_qi_term_gc_if_pending();
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

        // A root-falsified activation consequence still requires an epoch
        // transition. Ordinary source-clause collection is targeted in place
        // and must not turn a natural restart into a generation reset.
        let transition_requested = level == 0
            && self.qi_gc_state.as_ref().is_some_and(|gc| {
                let gc = gc.borrow();
                gc.pending_retired_qi_clause_ids.is_empty()
                    && gc.pending_retired_qi_clause_contents.is_empty()
                    && self.qi_gc_requires_root_transition(&gc)
            });
        if level == 0 && (self.qi_gc_transition_pending || transition_requested) {
            self.qi_gc_transition_pending = false;
            self.qi_gc_force_backtrack = false;
            if let Some(gc_state) = self.qi_gc_state.clone() {
                self.trigger_epoch_transition(&gc_state);
            }
        }

        // `force_backtrack(0)` returns control to CaDiCaL, which may create
        // its next decision level before invoking `cb_decide` again. Submit a
        // deferred targeted collection while this callback still observes the
        // level-zero state instead of waiting for a root-level decision
        // callback that is not guaranteed to occur.
        if level == 0 {
            self.schedule_qi_gc_transition_if_worthwhile();
        }

        // A targeted clause may have been protected because it was a reason
        // during the first collection. At a natural root backtrack all
        // transient reasons have been released, so retry without forcing an
        // additional backtrack.
        if level == 0
            && self.qi_gc_state.as_ref().is_some_and(|gc| {
                let gc = gc.borrow();
                !gc.pending_retired_qi_clause_ids.is_empty()
                    || !gc.pending_requested_theory_clause_ids.is_empty()
            })
        {
            unsafe {
                (*self.solver).request_garbage_collection();
            }
        }

        debug_println!(16, 0, "Ending backtracking at level {}", level);
        debug_println!(11, 0, "{}", self.solver_state.egraph);
    }

    fn cb_check_found_model(&mut self, model: &[i32]) -> bool {
        self.finish_targeted_qi_collection_if_ready();
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
                if self.solver_state.is_retired_sat_var(id) {
                    continue;
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
                    if self.solver_state.is_retired_sat_var(*x) {
                        return None;
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

        if self.resurrect_violated_retired_qi_instances(model, false) > 0 {
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
            if self.solver_state.is_retired_sat_var(*term) {
                continue;
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
                            let _ = self.solver_state.egraph.collect_backtracked_predecessors();
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
                let _ = self.solver_state.egraph.collect_backtracked_predecessors();
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
                self.queue_theory_clause_with_origin(
                    conflict_clause,
                    Theory::Datatypes,
                    TheoryClauseOrigin::DatatypeOccursCheck,
                );
                self.stats.conflicts += 1;
                return false;
            }

            // Lazy case split: add tester clauses for uninitialized datatype terms
            let new_clauses =
                crate::datatypes::occurs_check::generate_deferred_tester_clauses(self.solver_state);
            if !new_clauses.is_empty() {
                for clause in new_clauses {
                    self.queue_theory_clause_with_origin(
                        clause,
                        Theory::Datatypes,
                        TheoryClauseOrigin::DatatypeDeferredTester,
                    );
                }
                self.sync_new_vars();
                self.stats.conflicts += 1;
                return false;
            }
        }

        debug_println!(11, 0, "Starting quantifier instantiations");
        // Eager rounds use relevant classes as a cheap source of likely useful
        // instances. At a complete-model check, widen the search to every class
        // so filtered progress cannot indefinitely postpone a refutation.
        self.release_compact_qi_obligations_for_model_matching();
        if !self.start_quantifier_instantiation_round(
            true,
            false,
            TriggerMatchScope::AllClasses,
            None,
            None,
        ) {
            // Compact GC obligations intentionally have no remaining CNF
            // closure. Give the active model and the regular all-class
            // quantifier round the first chance to make progress; only
            // rematerialize an old exact substitution before accepting a
            // genuinely saturated model.
            if self.resurrect_violated_retired_qi_instances(model, true) > 0 {
                self.stats.conflicts += 1;
                return false;
            }
            debug_println!(10, 0, "{}", self.solver_state.egraph);
            assert!(self.disequalities.borrow().is_empty());
            if QI_GC_PROFILE.load(Ordering::Relaxed) {
                let egraph = self.solver_state.egraph.gc_profile();
                if let Some(gc_state) = &self.qi_gc_state {
                    let gc = gc_state.borrow();
                    let tracker = gc.tracker.profile();
                    eprintln!(
                        "[qi-gc-profile] model-saturated epoch={} quantifiers={} \
                         retired_instances={} pending_sat_gc_ids={} \
                         pending_sat_gc_contents={} total_retired_terms={} \
                         total_retired_sat_vars={} tracked_qi={} instance_groups={} \
                         egraph_terms={} reusable_ids={} function_entries={} \
                         active_relevant_terms={} predecessors={} match_calls={} \
                         match_candidates={} relevant_match_candidates={} match_results={}",
                        gc.epoch,
                        self.solver_state.quantifiers.len(),
                        gc.retired_qi_instances.len() + gc.compact_qi_obligations.len(),
                        gc.pending_retired_qi_clause_ids.len(),
                        gc.pending_retired_qi_clause_contents
                            .values()
                            .sum::<usize>(),
                        gc.total_retired_terms,
                        gc.total_retired_sat_vars,
                        tracker.qi_clauses,
                        tracker.instance_groups,
                        egraph.registered_terms,
                        egraph.reusable_ids,
                        egraph.function_entries,
                        egraph.active_relevant_terms,
                        egraph.predecessor_entries,
                        egraph.e_match_calls,
                        egraph.e_match_candidates_scanned,
                        egraph.e_match_relevant_candidates_scanned,
                        egraph.e_match_results,
                    );
                } else {
                    eprintln!(
                        "[qi-gc-profile] model-saturated epoch=disabled quantifiers={} \
                         egraph_terms={} reusable_ids={} function_entries={} \
                         active_relevant_terms={} predecessors={} match_calls={} \
                         match_candidates={} relevant_match_candidates={} match_results={}",
                        self.solver_state.quantifiers.len(),
                        egraph.registered_terms,
                        egraph.reusable_ids,
                        egraph.function_entries,
                        egraph.active_relevant_terms,
                        egraph.predecessor_entries,
                        egraph.e_match_calls,
                        egraph.e_match_candidates_scanned,
                        egraph.e_match_relevant_candidates_scanned,
                        egraph.e_match_results,
                    );
                }
            }
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

        self.schedule_qi_gc_transition_if_worthwhile();
        if self.decision_level == 0 {
            self.run_targeted_qi_term_gc_if_pending();
        }

        // A collection request can coincide with a natural root backtrack.
        // Complete it directly instead of asking CaDiCaL to backtrack from
        // level zero to level zero.
        if self.qi_gc_transition_pending && self.decision_level == 0 {
            self.qi_gc_transition_pending = false;
            self.qi_gc_force_backtrack = false;
            if let Some(gc_state) = self.qi_gc_state.clone() {
                self.trigger_epoch_transition(&gc_state);
            }
        }

        if self
            .qi_gc_rebuild_requested
            .as_ref()
            .is_some_and(|requested| requested.get())
        {
            return 0;
        }

        // QI GC: force backtrack to level 0 if scheduled (triggers epoch transition)
        if self.qi_gc_force_backtrack {
            self.qi_gc_force_backtrack = false;
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
                if act == 0 {
                    // Targeted clause-ID collection does not use a selector.
                } else {
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

        // An epoch transition has already built the exact replay queues and
        // requested replacement of this SAT solver. Do not let the old solver
        // consume those clauses before it is discarded: doing so gives them
        // obsolete clause IDs and makes the dependency tracker observe the
        // migrated generation twice.
        if self
            .qi_gc_rebuild_requested
            .as_ref()
            .is_some_and(|requested| requested.get())
        {
            self.draining_forgettable = false;
            return false;
        }

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

        let mut queued = self.disequalities.borrow_mut();
        let Some(clause) = queued.last_mut() else {
            return false;
        };
        *is_forgettable = clause.forgettable;
        if !clause.ownership_registered {
            if let Some(gc) = &self.qi_gc_state
                && let Some(tracked_terms) = clause.tracked_terms.clone()
            {
                if clause.forgettable {
                    gc.borrow_mut()
                        .tracker
                        .register_pending_forgettable_theory_clause(
                            &clause.literals,
                            tracked_terms,
                        );
                } else {
                    gc.borrow_mut()
                        .tracker
                        .register_pending_permanent_clause(&clause.literals, tracked_terms);
                }
            }
            clause.ownership_registered = true;
        }
        match clause.literals.len() {
            0 | 1 => {} // don't count unit or empty clauses
            2 => self.stats.binary_clauses += 1,
            _ => self.stats.clauses += 1,
        }
        debug_println!(
            4,
            0,
            "In cb_has_external_clause: We have the following disequalities: {:?}",
            queued[0]
        );
        true
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
        debug_println!(
            11,
            0,
            "We have the next clause {:?}",
            v[last_index].literals
        );
        let literal = if v[last_index].literals.is_empty() {
            v.pop();
            0
        } else {
            v[last_index].literals.pop().unwrap()
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
    use super::{
        QiGcCollectionTrigger, activation_consequence_is_false_at_root,
        clause_is_satisfied_at_root, clause_is_satisfied_by_model,
        instance_group_is_satisfied_at_root, qi_gc_collection_trigger,
        qi_gc_term_reduction_is_worthwhile, retire_activation_unit,
    };
    use crate::qi_gc::QiCollectibleInstanceGroup;

    #[test]
    fn retiring_activation_satisfies_negatively_guarded_epoch_clauses() {
        assert_eq!(retire_activation_unit(17), vec![-17]);
    }

    #[test]
    fn root_transition_requires_the_activation_free_consequence_to_be_false() {
        // Root assignments: variable 1 is true, variable 2 is false.
        let assignments = vec![0, 1, -1, 0];
        assert!(activation_consequence_is_false_at_root(
            &assignments,
            &[-100, -1, 2],
            100,
        ));
        assert!(!activation_consequence_is_false_at_root(
            &assignments,
            &[-100, 1, 2],
            100,
        ));
        assert!(!activation_consequence_is_false_at_root(
            &assignments,
            &[-100, 3],
            100,
        ));
    }

    #[test]
    fn collection_uses_an_absolute_batch_or_a_large_garbage_fraction() {
        assert_eq!(
            qi_gc_collection_trigger(9_999, 5_000, 5_000),
            QiGcCollectionTrigger::EpochTooSmall
        );
        assert_eq!(
            qi_gc_collection_trigger(20_000, 4_000, 499),
            QiGcCollectionTrigger::BatchTooSmall
        );
        assert_eq!(
            qi_gc_collection_trigger(20_000, 4_000, 1_000),
            QiGcCollectionTrigger::BatchTooSmall
        );
        assert_eq!(
            qi_gc_collection_trigger(20_000, 1_064, 609),
            QiGcCollectionTrigger::GarbageToLiveRatio
        );
        assert_eq!(
            qi_gc_collection_trigger(10_000, 8_000, 2_000),
            QiGcCollectionTrigger::AbsoluteBatch
        );
    }

    #[test]
    fn term_collection_requires_an_amortized_batch() {
        assert!(!qi_gc_term_reduction_is_worthwhile(9_999, 5_000));
        assert!(!qi_gc_term_reduction_is_worthwhile(20_000, 1_999));
        assert!(qi_gc_term_reduction_is_worthwhile(10_000, 2_000));
    }

    #[test]
    fn permanent_collection_requires_a_root_satisfying_literal() {
        // Variable 1 is true at root, variable 2 is false at root, and
        // variable 3 is true at decision level 1 (encoded as level + 1).
        let assignments = vec![0, 1, -1, 2];
        assert!(clause_is_satisfied_at_root(&assignments, &[1, 3]));
        assert!(clause_is_satisfied_at_root(&assignments, &[-2]));
        assert!(!clause_is_satisfied_at_root(&assignments, &[3]));
        assert!(!clause_is_satisfied_at_root(&assignments, &[-1, 2]));
    }

    #[test]
    fn permanent_instance_collection_requires_every_clause_at_root() {
        let assignments = vec![0, 1, -1, 2];
        let permanent = QiCollectibleInstanceGroup {
            group_id: 1,
            clauses: vec![(10, vec![1, 3]), (11, vec![-2])],
        };
        let decision_dependent = QiCollectibleInstanceGroup {
            group_id: 2,
            clauses: vec![(12, vec![1]), (13, vec![3])],
        };

        assert!(instance_group_is_satisfied_at_root(
            &assignments,
            &permanent
        ));
        assert!(!instance_group_is_satisfied_at_root(
            &assignments,
            &decision_dependent
        ));
    }

    #[test]
    fn retired_clause_model_check_treats_missing_literals_as_unsatisfied() {
        let model = [0, 1, -1];
        assert!(clause_is_satisfied_by_model(&[1, 2], &model));
        assert!(!clause_is_satisfied_by_model(&[-1, 2], &model));
        assert!(!clause_is_satisfied_by_model(&[3], &model));
        assert!(!clause_is_satisfied_by_model(&[], &model));
    }
}
