// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Main CDCL decision loop
use crate::arithmetic::lp::ArithSolver;
use crate::cadical_propagator::{
    CustomExternalPropagator, EagerQiMode, QiGcLearner, QiGcState, init_qi_gc_trace,
    qi_gc_profile_enabled,
};
use crate::config::RelevancyLevel;
use crate::debug_println;
use crate::egraphs::EgraphTrait;
use crate::proof::{SMTProofTracer, Theory};
use crate::solver_state::SolverState;
use crate::stats::SolverStats;
use crate::utils::DeterministicHashSet;
use cadical_sys::{CaDiCal, ClauseIterator, Status, Terminator};
use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::path::PathBuf;
use std::rc::Rc;
use std::time::Instant;
use yaspar_ir::ast::{FunctionMeta, Sig, SortDef, Str};

struct DeadlineTerminator {
    deadline: Option<Instant>,
    qi_gc_rebuild_requested: Rc<Cell<bool>>,
}

#[derive(Default)]
struct ClauseCollector {
    clauses: Vec<Vec<i32>>,
}

impl ClauseIterator for ClauseCollector {
    fn clause(&mut self, clause: &[i32]) -> bool {
        self.clauses.push(clause.to_vec());
        true
    }
}

impl Terminator for DeadlineTerminator {
    fn terminated(&mut self) -> bool {
        self.qi_gc_rebuild_requested.get()
            || self
                .deadline
                .is_some_and(|deadline| Instant::now() >= deadline)
    }
}

impl DeadlineTerminator {
    fn timed_out(&self) -> bool {
        self.deadline
            .is_some_and(|deadline| Instant::now() >= deadline)
    }
}

/// Main CDCL decision loop
///
/// todo: reduce the number of arguments
#[allow(clippy::too_many_arguments)]
pub fn cdcl_decision_procedure(
    solver_state: &mut SolverState,
    clauses: Vec<Vec<i32>>,
    boolean_dt_constraints: Vec<Vec<i32>>,
    proof_file: Option<PathBuf>,
    partial_proof_file: Option<PathBuf>,
    trail_file: Option<PathBuf>,
    sorts: HashMap<Str, SortDef>,
    symbol_table: HashMap<Str, Vec<(Sig, FunctionMeta)>>,
    arithmetic: ArithSolver,
    timeout: u64,
    elevate: i32,
    max_arith_conflicts_per_round: usize,
    batch_cap: usize,
    eager_qi: i32,
    qi_gc: bool,
    relevancy_level: RelevancyLevel,
) -> (Status, SolverStats) {
    let mut solver = CaDiCal::new();
    assert!(
        solver.set("elevate".to_string(), elevate),
        "CaDiCaL option 'elevate' is unavailable; Sundance requires the cadical-sys elevate fork for lazy quantifier instantiation"
    );

    // Create proof tracker for real-time proof tracking wrapped in Rc<RefCell<>>
    // todo: for right now always have hid_quantifiers to be true, need to change this
    let proof_tracer = Rc::new(RefCell::new(SMTProofTracer::new(sorts, symbol_table)));

    // Connect the proof tracer (must be done in CONFIGURING state)
    solver.connect_proof_tracer1(&mut *proof_tracer.borrow_mut(), true); // true for antecedents

    #[cfg(feature = "z3-solver")]
    let using_z3_incremental = matches!(arithmetic, ArithSolver::Z3Incremental);
    #[cfg(not(feature = "z3-solver"))]
    let using_z3_incremental = false;
    solver_state
        .egraph
        .incremental_arithmetic(using_z3_incremental);

    #[cfg(feature = "z3-solver")]
    let z3_incremental =
        using_z3_incremental.then(crate::arithmetic::z3incremental::Z3IncrementalState::new);

    // --- QI Garbage Collection setup ---
    // Only active with lazy QI (eager_qi == 0) and when qi_gc is enabled.
    init_qi_gc_trace();
    crate::relevancy::init_relevancy_trace();
    let qi_gc_active = qi_gc && eager_qi == 0;
    let qi_gc_rebuild_requested = Rc::new(Cell::new(false));
    let mut terminator = (timeout > 0 || qi_gc_active).then(|| DeadlineTerminator {
        deadline: (timeout > 0).then(|| Instant::now() + std::time::Duration::from_secs(timeout)),
        qi_gc_rebuild_requested: Rc::clone(&qi_gc_rebuild_requested),
    });
    if let Some(ref mut t) = terminator {
        solver.connect_terminator(t);
    }
    let qi_gc_state: Option<Rc<RefCell<QiGcState>>> = if qi_gc_active {
        let state = Rc::new(RefCell::new(QiGcState {
            // Targeted clause-ID collection propagates dependency through
            // proof antecedents and does not inject a SAT selector.
            current_act: 0,
            activation_lits: std::collections::HashSet::new(),
            learned_clauses: Vec::new(),
            safe_learned_clauses: Vec::new(),
            learner_buf: Vec::new(),
            epoch: 0,
            epoch_guarded_clauses: 0,
            total_guarded_clauses: 0,
            epoch_instantiations: 0,
            total_epoch_instantiations: 0,
            transitions: 0,
            tracker: Default::default(),
            total_retained_qi_clauses: 0,
            total_retired_qi_clauses: 0,
            total_promoted_derived_clauses: 0,
            total_retired_terms: 0,
            total_retired_sat_vars: 0,
            pending_unobserve_sat_vars: Default::default(),
            total_unobserved_sat_vars: 0,
            pending_retired_qi_clause_ids: std::collections::HashSet::new(),
            pending_retired_qi_clause_contents: Default::default(),
            pending_retired_qi_group_ids: Default::default(),
            total_physically_collected_qi_clauses: 0,
            total_physically_collected_qi_clause_ids: 0,
            total_physically_collected_qi_clause_contents: 0,
            total_naturally_compacted_qi_clauses: 0,
            total_targeted_compacted_qi_clauses: 0,
            total_compacted_qi_groups: 0,
            total_removed_qi_groups: 0,
            pending_requested_theory_clause_ids: std::collections::HashSet::new(),
            total_requested_theory_clauses: 0,
            total_physically_collected_theory_clauses: 0,
            total_reclaimed_qi_instances: 0,
            total_permanently_satisfied_qi_instances: 0,
            retired_qi_instances: Vec::new(),
            compact_qi_obligations: Default::default(),
            total_resurrected_qi_instances: 0,
            total_gc_protected_qi_instances: 0,
            retired_activations: std::collections::HashSet::new(),
            observed_retirement_units: std::collections::HashSet::new(),
            total_deleted_retired_activation_clauses: 0,
            in_search_collection_started: None,
            in_search_collection_expected_qi_clauses: 0,
            targeted_term_gc_pending: false,
            total_predecessor_compactions: 0,
            total_predecessor_entries_removed: 0,
            collection_check_pending: false,
            theory_clauses_by_kind: [0; 7],
            theory_clauses_touching_epoch_terms_by_kind: [0; 7],
            newly_pinned_epoch_term_references_by_kind: [0; 7],
            theory_unit_clauses_by_kind: [0; 7],
            theory_unit_clauses_touching_epoch_terms_by_kind: [0; 7],
            newly_pinned_epoch_term_references_from_units_by_kind: [0; 7],
            theory_empty_clauses_by_kind: [0; 7],
            datatype_clauses_by_origin: [0; 3],
            datatype_units_by_origin: [0; 3],
            datatype_epoch_units_by_origin: [0; 3],
            deduplicated_theory_units_by_kind: [0; 7],
            deduplicated_datatype_units_by_origin: [0; 3],
            datatype_unit_literals: Default::default(),
            datatype_epoch_unit_literals: Default::default(),
            rebuild_learned_term_uids: Default::default(),
        }));
        proof_tracer.borrow_mut().qi_gc_state = Some(Rc::clone(&state));
        eprintln!("[qi-gc] epoch 0: targeted unguarded QI collection");
        Some(state)
    } else {
        None
    };
    // Exact proof antecedents replace syntactic selector-taint tracking.
    let mut qi_gc_learner: Option<QiGcLearner> = None;

    // Relevancy filtering: initialize purely from pre-NNF assertions. Any
    // theory-generated terms (datatype axioms, QI, trichotomy) register
    // themselves via `relevancy_register_term` at the point of generation,
    // so no var_map-scanning fallback is needed.
    if relevancy_level.is_enabled() {
        use crate::egraphs::EgraphTrait;
        solver_state.egraph.set_track_all_merges(true);
        solver_state.relevancy_initialize_from_assertions();
        let root_lits: Vec<i32> = clauses
            .iter()
            .chain(boolean_dt_constraints.iter())
            .filter(|c| c.len() == 1)
            .map(|c| c[0])
            .collect();
        for lit in &root_lits {
            solver_state.mark_lit_relevant(*lit, 0);
        }
    }

    let mut propagator = CustomExternalPropagator {
        decision_level: 0,
        solver_state,
        disequalities: RefCell::new(vec![]),
        fixed_literals: DeterministicHashSet::default(),
        proof_tracer: Rc::clone(&proof_tracer), // Clone the Rc reference
        assignments: vec![0, 0],
        solver: &mut solver as *mut CaDiCal,
        arithmetic,
        stats: SolverStats::new(),
        pending: None,
        eager_qi: EagerQiMode::new(eager_qi),
        eager_original_vars: vec![false, false],
        unassigned_eager_original_vars: 0,
        eager_attempted_since_model: false,
        materializing_quantifiers: false,
        max_arith_conflicts_per_round,
        last_observed_var: 1,
        batch_cap,
        #[cfg(feature = "z3-solver")]
        z3_incremental,
        trail_writer: trail_file
            .as_ref()
            .and_then(|p| match std::fs::File::create(p) {
                Ok(f) => Some(std::io::BufWriter::new(f)),
                Err(e) => {
                    debug_println!(2, 0, "Failed to open trail log {}: {}", p.display(), e);
                    None
                }
            }),
        trail_atoms: std::collections::HashMap::new(),
        qi_gc_state,
        queued_theory_unit_literals: RefCell::new(Default::default()),
        forgettable_queue: Vec::new(),
        active_forgettable_clauses: Vec::new(),
        rebuild_learned_clauses: Vec::new(),
        rebuild_learned_clause_terms: Default::default(),
        draining_forgettable: false,
        next_is_decision: false,
        qi_gc_force_backtrack: false,
        qi_gc_transition_pending: false,
        qi_gc_rebuild_requested: qi_gc_active.then(|| Rc::clone(&qi_gc_rebuild_requested)),
        qi_gc_maintenance_in_progress: false,
        qi_gc_preserved_root_assignments: Vec::new(),
        qi_gc_phase_hints: vec![0, 0],
        theory_processed_levels: vec![None, None],
        pending_relevant_assignments: std::collections::VecDeque::new(),
        theory_assignment_pending: vec![false, false],
        relevancy_level,
    };

    solver.connect_external_propagator(&mut propagator);
    // note: not using a fixed listener anymore
    // solver.connect_fixed_listener(&mut propagator);

    // Selector-based epochs still support observation for the legacy
    // transition path, but targeted collection uses no selector.
    if let Some(ref gc) = propagator.qi_gc_state
        && gc.borrow().current_act != 0
    {
        solver.add_observed_var(gc.borrow().current_act);
    }

    debug_println!(2, 0, "CDCL: Starting CDCL solver");
    debug_println!(1, 1, "Adding {} clauses to solver", clauses.len());

    // Add all clauses to the solver
    for (i, clause) in clauses.iter().enumerate() {
        debug_println!(11, 2, "Adding clause #{}: {:?}", i + 1, clause);
        add_clause_to_proof_and_solver(clause, &mut solver, &proof_tracer, None);
    }

    // adding this into disequalities instead so that it appears as a theory lemma
    for clause in &boolean_dt_constraints {
        add_clause_to_proof_and_solver(clause, &mut solver, &proof_tracer, Some(Theory::Datatypes));
    }

    // Observe all known CNF variables at startup
    propagator.sync_new_vars();
    propagator.mark_current_vars_as_eager_originals();

    debug_println!(2, 1, "All clauses added, starting solver");

    for clause in &boolean_dt_constraints {
        match clause.len() {
            0 | 1 => {}
            2 => propagator.stats.binary_clauses += 1,
            _ => propagator.stats.clauses += 1,
        }
    }

    let result = loop {
        let result = solve(&mut solver);
        let rebuild_requested = qi_gc_rebuild_requested.replace(false);
        if result != Status::UNKNOWN
            || !rebuild_requested
            || terminator
                .as_ref()
                .is_some_and(DeadlineTerminator::timed_out)
        {
            break result;
        }

        let maintenance_result = rebuild_cadical_after_qi_gc(
            &mut solver,
            &mut propagator,
            &proof_tracer,
            terminator.as_mut(),
            qi_gc_learner.as_mut(),
            elevate,
        );
        if maintenance_result != Status::UNKNOWN {
            break maintenance_result;
        }
    };

    // Disconnect the learner before dropping the propagator
    if qi_gc_learner.is_some() {
        solver.disconnect_learner();
    }

    // Disconnect the proof tracer before dropping the propagator
    solver.disconnect_proof_tracer1();

    // Generate proof after all borrows are released
    let edrat_proof = proof_tracer.borrow_mut().generate_edrat();

    // Write proof to file if requested
    if let Some(p) = proof_file
        && result == Status::UNSATISFIABLE
    {
        if let Err(e) = std::fs::write(&p, &edrat_proof) {
            debug_println!(
                2,
                0,
                "Failed to write eDRAT proof to {}: {}",
                p.display(),
                e
            );
        } else {
            debug_println!(2, 0, "eDRAT proof written to: {}", p.display());
        }
    }

    if let Some(p) = partial_proof_file {
        write_partial_proof(&p, result, &edrat_proof);
    }

    // Trails were streamed during the solve; append the now-complete atom map.
    if trail_file.is_some() {
        propagator.finish_trail_log();
        debug_println!(2, 0, "trail log written");
    }

    // Harvest stats from solver_state, egraph, and proof tracer
    propagator.sync_external_stats();
    propagator.stats.finish();
    (result, propagator.stats)
}

/// Dump the eDRAT proof forest for any result: complete on unsat, else a prefix
/// with no final empty clause. A leading `;` comment records which case it is.
/// Header status: unsat -> unsat, sat -> unknown, unknown (cadical) ->
/// timeout/interrupt.
fn write_partial_proof(path: &std::path::Path, result: Status, edrat_proof: &str) {
    let complete = result == Status::UNSATISFIABLE;
    let status = match result {
        Status::UNSATISFIABLE => "unsat",
        Status::SATISFIABLE => "unknown",
        Status::UNKNOWN => "timeout/interrupt",
    };
    let header = if complete {
        "; COMPLETE eDRAT proof (result: unsat): a checkable refutation.\n".to_string()
    } else {
        format!(
            "; PARTIAL eDRAT proof (result: {status}): every step derived so far,\n\
             ; but NO final empty clause -- a prefix, not a checkable refutation.\n"
        )
    };
    if let Err(e) = std::fs::write(path, format!("{header}{edrat_proof}")) {
        debug_println!(
            2,
            0,
            "Failed to write partial proof to {}: {}",
            path.display(),
            e
        );
    } else {
        debug_println!(
            2,
            0,
            "{} proof forest written to: {}",
            if complete { "Complete" } else { "Partial" },
            path.display()
        );
    }
}

/// Records a clause before CaDiCaL can synchronously simplify or delete it.
/// A missing `theory` denotes an original CNF clause.
fn add_clause_to_proof_and_solver(
    clause: &[i32],
    solver: &mut CaDiCal,
    proof_tracer: &RefCell<SMTProofTracer>,
    theory: Option<Theory>,
) {
    {
        let mut proof_tracer = proof_tracer.borrow_mut();
        if let Some(theory) = theory {
            proof_tracer.add_theory_clause(clause, theory);
        } else {
            proof_tracer.add_original_clause(clause);
        }
        proof_tracer.register_clause_for_cadical_callback(clause);
    }

    solver.clause6(clause); // TODO `clause1()`, `clause2()`, etc. might be more efficient
}

fn solve(solver: &mut CaDiCal) -> Status {
    solver.solve()
}

fn pending_retired_qi_clause_histogram(
    propagator: &CustomExternalPropagator<'_>,
) -> BTreeMap<usize, usize> {
    let mut histogram = BTreeMap::new();
    if let Some(gc) = &propagator.qi_gc_state {
        for (clause, count) in &gc.borrow().pending_retired_qi_clause_contents {
            *histogram.entry(clause.len()).or_default() += count;
        }
    }
    histogram
}

fn normalize_clause(clause: &[i32]) -> Vec<i32> {
    let mut normalized = clause.to_vec();
    normalized.sort_unstable();
    normalized.dedup();
    normalized
}

fn rebuild_cadical_after_qi_gc(
    solver: &mut CaDiCal,
    propagator: &mut CustomExternalPropagator<'_>,
    proof_tracer: &Rc<RefCell<SMTProofTracer>>,
    terminator: Option<&mut DeadlineTerminator>,
    learner: Option<&mut QiGcLearner>,
    elevate: i32,
) -> Status {
    let started = Instant::now();
    let old_vars = solver.vars();
    let old_active = solver.active();
    let old_irredundant = solver.irredundant();
    let old_redundant = solver.redundant();
    let pending_before = propagator.qi_gc_state.as_ref().map_or(0, |gc| {
        gc.borrow()
            .pending_retired_qi_clause_contents
            .values()
            .sum::<usize>()
    });
    let pending_histogram_before = pending_retired_qi_clause_histogram(propagator);
    let queued_before = propagator.queued_retired_activation_clauses();
    assert_eq!(
        pending_before, 0,
        "SAT rebuild started before targeted QI clause collection completed"
    );

    propagator.begin_qi_gc_maintenance();
    let mut root_units = propagator.prepare_for_solver_rebuild();
    propagator.run_targeted_qi_term_gc_during_maintenance();
    root_units.retain(|lit| {
        !propagator.solver_state.is_retired_sat_var(*lit)
            || propagator.solver_state.is_retired_sat_only_var(*lit)
    });
    let retired_sat_vars_before_ownership =
        propagator.qi_gc_state.as_ref().map_or_else(Vec::new, |gc| {
            let mut vars: Vec<i32> = gc
                .borrow()
                .pending_unobserve_sat_vars
                .iter()
                .copied()
                .collect();
            vars.sort_unstable();
            vars
        });
    assert!(
        !retired_sat_vars_before_ownership.is_empty(),
        "SAT rebuild requested without any retired SAT variables"
    );
    let replay_source_clauses = propagator.active_forgettable_clauses.clone();
    let replay_learned_clauses = propagator.rebuild_learned_clauses.clone();
    let source_shape_counts: HashMap<Vec<i32>, usize> =
        replay_source_clauses
            .iter()
            .fold(HashMap::new(), |mut counts, clause| {
                *counts.entry(normalize_clause(clause)).or_default() += 1;
                counts
            });
    let source_shapes: HashSet<Vec<i32>> = source_shape_counts.keys().cloned().collect();

    solver.disconnect_external_propagator();
    if learner.is_some() {
        solver.disconnect_learner();
    }
    if terminator.is_some() {
        solver.disconnect_terminator();
    }
    solver.disconnect_proof_tracer1();

    let snapshot_started = Instant::now();
    let mut snapshot = ClauseCollector::default();
    assert!(solver.traverse_clauses(&mut snapshot));
    let snapshot_duration = snapshot_started.elapsed();

    let mut remaining_source_counts = source_shape_counts;
    let mut retained_snapshot = Vec::new();
    let mut filtered_retired_clauses = 0usize;
    let mut filtered_retired_units = 0usize;
    let mut filtered_retired_literals = 0usize;
    let mut filtered_source_clauses = 0usize;
    for clause in snapshot.clauses {
        let key = normalize_clause(&clause);
        if let Some(count) = remaining_source_counts.get_mut(&key)
            && *count != 0
        {
            *count -= 1;
            filtered_source_clauses += 1;
            continue;
        }

        let retired_literals = clause
            .iter()
            .filter(|lit| propagator.solver_state.is_retired_sat_var(**lit))
            .count();
        if retired_literals != 0 {
            filtered_retired_clauses += 1;
            filtered_retired_literals += retired_literals;
            if clause.len() == 1 {
                filtered_retired_units += 1;
            }
            continue;
        }
        retained_snapshot.push(clause);
    }
    let source_clauses_absent_from_snapshot =
        remaining_source_counts.values().copied().sum::<usize>();

    let mut fresh = CaDiCal::new();
    assert!(
        fresh.set("elevate".to_string(), elevate),
        "CaDiCaL option 'elevate' is unavailable during SAT rebuild"
    );

    let mut replayed_clause_shapes = HashSet::new();
    let mut replay_clauses = Vec::new();
    let mut replayed_snapshot = 0usize;
    let mut deduplicated_snapshot = 0usize;
    for clause in retained_snapshot {
        if replayed_clause_shapes.insert(normalize_clause(&clause)) {
            replay_clauses.push(clause);
            replayed_snapshot += 1;
        } else {
            deduplicated_snapshot += 1;
        }
    }
    let mut replayed_learned = 0usize;
    let mut skipped_learned_source_duplicates = 0usize;
    let mut deduplicated_learned = 0usize;
    for clause in replay_learned_clauses {
        let key = normalize_clause(&clause);
        if source_shapes.contains(&key) {
            skipped_learned_source_duplicates += 1;
        } else if replayed_clause_shapes.insert(key) {
            replay_clauses.push(clause);
            replayed_learned += 1;
        } else {
            deduplicated_learned += 1;
        }
    }

    let learned_ownership = propagator.register_replayed_learned_clause_ownership(&replay_clauses);
    let retired_sat_var_set =
        DeterministicHashSet::from_iter(retired_sat_vars_before_ownership.iter().copied());
    let ownership_rebuild = propagator
        .qi_gc_state
        .as_ref()
        .map_or_else(Default::default, |gc| {
            gc.borrow_mut()
                .tracker
                .rekey_permanent_clause_ownership_for_solver_rebuild(
                    &replay_clauses,
                    &propagator.assignments,
                    &retired_sat_var_set,
                )
        });

    // Clause-ID ownership is assigned only when the fresh solver replays each
    // clause. Hold the complete theory-term closure of that replay across the
    // post-ownership GC pass so no still-referenced theory variable can be
    // retired in the gap between constructing the replay and its callbacks.
    let mut replay_term_uids = DeterministicHashSet::default();
    propagator
        .solver_state
        .collect_clause_theory_term_closure(&replay_clauses, &mut replay_term_uids);
    propagator
        .solver_state
        .collect_clause_theory_term_closure(&replay_source_clauses, &mut replay_term_uids);
    let root_unit_clauses: Vec<Vec<i32>> = root_units.iter().map(|lit| vec![*lit]).collect();
    propagator
        .solver_state
        .collect_clause_theory_term_closure(&root_unit_clauses, &mut replay_term_uids);
    if let Some(gc) = &propagator.qi_gc_state {
        gc.borrow_mut()
            .rebuild_learned_term_uids
            .extend(replay_term_uids.iter().copied());
    }

    // Re-keying releases the old solver's absent clause owners. Collect terms
    // exposed by that release before attaching the fresh solver, so a large
    // rebuild is not immediately followed by a second tiny rebuild.
    propagator.run_targeted_qi_term_gc_during_maintenance();
    assert!(
        replay_clauses.iter().all(|clause| clause.iter().all(|lit| {
            !propagator.solver_state.is_retired_sat_var(*lit)
                || propagator.solver_state.is_retired_sat_only_var(*lit)
        })),
        "post-ownership term GC retired a theory SAT variable used by the replay"
    );
    if let Some(gc) = &propagator.qi_gc_state {
        gc.borrow_mut().rebuild_learned_term_uids.clear();
    }
    root_units.retain(|lit| {
        !propagator.solver_state.is_retired_sat_var(*lit)
            || propagator.solver_state.is_retired_sat_only_var(*lit)
    });
    let mut replayed_root_units = 0usize;
    let mut deduplicated_root_units = 0usize;
    for unit in &root_units {
        let clause = vec![*unit];
        if replayed_clause_shapes.insert(clause.clone()) {
            replay_clauses.push(clause);
            replayed_root_units += 1;
        } else {
            deduplicated_root_units += 1;
        }
    }

    let retired_sat_vars = propagator.qi_gc_state.as_ref().map_or_else(Vec::new, |gc| {
        let mut vars: Vec<i32> = gc
            .borrow()
            .pending_unobserve_sat_vars
            .iter()
            .copied()
            .collect();
        vars.sort_unstable();
        vars
    });
    let post_ownership_retired_sat_vars = retired_sat_vars
        .len()
        .saturating_sub(retired_sat_vars_before_ownership.len());

    {
        let mut tracer = proof_tracer.borrow_mut();
        for clause in &replay_clauses {
            tracer.register_clause_for_cadical_callback(clause);
        }
        fresh.connect_proof_tracer1(&mut *tracer, true);
    }
    *solver = fresh;
    propagator.attach_rebuilt_solver(solver);
    if let Some(terminator) = terminator {
        solver.connect_terminator(terminator);
    }
    if let Some(learner) = learner {
        solver.connect_learner(learner);
    }
    solver.connect_external_propagator(propagator);
    let replay_started = Instant::now();
    for clause in &replay_clauses {
        solver.clause6(clause);
    }
    let replay_duration = replay_started.elapsed();
    let replayed_phases = propagator.replay_sat_phase_hints(solver);
    let pending_permanent_owners_after_replay = propagator.qi_gc_state.as_ref().map_or(0, |gc| {
        gc.borrow().tracker.profile().pending_permanent_clauses
    });

    propagator
        .queued_theory_unit_literals
        .borrow_mut()
        .retain(|lit| !propagator.solver_state.is_retired_sat_var(*lit));
    if let Some(gc) = &propagator.qi_gc_state {
        let mut gc = gc.borrow_mut();
        for var in &retired_sat_vars {
            gc.pending_unobserve_sat_vars.remove(var);
        }
        gc.total_unobserved_sat_vars += retired_sat_vars.len() as u64;
        gc.pending_retired_qi_clause_ids.clear();
        gc.pending_retired_qi_clause_contents.clear();
        gc.pending_requested_theory_clause_ids.clear();
    }

    let pending_after = propagator.qi_gc_state.as_ref().map_or(0, |gc| {
        gc.borrow()
            .pending_retired_qi_clause_contents
            .values()
            .sum::<usize>()
    });
    let pending_histogram_after = pending_retired_qi_clause_histogram(propagator);
    let queued_after = propagator.queued_retired_activation_clauses();

    let new_vars = solver.vars();
    let new_active = solver.active();
    let new_irredundant = solver.irredundant();
    let new_redundant = solver.redundant();
    if qi_gc_profile_enabled() {
        eprintln!(
            "[qi-gc-profile] sat-rebuild maintenance_duration={:.6}s \
             snapshot_duration={:.6}s replay_duration={:.6}s \
             vars_before={} vars_after={} active_before={} active_after={} \
             irredundant_before={} irredundant_after={} redundant_before={} redundant_after={} \
             retired_sat_vars={} post_ownership_retired_sat_vars={} \
             snapshot_clauses={} replayed_snapshot={} \
             filtered_retired_clauses={} filtered_retired_units={} \
             filtered_retired_literals={} filtered_source_clauses={} \
             replay_source_clauses={} source_clauses_absent_from_snapshot={} \
             replayed_learned={} skipped_learned_source_duplicates={} \
             replayed_root_units={} deduplicated_snapshot={} \
             deduplicated_learned={} deduplicated_root_units={} replayed_phases={} \
             queued_retired_before={} queued_retired_after={} \
             pending_retired_before={} pending_retired_after={} reclaimed_retired_qi={} \
             permanent_owners_before={} rekeyed_permanent_owners={} \
             rekeyed_permanent_clause_shapes={} dropped_permanent_owners={} \
             rekeyed_permanent_term_uids={} pending_permanent_owners_before_replay={} \
             pending_permanent_owners_after_replay={} \
             learned_owner_candidates={} replayed_learned_owners={} \
             dropped_learned_owners={} replayed_learned_term_uids={} \
             pending_size_histogram_before={:?} pending_size_histogram_after={:?}",
            started.elapsed().as_secs_f64(),
            snapshot_duration.as_secs_f64(),
            replay_duration.as_secs_f64(),
            old_vars,
            new_vars,
            old_active,
            new_active,
            old_irredundant,
            new_irredundant,
            old_redundant,
            new_redundant,
            retired_sat_vars.len(),
            post_ownership_retired_sat_vars,
            replayed_snapshot
                + deduplicated_snapshot
                + filtered_retired_clauses
                + filtered_source_clauses,
            replayed_snapshot,
            filtered_retired_clauses,
            filtered_retired_units,
            filtered_retired_literals,
            filtered_source_clauses,
            replay_source_clauses.len(),
            source_clauses_absent_from_snapshot,
            replayed_learned,
            skipped_learned_source_duplicates,
            replayed_root_units,
            deduplicated_snapshot,
            deduplicated_learned,
            deduplicated_root_units,
            replayed_phases,
            queued_before,
            queued_after,
            pending_before,
            pending_after,
            pending_before.saturating_sub(pending_after),
            ownership_rebuild.live_owners_before,
            ownership_rebuild.rekeyed_owners,
            ownership_rebuild.rekeyed_clause_shapes,
            ownership_rebuild.dropped_owners,
            ownership_rebuild.rekeyed_term_uids,
            ownership_rebuild.pending_owners_after,
            pending_permanent_owners_after_replay,
            learned_ownership.candidate_clause_shapes,
            learned_ownership.replayed_clause_shapes,
            learned_ownership.dropped_clause_shapes,
            learned_ownership.replayed_term_uids,
            pending_histogram_before,
            pending_histogram_after,
        );
    }
    propagator.finish_qi_gc_maintenance();
    Status::UNKNOWN
}
