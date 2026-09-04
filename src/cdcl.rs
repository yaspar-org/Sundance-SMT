// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Main CDCL decision loop
use crate::arithmetic::lp::ArithSolver;
use crate::cadical_propagator::{
    CustomExternalPropagator, EagerQiMode, QiGcLearner, QiGcState, init_qi_gc_trace,
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
use std::collections::HashMap;
use std::path::PathBuf;
use std::rc::Rc;
use std::time::Instant;
use yaspar_ir::ast::{FunctionMeta, Sig, SortDef, Str};

struct DeadlineTerminator {
    deadline: Option<Instant>,
    qi_gc_rebuild_requested: Rc<Cell<bool>>,
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
        let act_var = solver_state.cnf_cache.next_var;
        solver_state.cnf_cache.next_var += 1;
        // add_observed_var is deferred to after connect_external_propagator
        let mut initial_activation_lits = std::collections::HashSet::new();
        initial_activation_lits.insert(act_var);
        let state = Rc::new(RefCell::new(QiGcState {
            current_act: act_var,
            activation_lits: initial_activation_lits,
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
            pending_retired_qi_clause_ids: std::collections::HashSet::new(),
            pending_retired_qi_clause_contents: Default::default(),
            total_physically_collected_qi_clauses: 0,
            total_physically_collected_qi_clause_ids: 0,
            total_physically_collected_qi_clause_contents: 0,
            retired_activations: std::collections::HashSet::new(),
            observed_retirement_units: std::collections::HashSet::new(),
            total_deleted_retired_activation_clauses: 0,
            collection_check_pending: false,
        }));
        proof_tracer.borrow_mut().qi_gc_state = Some(Rc::clone(&state));
        eprintln!("[qi-gc] epoch 0: new activation literal act={}", act_var);
        Some(state)
    } else {
        None
    };
    let mut qi_gc_learner = qi_gc_state.as_ref().map(|s| QiGcLearner {
        state: Rc::clone(s),
    });
    if let Some(ref mut learner) = qi_gc_learner {
        solver.connect_learner(learner);
    }

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
        forgettable_queue: Vec::new(),
        active_forgettable_clauses: Vec::new(),
        rebuild_learned_clauses: Vec::new(),
        draining_forgettable: false,
        next_is_decision: false,
        qi_gc_force_backtrack: false,
        qi_gc_transition_pending: false,
        qi_gc_rebuild_requested: qi_gc_active.then(|| Rc::clone(&qi_gc_rebuild_requested)),
        qi_gc_root_replay: Vec::new(),
        qi_gc_root_replay_pending: 0,
        qi_gc_phase_hints: vec![0, 0],
        theory_processed_levels: vec![None, None],
        pending_relevant_assignments: std::collections::VecDeque::new(),
        theory_assignment_pending: vec![false, false],
        relevancy_level,
    };

    solver.connect_external_propagator(&mut propagator);
    // note: not using a fixed listener anymore
    // solver.connect_fixed_listener(&mut propagator);

    // Observe the activation literal AFTER the propagator is connected.
    if let Some(ref gc) = propagator.qi_gc_state {
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

        rebuild_cadical_after_qi_gc(
            &mut solver,
            &mut propagator,
            &proof_tracer,
            terminator.as_mut(),
            qi_gc_learner.as_mut(),
        );
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

fn rebuild_cadical_after_qi_gc(
    solver: &mut CaDiCal,
    propagator: &mut CustomExternalPropagator<'_>,
    proof_tracer: &Rc<RefCell<SMTProofTracer>>,
    terminator: Option<&mut DeadlineTerminator>,
    learner: Option<&mut QiGcLearner>,
) {
    let started = Instant::now();
    let old_vars = solver.vars();
    let old_active = solver.active();
    let old_irredundant = solver.irredundant();
    let old_redundant = solver.redundant();
    let pending_retired_qi = propagator.qi_gc_state.as_ref().map_or(0, |gc| {
        gc.borrow()
            .pending_retired_qi_clause_contents
            .values()
            .sum::<usize>()
    });
    let queued_retired_activation_clauses = propagator.queued_retired_activation_clauses();
    assert_eq!(
        queued_retired_activation_clauses, 0,
        "SAT rebuild queue still contains clauses from a retired activation epoch"
    );

    let root_units = propagator.prepare_for_solver_rebuild();

    // CaDiCaL's copy operation only transfers irredundant clauses. Disconnect
    // callbacks first so the source can be dropped after the copy without
    // retaining stale raw pointers. Root assignments that were represented
    // only by learned units are added explicitly below.
    solver.disconnect_external_propagator();
    if learner.is_some() {
        solver.disconnect_learner();
    }
    if terminator.is_some() {
        solver.disconnect_terminator();
    }
    solver.disconnect_proof_tracer1();

    let mut copied = ClauseCollector::default();
    assert!(solver.traverse_clauses(&mut copied));

    let mut fresh = CaDiCal::new();
    {
        let mut tracer = proof_tracer.borrow_mut();
        for clause in &copied.clauses {
            tracer.register_clause_for_cadical_callback(clause);
        }
        for &unit in &root_units {
            tracer.register_clause_for_cadical_callback(&[unit]);
        }
        fresh.connect_proof_tracer1(&mut *tracer, true);
    }
    CaDiCal::copy(solver, &mut fresh);
    for &unit in &root_units {
        fresh.clause6(&[unit]);
    }
    let replayed_phases = propagator.replay_sat_phase_hints(&mut fresh);

    if let Some(terminator) = terminator {
        fresh.connect_terminator(terminator);
    }
    if let Some(learner) = learner {
        fresh.connect_learner(learner);
    }
    fresh.connect_external_propagator(propagator);

    *solver = fresh;
    propagator.attach_rebuilt_solver(solver);

    if let Some(gc) = &propagator.qi_gc_state {
        let mut gc = gc.borrow_mut();
        let collected_ids = gc.pending_retired_qi_clause_ids.len();
        let collected_contents = gc
            .pending_retired_qi_clause_contents
            .values()
            .sum::<usize>();
        gc.total_physically_collected_qi_clauses += collected_ids.max(collected_contents) as u64;
        gc.total_physically_collected_qi_clause_ids += collected_ids as u64;
        gc.total_physically_collected_qi_clause_contents += collected_contents as u64;
        gc.pending_retired_qi_clause_ids.clear();
        gc.pending_retired_qi_clause_contents.clear();
    }

    let new_vars = solver.vars();
    let new_active = solver.active();
    let new_irredundant = solver.irredundant();
    let new_redundant = solver.redundant();
    eprintln!(
        "[qi-gc-profile] sat-rebuild duration={:.6}s copied_irredundant={} root_units={} \
         vars_before={} vars_after={} active_before={} active_after={} \
         irredundant_before={} irredundant_after={} redundant_before={} redundant_after={} \
         replay_forgettable={} replay_learned={} replay_permanent={} replayed_phases={} \
         queued_retired_activation_clauses={} \
         reclaimed_retired_qi={}",
        started.elapsed().as_secs_f64(),
        copied.clauses.len(),
        root_units.len(),
        old_vars,
        new_vars,
        old_active,
        new_active,
        old_irredundant,
        new_irredundant,
        old_redundant,
        new_redundant,
        propagator.active_forgettable_clauses.len(),
        propagator.rebuild_learned_clauses.len(),
        propagator.disequalities.borrow().len(),
        replayed_phases,
        queued_retired_activation_clauses,
        pending_retired_qi,
    );
}
