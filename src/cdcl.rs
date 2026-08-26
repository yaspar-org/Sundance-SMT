// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Main CDCL decision loop
use crate::arithmetic::lp::ArithSolver;
use crate::cadical_propagator::{
    CustomExternalPropagator, EagerQiMode, QiGcLearner, QiGcState, init_qi_gc_trace,
};
use crate::debug_println;
use crate::egraphs::EgraphTrait;
use crate::proof::{SMTProofTracer, Theory};
use crate::solver_state::SolverState;
use crate::stats::SolverStats;
use crate::utils::DeterministicHashSet;
use cadical_sys::{CaDiCal, Status, Terminator};
use std::cell::RefCell;
use std::collections::HashMap;
use std::path::PathBuf;
use std::rc::Rc;
use std::time::Instant;
use yaspar_ir::ast::{FunctionMeta, Sig, SortDef, Str};

struct DeadlineTerminator {
    deadline: Instant,
}

impl Terminator for DeadlineTerminator {
    fn terminated(&mut self) -> bool {
        Instant::now() >= self.deadline
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

    let mut terminator = if timeout > 0 {
        Some(DeadlineTerminator {
            deadline: Instant::now() + std::time::Duration::from_secs(timeout),
        })
    } else {
        None
    };
    if let Some(ref mut t) = terminator {
        solver.connect_terminator(t);
    }

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
    let qi_gc_active = qi_gc && eager_qi == 0;
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
            learner_buf: Vec::new(),
            qi_clause_registry: HashMap::new(),
            qi_ancestry: HashMap::new(),
            used_qi_ids: std::collections::HashSet::new(),
            epoch: 0,
        }));
        proof_tracer.borrow_mut().qi_gc_state = Some(Rc::clone(&state));
        eprintln!("[qi-gc] epoch 0: new activation literal act={}", act_var);
        Some(state)
    } else {
        None
    };
    let mut qi_gc_learner = qi_gc_state
        .as_ref()
        .map(|s| QiGcLearner { state: Rc::clone(s) });
    if let Some(ref mut learner) = qi_gc_learner {
        solver.connect_learner(learner);
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
        draining_forgettable: false,
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

    debug_println!(2, 1, "All clauses added, starting solver");

    for clause in &boolean_dt_constraints {
        match clause.len() {
            0 | 1 => {}
            2 => propagator.stats.binary_clauses += 1,
            _ => propagator.stats.clauses += 1,
        }
    }

    let result = solve(&mut solver);

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
