// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Main CDCL decision loop
use crate::arithmetic::lp::ArithSolver;
use crate::cadical_propagator::{CustomExternalPropagator, EagerQiMode, QiLearner};
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
        qi_generation: 0,
        qi_activation_lit: 0,
        qi_activation_pending: false,
        qi_forgettable_queue: RefCell::new(vec![]),
        qi_learned_clauses: Rc::new(RefCell::new(Vec::new())),
    };

    solver.connect_external_propagator(&mut propagator);

    // Connect a Learner to capture conflict clauses for QI GC.
    let mut qi_learner = QiLearner::new(Rc::clone(&propagator.qi_learned_clauses));
    solver.connect_learner(&mut qi_learner);

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
