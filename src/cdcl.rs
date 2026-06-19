// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Main CDCL decision loop
use crate::arithmetic::lp::ArithSolver;
use crate::cadical_propagator::CustomExternalPropagator;
use crate::debug_println;
use crate::egraphs::egraph::Egraph;
use crate::proof::{SMTProofTracer, Theory};
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
    egraph: &mut Egraph,
    clauses: Vec<Vec<i32>>,
    boolean_dt_constraints: Vec<Vec<i32>>,
    proof_file: Option<PathBuf>,
    sorts: HashMap<Str, SortDef>,
    symbol_table: HashMap<Str, Vec<(Sig, FunctionMeta)>>,
    arithmetic: ArithSolver,
    timeout: u64,
) -> (Status, SolverStats) {
    let mut solver = CaDiCal::new();

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

    let mut propagator = CustomExternalPropagator {
        decision_level: 0,
        egraph,
        disequalities: RefCell::new(vec![]),
        fixed_literals: DeterministicHashSet::default(),
        proof_tracer: Rc::clone(&proof_tracer), // Clone the Rc reference
        assignments: vec![0, 0],
        solver: &mut solver as *mut CaDiCal,
        arithmetic,
        stats: SolverStats::new(),
    };

    solver.connect_external_propagator(&mut propagator);
    // note: not using a fixed listener anymore
    // solver.connect_fixed_listener(&mut propagator);

    debug_println!(2, 0, "CDCL: Starting CDCL solver");
    debug_println!(1, 1, "Adding {} clauses to solver", clauses.len());

    // Add all clauses to the solver
    for (i, clause) in clauses.iter().enumerate() {
        debug_println!(11, 2, "Adding clause #{}: {:?}", i + 1, clause);
        add_clause_to_solver_and_to_proof(clause, &mut solver, proof_tracer.clone(), None);
        for lit in clause {
            // kind've annoying that I have to do this, but I don't think there is a better way
            solver.add_observed_var(i32::abs(*lit));
            debug_println!(0, 2, "Added observed variable: {}", i32::abs(*lit));
        }
    }

    // adding this into disequalities instead so that it appears as a theory lemma
    for clause in &boolean_dt_constraints {
        add_clause_to_solver_and_to_proof(
            clause,
            &mut solver,
            proof_tracer.clone(),
            Some(Theory::Datatypes),
        );
        for lit in clause {
            // kind've annoying that I have to do this, but I don't think there is a better way
            solver.add_observed_var(i32::abs(*lit));
            propagator.add_lit_to_proof_tracer(*lit); // todo: calling this in too many places, need to cut down
            debug_println!(0, 2, "Added observed variable: {}", i32::abs(*lit));
        }
    }

    debug_println!(2, 1, "All clauses added, starting solver");

    let result = solve(&mut solver);

    // Disconnect the proof tracer before dropping the propagator
    solver.disconnect_proof_tracer1();

    // Generate proof after all borrows are released
    let edrat_proof = proof_tracer.borrow_mut().generate_edrat();

    // Write proof to file if requested
    if let Some(p) = proof_file
        && result == Status::UNSATISFIABLE
    {
        if let Err(e) = std::fs::write(&p, edrat_proof) {
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
    (result, propagator.stats)
}

/// Adds the clause to the eDRAT proof and gives it to the CaDiCaL solver.
/// Notably, the clause is added to the proof *before* it is given to CaDiCaL.
/// If `theory` is `None`, the clause is treated as an original CNF clause.
///
/// During the development of eDRAT proof production in summer 2026,
/// we found that calling `.clause6()` causes CaDiCaL to immediately process
/// the clause. In some cases, CaDiCaL immediately deletes the clause
/// (such as when the clause is a tautology or when it is subsumed by some other
/// clause already in the solver), and this deletion leads to CaDiCaL invoking
/// its callback in `proof_tracer.rs`. As a result, the eDRAT proof would try
/// to delete a clause before it is introduced. This function adds the clause
/// to the proof before it is given to CaDiCaL to avoid this scenario.
fn add_clause_to_solver_and_to_proof(
    clause: &Vec<i32>,
    solver: &mut CaDiCal,
    proof_tracer: Rc<RefCell<SMTProofTracer>>,
    theory: Option<Theory>,
) {
    if let Some(theory) = theory {
        proof_tracer.borrow_mut().add_theory_clause(clause, theory);
    } else {
        proof_tracer.borrow_mut().add_original_clause(clause);
    }

    solver.clause6(clause); // TODO `clause1()`, `clause2()`, etc. might be more efficient
}

fn solve(solver: &mut CaDiCal) -> Status {
    solver.solve()
}
