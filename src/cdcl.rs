//! Main CDCL decision loop
use crate::arithmetic::lp::ArithSolver;
use crate::cadical_propagator::CustomExternalPropagator;
use crate::egraphs::egraph::Egraph;
use crate::proof::proof_tracer::SMTProofTracker;
use crate::utils::DeterministicHashSet;
use cadical_sys::{CaDiCal, Status};
use std::cell::RefCell;
use std::collections::HashMap;
use std::path::PathBuf;
use std::rc::Rc;
use yaspar_ir::ast::{FunctionMeta, Sig, SortDef, Str};

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
    _timeout: u64, // todo: add timeout functionality
) -> Status {
    let mut solver = CaDiCal::new();

    // Create proof tracker for real-time proof tracking wrapped in Rc<RefCell<>>
    // todo: for right now always have hid_quantifiers to be true, need to change this
    let proof_tracker = Rc::new(RefCell::new(SMTProofTracker::new(sorts, symbol_table)));

    // Connect the proof tracer (must be done in CONFIGURING state)
    solver.connect_proof_tracer1(&mut *proof_tracker.borrow_mut(), true); // true for antecedents

    let mut propagator = CustomExternalPropagator {
        decision_level: 0,
        egraph,
        disequalities: RefCell::new(vec![]),
        fixed_literals: DeterministicHashSet::default(),
        proof_tracker: Rc::clone(&proof_tracker), // Clone the Rc reference
        assignments: vec![0, 0],
        solver: &mut solver as *mut CaDiCal,
        arithmetic,
    };

    solver.connect_external_propagator(&mut propagator);
    // note: not using a fixed listenere anymore
    // solver.connect_fixed_listener(&mut propagator);

    debug_println!(2, 0, "CDCL: Starting CDCL solver");
    debug_println!(1, 1, "Adding {} clauses to solver", clauses.len());

    // Add all clauses to the solver
    for (i, clause) in clauses.iter().enumerate() {
        debug_println!(11, 2, "Adding clause #{}: {:?}", i + 1, clause);
        solver.clause6(clause); // there are function clause1 ... clause5 for adding in smaller clauses, might be more efficient
        for lit in clause {
            // kind've annoying that I have to do this, but I don't thnk there is a better way
            solver.add_observed_var(i32::abs(*lit));
            debug_println!(0, 2, "Added observed variable: {}", i32::abs(*lit));
        }
    }

    // telling the proof_tracker that I am done with the original clauses
    proof_tracker.borrow_mut().finished_original_clauses = true;

    // adding this into disequalities instead so that it appears as a theory lemma
    for clause in &boolean_dt_constraints {
        solver.clause6(clause); // there are function clause1 ... clause5 for adding in smaller clauses, might be more efficient
        for lit in clause {
            // kind've annoying that I have to do this, but I don't thnk there is a better way
            solver.add_observed_var(i32::abs(*lit));
            propagator.add_lit_to_proof_tracker(*lit); // todo: calling this in too many places, need to cut down
            debug_println!(0, 2, "Added observed variable: {}", i32::abs(*lit));
        }
    }

    debug_println!(2, 1, "All clauses added, starting solver");

    let result = solve(&mut solver);

    // Disconnect the proof tracer before dropping the propagator
    solver.disconnect_proof_tracer1();

    // Generate proof after all borrows are released
    let edrat_proof = proof_tracker.borrow_mut().generate_edrat();
    // let quantifier_smt2_proof = proof_tracker.borrow_mut().generate_quantifier_smt2();

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
    result
}

fn solve(solver: &mut CaDiCal) -> Status {
    solver.solve()
}
