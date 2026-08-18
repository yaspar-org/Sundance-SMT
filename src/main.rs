// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use cadical_sys::Status;
use clap::Parser;
use std::fs;
use sundance_smt::cdcl::cdcl_decision_procedure;
use sundance_smt::cnf::CNFConversion;
use sundance_smt::config::Args;
use sundance_smt::preprocess::check_for_function_bool;
use sundance_smt::solver_state::SolverState;
use sundance_smt::{debug_println, log};
use yaspar_ir::ast::alg::{self};
use yaspar_ir::ast::{Context, LetElim, ObjectAllocatorExt, Repr, Term, Typecheck};
use yaspar_ir::ast::{GlobalSubst, TermAllocator};
use yaspar_ir::untyped::UntypedAst;

fn main() -> Result<(), String> {
    let args = Args::parse();

    // --proof and --partial-proof both write an eDRAT dump; using them together
    // is ambiguous (and with the same path the second write silently truncates
    // the first, replacing a checkable refutation with a header-prefixed
    // prefix, or vice versa). Reject the combination outright.
    assert!(
        !(args.proof.is_some() && args.partial_proof.is_some()),
        "--proof and --partial-proof are mutually exclusive: both write an eDRAT \
         dump, and pointing them at the same file would overwrite one with the \
         other. Pass only one (--proof for a checkable refutation on unsat, \
         --partial-proof for a dump on any result)."
    );

    // Parse debug flag and level
    if args.debug > 0 {
        log::set_debug_level(args.debug);
        debug_println!(
            2,
            0,
            "Debug mode enabled (level {})",
            log::get_debug_level()
        );
    }
    // else the default is set in `crate::log`

    // Enable debug output for proof tracking if proof file is specified
    if args.proof.is_some() {
        debug_println!(2, 0, "Proof tracking enabled - will generate eDRAT proof");
    }

    // Read the SMT file
    let input = fs::read_to_string(&args.smt_file)
        .map_err(|e| format!("Error reading file {}: {}", args.smt_file.display(), e))?;

    let commands = UntypedAst
        .parse_script_str(&input)
        .map_err(|e| format!("Error parsing SMT file: {e}"))?;

    let mut context = Context::new();

    let typed_commands = commands
        .type_check(&mut context)
        .map_err(|e| format!("Error checking typed commands: {e}"))?;

    let mut assertions: Vec<Term> = typed_commands
        .iter()
        .filter_map(|c| {
            if let alg::Command::Assert(t) = c.repr() {
                Some(t.clone())
            } else {
                None
            }
        })
        .collect::<Vec<_>>();

    let mut prop_skeleton: Vec<Vec<i32>> = vec![];

    // adding true and false to the egraph
    let false_term: Term = context.get_false();
    let not_false_term = context.not(false_term.clone());

    let true_term: Term = context.get_true();

    // these are necessary because you want to include true and not false in var_map
    assertions.push(true_term.clone());
    assertions.push(not_false_term);

    let mut solver_state = SolverState::new(
        context,
        args.lazy_dt,
        args.ddsmt,
        args.eager_skolem,
        args.infer_triggers,
    );

    solver_state.register_bool_constants(&true_term, &false_term);

    let mut nnf_terms = vec![];
    for assert in assertions {
        debug_println!(22, 0, "We have the assertion {} [{}]", assert, assert.uid());

        // inline the let bindings
        let expanded_term = assert
            .let_elim(&mut solver_state.context)
            .gsubst_all(&mut solver_state.context);
        debug_println!(10, 0, "Expanded form: {}", expanded_term);

        let skolemized_term = expanded_term;

        let nnf_term = skolemized_term.nnf(&mut solver_state);
        debug_println!(12, 0, "NNF form: {}", nnf_term,);

        nnf_terms.push(nnf_term.clone());

        solver_state.insert_predecessor(&nnf_term, None, None, false);

        debug_println!(4, 0, "We have the nnf term {}", nnf_term);

        // Convert to CNF (Conjunctive Normal Form) using Sundance implementation
        // using tseitin transformation because if we have (and true b), we
        // want (and true b) <-> true \land b, not just the forwards direction
        let cnf_formula = nnf_term.cnf_tseitin(&mut solver_state);

        debug_println!(4, 0, "We have the cnf formula {}", cnf_formula);

        debug_println!(4, 0, "CNF formula: {:?}", cnf_formula);

        prop_skeleton.extend(
            cnf_formula
                .clone()
                .into_iter()
                .map(|x| x.into_iter().collect::<Vec<_>>()),
        );
    }

    // save the sorts and symbol table for the proof file
    let sorts = solver_state.context.expose_sorts().clone();
    let symbol_table = solver_state.context.expose_symbol_table().clone();

    debug_println!(
        6,
        0,
        "before BOOL: We have the var_map {:?}",
        solver_state.cnf_cache.var_map
    );

    let mut boolean_dt_constraints = vec![];

    // have to do this as a separate loop because `check_for_function_bool` uses solver_state.context
    // somewhat inefficient especially since we have to clone nnf_term, but I couldn't come up with a
    // better way to do this
    for nnf_term in nnf_terms {
        let additional_constraints = check_for_function_bool(
            &nnf_term,
            &mut solver_state,
            false,
            args.ddsmt,
            args.lazy_dt,
        );
        boolean_dt_constraints.extend(additional_constraints);
    }

    debug_println!(22, 0, "We have the prop_skeleton {:?}", prop_skeleton);

    debug_println!(
        24,
        0,
        "We have the prop_skeleton in terms: {:?}",
        prop_skeleton
            .iter()
            .map(|x| x
                .iter()
                .map(|y| solver_state.get_term_from_lit(*y))
                .collect::<Vec<_>>())
            .collect::<Vec<_>>()
    );

    let quantifiers = !solver_state.quantifiers.is_empty();

    let (return_value, stats) = cdcl_decision_procedure(
        &mut solver_state,
        prop_skeleton,
        boolean_dt_constraints,
        args.proof,
        args.partial_proof,
        args.trail_out,
        sorts,
        symbol_table,
        args.arithmetic,
        args.timeout,
        args.elevate,
        args.max_arith_conflicts_per_round,
        args.batch_cap,
        args.eager_qi,
    );

    match return_value {
        Status::SATISFIABLE => {
            if quantifiers {
                println!("unknown")
            } else {
                println!("sat")
            }
        }
        Status::UNSATISFIABLE => println!("unsat"),
        Status::UNKNOWN => println!("unknown"),
    }

    if args.stats {
        eprintln!("{stats}");
    }

    Ok(())
}
