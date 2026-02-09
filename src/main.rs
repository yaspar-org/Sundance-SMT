// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use cadical_sys::Status;
use clap::Parser;
use std::fs;
use sundance_smt::cdcl::cdcl_decision_procedure;
use sundance_smt::cnf::CNFConversion;
use sundance_smt::config::Args;
use sundance_smt::datatypes::process::check_for_inductive_datatypes_and_panic;
use sundance_smt::egraphs::egraph::Egraph;
use sundance_smt::preprocess::check_for_function_bool;
use sundance_smt::{debug_println, utils};
use yaspar_ir::ast::alg::{self};
use yaspar_ir::ast::TermAllocator;
use yaspar_ir::ast::{Context, LetElim, ObjectAllocatorExt, Repr, Term, Typecheck};
use yaspar_ir::untyped::UntypedAst;

fn main() -> Result<(), String> {
    let args = Args::parse();

    // Parse debug flag and level
    if args.debug > 0 {
        utils::DEBUG_LEVEL.store(args.debug, std::sync::atomic::Ordering::Relaxed);
        debug_println!(
            2,
            0,
            "Debug mode enabled (level {})",
            utils::DEBUG_LEVEL.load(std::sync::atomic::Ordering::Relaxed)
        );
    } else {
        utils::DEBUG_LEVEL.store(30, std::sync::atomic::Ordering::Relaxed);
    }

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

    let mut egraph = Egraph::new(context, args.lazy_dt, args.ddsmt, args.eager_skolem);

    egraph.insert_predecessor(&false_term, None, None, false, None);
    egraph.insert_predecessor(&true_term, None, None, false, None);

    // checking if we have any inductive datatypes -> if we do panic!
    // gets the info about our datatypes
    let datatype_info = check_for_inductive_datatypes_and_panic(&egraph.context);
    egraph.datatype_info = datatype_info;

    let mut nnf_terms = vec![];
    for assert in assertions {
        debug_println!(22, 0, "We have the assertion {} [{}]", assert, assert.uid());

        // inline the let bindings
        let let_elim_term = assert.let_elim(&mut egraph.context);
        debug_println!(10, 0, "Let_elim form: {}", let_elim_term);
        // todo: for some reason not inling define-fun

        let skolemized_term = let_elim_term;

        let nnf_term = skolemized_term.nnf(&mut egraph);
        debug_println!(
            12,
            0,
            "NNF form: {} with hash {}",
            nnf_term,
            egraph.predecessor_hash
        );

        nnf_terms.push(nnf_term.clone());

        egraph.insert_predecessor(&nnf_term, None, None, false, None);

        debug_println!(4, 0, "We have the nnf term {}", nnf_term);

        // Convert to CNF (Conjunctive Normal Form) using Sundance implementation
        // using tseitin transformation because if we have (and true b), we
        // want (and true b) <-> true \land b, not just the forwards direction
        let cnf_formula = nnf_term.cnf_tseitin(&mut egraph);

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
    let sorts = egraph.context.expose_sorts().clone();
    let symbol_table = egraph.context.expose_symbol_table().clone();

    debug_println!(
        6,
        0,
        "before BOOL: We have the var_map {:?}",
        egraph.cnf_cache.var_map
    );

    let mut boolean_dt_constraints = vec![];

    // have to do this as a separate loop because `check_for_function_bool` uses egraph.context
    // somewhat inefficient especially since we have to clone nnf_term, but I couldn't come up with a
    // better way to do this
    for nnf_term in nnf_terms {
        let additional_constraints = check_for_function_bool(&nnf_term, &mut egraph, false);
        boolean_dt_constraints.extend(additional_constraints);
    }

    // filtering prop_skeleton to get rid of -l l terms
    let prop_skeleton_filtered = prop_skeleton
        .iter()
        .filter(|list| !(list.len() == 2 && list[0] == -list[1]))
        .collect::<Vec<_>>();

    debug_println!(
        22,
        0,
        "We have the prop_skeleton {:?}",
        prop_skeleton_filtered
    );

    debug_println!(
        24,
        0,
        "We have the prop_skeleton in terms: {:?}",
        prop_skeleton_filtered
            .iter()
            .map(|x| x
                .iter()
                .map(|y| egraph.get_term_from_lit(*y))
                .collect::<Vec<_>>())
            .collect::<Vec<_>>()
    );

    let quantifiers = !egraph.quantifiers.is_empty();

    let return_value = cdcl_decision_procedure(
        &mut egraph,
        prop_skeleton,
        boolean_dt_constraints,
        args.proof,
        sorts,
        symbol_table,
        args.arithmetic,
        args.timeout,
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
    Ok(())
}
