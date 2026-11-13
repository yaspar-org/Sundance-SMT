// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use cadical_sys::Status;
use clap::Parser;
use std::fs;
use std::path::PathBuf;
use sundance_smt::cdcl::cdcl_decision_procedure;
use sundance_smt::cnf::CNFConversion;
use sundance_smt::config::Args;
use sundance_smt::preprocess::check_for_function_bool;
use sundance_smt::solver_state::SolverState;
use sundance_smt::stats::SolverStats;
use sundance_smt::theory_check::{NonlinearityCheck, reject_unsupported_theories};
use sundance_smt::{debug_println, log};
use yaspar_ir::ast::alg::{self};
use yaspar_ir::ast::{Context, LetElim, ObjectAllocatorExt, Repr, Term, Typecheck};
use yaspar_ir::ast::{GlobalSubst, TermAllocator};
use yaspar_ir::traits::MetaData;
use yaspar_ir::untyped::{Command as UntypedCommand, UntypedAst};

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

    if is_incremental(&commands) {
        return run_incremental(&commands, &args);
    }

    let mut context = Context::new();

    let typed_commands = commands
        .type_check(&mut context)
        .map_err(|e| format!("Error checking typed commands: {e}"))?;

    let assertions: Vec<Term> = typed_commands
        .iter()
        .filter_map(|c| {
            if let alg::Command::Assert(t) = c.repr() {
                Some(t.clone())
            } else {
                None
            }
        })
        .collect::<Vec<_>>();

    let (return_value, stats, quantifiers) = solve_single(
        context,
        assertions,
        &args,
        args.proof.clone(),
        args.partial_proof.clone(),
        args.trail_out.clone(),
    )?;

    print_status(return_value, quantifiers);

    if args.stats {
        eprintln!("{stats}");
    }

    Ok(())
}

/// Print the answer of one check. `sat` is weakened to `unknown` when the query has quantifiers,
/// since the instantiation procedure is incomplete.
fn print_status(status: Status, quantifiers: bool) {
    match status {
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
}

/// Whether `commands` needs the incremental (one solve per check) path: it has a
/// `check-sat-assuming`, more than one `check-sat`, or a `check-sat` after a `pop`. Every other
/// script, including the Boogie/Dafny shape `(push 1) ... (check-sat)`, keeps the single-solve
/// path. Commands after `exit` are never executed, so they are not counted.
fn is_incremental(commands: &[UntypedCommand]) -> bool {
    let mut seen_pop = false;
    let mut checks = 0usize;
    for c in commands {
        match c.repr() {
            alg::Command::CheckSatAssuming(_) => return true,
            alg::Command::CheckSat => {
                if seen_pop || checks > 0 {
                    return true;
                }
                checks += 1;
            }
            alg::Command::Pop(_) => seen_pop = true,
            alg::Command::Exit => break,
            _ => {}
        }
    }
    false
}

/// Run an incremental script by rebuilding everything at each check.
///
/// The untyped commands (declarations, definitions, assertions, options) are kept on a stack of
/// frames, one per open `push` level. At every `check-sat` / `check-sat-assuming`, the commands of
/// all open frames are type-checked from scratch into a fresh `Context` and solved by
/// [`solve_single`] with a fresh `SolverState` and SAT solver. Nothing (instances, lemmas, learned
/// clauses) is carried from one check to the next, so declarations made inside a popped frame
/// are simply gone. `check-sat-assuming` adds its assumptions as extra assertions for that check
/// only. `--timeout` applies to each check separately, and `--stats` prints the statistics of
/// each check. `--trail-out` is rewritten by every check, so it ends up holding the trail of the
/// last one. Proof output is rejected, because one proof file cannot hold one refutation per
/// check.
fn run_incremental(commands: &[UntypedCommand], args: &Args) -> Result<(), String> {
    if args.proof.is_some() || args.partial_proof.is_some() {
        return Err(
            "--proof and --partial-proof are not supported for incremental scripts \
             (push/pop, check-sat-assuming or several check-sat commands)"
                .to_string(),
        );
    }

    let mut frames: Vec<Vec<UntypedCommand>> = vec![vec![]];
    for c in commands {
        match c.repr() {
            alg::Command::Push(n) => {
                let n = usize::try_from(n).map_err(|_| format!("push level too large: {n}"))?;
                frames.extend((0..n).map(|_| vec![]));
            }
            alg::Command::Pop(n) => {
                let n = usize::try_from(n).ok().filter(|n| *n < frames.len());
                let Some(n) = n else {
                    return Err(format!(
                        "pop of more levels than were pushed ({} open){}",
                        frames.len() - 1,
                        c.display_meta_data()
                    ));
                };
                frames.truncate(frames.len() - n);
            }
            alg::Command::CheckSat | alg::Command::CheckSatAssuming(_) => {
                let assuming = matches!(c.repr(), alg::Command::CheckSatAssuming(_));
                let mut script: Vec<UntypedCommand> = frames.concat();
                if assuming {
                    // Type-checked together with the prefix; its terms become assertions below.
                    script.push(c.clone());
                }
                let (status, stats, quantifiers) = solve_scope(&script, args)?;
                print_status(status, quantifiers);
                if args.stats {
                    eprintln!("{stats}");
                }
            }
            alg::Command::Exit => break,
            alg::Command::Reset | alg::Command::ResetAssertions => {
                return Err(format!(
                    "reset and reset-assertions are not supported{}",
                    c.display_meta_data()
                ));
            }
            // Output-only commands: ignored, as on the single-solve path.
            alg::Command::Echo(_)
            | alg::Command::GetAssertions
            | alg::Command::GetAssignment
            | alg::Command::GetInfo(_)
            | alg::Command::GetModel
            | alg::Command::GetOption(_)
            | alg::Command::GetProof
            | alg::Command::GetUnsatAssumptions
            | alg::Command::GetUnsatCore
            | alg::Command::GetValue(_) => {}
            _ => frames
                .last_mut()
                .expect("the base frame is never popped")
                .push(c.clone()),
        }
    }
    Ok(())
}

/// Type-check `script` (the in-scope commands of an incremental script, possibly ending in a
/// `check-sat-assuming`) into a fresh `Context` and solve its assertions as one query.
fn solve_scope(
    script: &[UntypedCommand],
    args: &Args,
) -> Result<(Status, SolverStats, bool), String> {
    let mut context = Context::new();
    let typed_commands = script
        .to_vec()
        .type_check(&mut context)
        .map_err(|e| format!("Error checking typed commands: {e}"))?;
    let mut assertions = vec![];
    for c in &typed_commands {
        match c.repr() {
            alg::Command::Assert(t) => assertions.push(t.clone()),
            alg::Command::CheckSatAssuming(ts) => assertions.extend(ts.iter().cloned()),
            _ => {}
        }
    }
    solve_single(
        context,
        assertions,
        args,
        None,
        None,
        args.trail_out.clone(),
    )
}

/// Solve one query: the conjunction of `assertions`, all type-checked in `context`. Returns the
/// SAT status, the solver statistics, and whether the query contains quantifiers.
fn solve_single(
    mut context: Context,
    mut assertions: Vec<Term>,
    args: &Args,
    proof: Option<PathBuf>,
    partial_proof: Option<PathBuf>,
    trail_out: Option<PathBuf>,
) -> Result<(Status, SolverStats, bool), String> {
    // Bail out before the assertions reach the egraph when operators from theories we do not
    // implement would silently become uninterpreted functions and could yield `sat` on an `unsat`
    // problem.
    reject_unsupported_theories(&assertions, &mut context)?;

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
    // Non-linear multiplication is the other input the solver cannot handle, and the arithmetic
    // frontend reports it by panicking from inside a CaDiCaL callback, where cxx turns the panic
    // into `abort()`. Catching it here instead keeps it a clean error. The check has to see the
    // let-eliminated, globally substituted term, so it runs inside the loop below rather than
    // alongside `reject_unsupported_theories`.
    let mut nonlinearity = NonlinearityCheck::default();
    // Inline the let bindings, then the global definitions. `gsubst_all` runs once over the whole
    // batch so the defined symbols are collected once rather than per assertion.
    let let_free: Vec<Term> = assertions
        .iter()
        .map(|a| a.let_elim(&mut solver_state.context))
        .collect();
    let expanded_terms = let_free.gsubst_all(&mut solver_state.context);
    for (assert, expanded_term) in assertions.iter().zip(expanded_terms) {
        debug_println!(22, 0, "We have the assertion {} [{}]", assert, assert.uid());
        debug_println!(10, 0, "Expanded form: {}", expanded_term);

        nonlinearity.check(&expanded_term)?;

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
    let sorts = solver_state
        .context
        .expose_sorts()
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
    let symbol_table = solver_state
        .context
        .expose_symbol_table()
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();

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
        proof,
        partial_proof,
        trail_out,
        sorts,
        symbol_table,
        args.arithmetic.clone(),
        args.timeout,
        args.sat_backend,
        args.elevate,
        args.max_arith_conflicts_per_round,
        args.batch_cap,
        args.eager_qi,
    );

    Ok((return_value, stats, quantifiers))
}
