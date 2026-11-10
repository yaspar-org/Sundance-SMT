// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Incremental SMT-LIB scripts: `push`/`pop`, `check-sat-assuming` and several `check-sat`
//! commands, all answered by one long-lived [`Session`].
//!
//! # Scopes
//!
//! Every push level owns a fresh *selector* variable `a`. An assertion made at that level is
//! converted to CNF as usual; the Tseitin definitions only define fresh variables and are added
//! permanently, and the final top-level unit `v` is added as `¬a ∨ v`. `check-sat` assumes the
//! selectors of every open level, and `pop` adds the unit `¬a`, which satisfies every clause
//! guarded by `a`, including the learned clauses that depended on the popped assertions (they
//! contain `¬a` because CaDiCaL treats assumptions as decisions). Assertions outside any scope
//! are added as plain units, exactly as in a non-incremental run. Theory lemmas, quantifier
//! instances and skolemizations are valid (or, for skolems, definitional over fresh symbols),
//! so they are kept across pops.
//!
//! Quantifiers asserted in a popped scope are marked inactive and no longer instantiated: their
//! instances would be sound but cannot help refute what is still asserted.

use std::io::Write;

use cadical_sys::Status;
use yaspar_ir::ast::alg::Command;
use yaspar_ir::ast::{Command as TypedCommand, GlobalSubst};
use yaspar_ir::ast::{Context, LetElim, ObjectAllocatorExt, Repr, Term, TermAllocator};

use crate::cdcl::{Session, SessionConfig, count_clauses};
use crate::cnf::CNFConversion;
use crate::config::Args;
use crate::debug_println;
use crate::preprocess::check_for_function_bool;
use crate::proof::Theory;
use crate::solver_state::SolverState;
use crate::stats::SolverStats;
use crate::theory_check::{NonlinearityCheck, reject_unsupported_theories};

/// Whether `commands` need the incremental driver rather than one solve over all assertions.
///
/// Scopes only matter if something is popped before a check: a single `check-sat` that no `pop`
/// precedes sees every assertion, so e.g. Boogie/Dafny output (`(push 1)`, assertions,
/// `(check-sat)`) keeps the plain single-solve path, where all assertions are permanent units.
pub fn is_incremental(commands: &[TypedCommand]) -> bool {
    let mut check_sats = 0;
    let mut popped = false;
    for c in commands {
        match c.repr() {
            Command::CheckSatAssuming(_) => return true,
            Command::Pop(_) => popped = true,
            Command::CheckSat if popped => return true,
            Command::CheckSat => check_sats += 1,
            _ => {}
        }
    }
    check_sats > 1
}

/// The commands the driver acts on, with their terms replaced by indices into the preprocessed
/// term list.
enum Step {
    Assert(usize),
    Push(usize),
    Pop(usize),
    CheckSat(Vec<usize>),
    Echo(String),
    Exit,
}

fn to_count(n: &dashu::integer::UBig) -> Result<usize, String> {
    usize::try_from(n.clone()).map_err(|_| format!("push/pop count {n} is too large"))
}

/// Run an incremental script, printing one result per `check-sat`/`check-sat-assuming`.
pub fn run_incremental(
    commands: &[TypedCommand],
    mut context: Context,
    args: &Args,
) -> Result<Option<SolverStats>, String> {
    // Flatten the script into steps, collecting every asserted or assumed term.
    let mut terms: Vec<Term> = vec![];
    let mut steps: Vec<Step> = vec![];
    for c in commands {
        match c.repr() {
            Command::Assert(t) => {
                steps.push(Step::Assert(terms.len()));
                terms.push(t.clone());
            }
            Command::CheckSat => steps.push(Step::CheckSat(vec![])),
            Command::CheckSatAssuming(ts) => {
                let idxs = (terms.len()..terms.len() + ts.len()).collect();
                terms.extend(ts.iter().cloned());
                steps.push(Step::CheckSat(idxs));
            }
            Command::Push(n) => steps.push(Step::Push(to_count(n)?)),
            Command::Pop(n) => steps.push(Step::Pop(to_count(n)?)),
            Command::Echo(s) => steps.push(Step::Echo(s.to_string())),
            Command::Exit => steps.push(Step::Exit),
            Command::Reset | Command::ResetAssertions => {
                return Err("reset and reset-assertions are not supported".to_string());
            }
            _ => {}
        }
    }

    reject_unsupported_theories(&terms, &mut context)?;

    let true_term = context.get_true();
    let false_term = context.get_false();
    let not_false_term = context.not(false_term.clone());

    let mut solver_state = SolverState::new(
        context,
        args.lazy_dt,
        args.ddsmt,
        args.eager_skolem,
        args.infer_triggers,
    );
    solver_state.register_bool_constants(&true_term, &false_term);
    solver_state.track_quantifier_scopes = true;

    // Same preprocessing as a non-incremental run: inline lets, then global definitions.
    let let_free: Vec<Term> = terms
        .iter()
        .map(|t| t.let_elim(&mut solver_state.context))
        .collect();
    let expanded = let_free.gsubst_all(&mut solver_state.context);
    let mut nonlinearity = NonlinearityCheck::default();
    for t in &expanded {
        nonlinearity.check(t)?;
    }

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

    let config = SessionConfig {
        proof_file: args.proof.clone(),
        partial_proof_file: args.partial_proof.clone(),
        trail_file: args.trail_out.clone(),
        arithmetic: args.arithmetic.clone(),
        timeout: args.timeout,
        sat_backend: args.sat_backend,
        elevate: args.elevate,
        max_arith_conflicts_per_round: args.max_arith_conflicts_per_round,
        batch_cap: args.batch_cap,
        eager_qi: args.eager_qi,
        incremental: true,
    };
    let session = Session::new(&mut solver_state, config, sorts, symbol_table);
    let mut driver = Driver {
        session,
        selectors: vec![],
        solves: 0,
        popped: false,
        lazy_dt: args.lazy_dt,
        ddsmt: args.ddsmt,
    };

    driver.assert_formula(&true_term);
    driver.assert_formula(&not_false_term);

    let mut out = std::io::stdout();
    for step in steps {
        match step {
            Step::Assert(i) => driver.assert_formula(&expanded[i]),
            Step::Push(n) => driver.push(n),
            Step::Pop(n) => driver.pop(n)?,
            Step::CheckSat(assumed) => {
                // `check-sat-assuming` is a check-sat in a throwaway scope holding the
                // assumptions.
                if !assumed.is_empty() {
                    driver.push(1);
                    for i in &assumed {
                        driver.assert_formula(&expanded[*i]);
                    }
                }
                let answer = driver.check_sat();
                if !assumed.is_empty() {
                    driver.pop(1)?;
                }
                writeln!(out, "{answer}").map_err(|e| e.to_string())?;
                out.flush().map_err(|e| e.to_string())?;
            }
            Step::Echo(s) => {
                writeln!(out, "{s}").map_err(|e| e.to_string())?;
            }
            Step::Exit => break,
        }
    }

    Ok(Some(driver.session.finish()))
}

struct Driver<'a> {
    session: Session<'a>,
    /// One selector per open push level, outermost first.
    selectors: Vec<i32>,
    solves: usize,
    /// Whether any scope has been popped (until then no quantifier can be inactive).
    popped: bool,
    lazy_dt: bool,
    ddsmt: bool,
}

impl Driver<'_> {
    fn depth(&self) -> usize {
        self.selectors.len()
    }

    /// Assert `term` (let-free, definitions expanded) in the innermost open scope.
    fn assert_formula(&mut self, term: &Term) {
        // Once the e-graph has been used by a search, new terms are registered dynamically so
        // congruence closure finds their existing counterparts.
        let dynamic = self.solves > 0;
        let depth = self.depth();
        let selector = self.selectors.last().copied();
        let (ddsmt, lazy_dt) = (self.ddsmt, self.lazy_dt);

        let state = self.session.state();
        let nnf_term = term.nnf(state);
        debug_println!(4, 0, "Asserting at depth {}: {}", depth, nnf_term);
        state.insert_predecessor(&nnf_term, None, None, dynamic);
        let mut clauses: Vec<Vec<i32>> = nnf_term
            .cnf_tseitin(state)
            .into_iter()
            .map(|c| c.into_iter().collect())
            .collect();
        let dt_clauses = check_for_function_bool(&nnf_term, state, dynamic, ddsmt, lazy_dt);
        state.mark_root_quantifiers(&nnf_term, depth);

        if let Some(selector) = selector {
            // `cnf_tseitin` emits the top-level unit last; only it depends on the assertion.
            let top = clauses
                .last_mut()
                .expect("cnf_tseitin always emits the top-level clause");
            debug_assert_eq!(top.len(), 1);
            top.push(-selector);
        }
        for clause in &clauses {
            self.session.add_clause(clause, None);
        }
        for clause in &dt_clauses {
            self.session.add_clause(clause, Some(Theory::Datatypes));
        }
        count_clauses(self.session.stats_mut(), &dt_clauses);
        if self.popped {
            // A re-asserted quantifier may have been inactive.
            self.session.state().recompute_inactive_quantifiers();
        }
    }

    fn push(&mut self, n: usize) {
        for _ in 0..n {
            let selector = self.session.state().new_control_var();
            self.selectors.push(selector);
        }
    }

    fn pop(&mut self, n: usize) -> Result<(), String> {
        if n > self.depth() {
            return Err(format!(
                "pop {n} exceeds the current push depth {}",
                self.depth()
            ));
        }
        for _ in 0..n {
            let selector = self.selectors.pop().unwrap();
            self.session.add_clause(&[-selector], None);
        }
        let depth = self.depth();
        let state = self.session.state();
        state.retract_root_quantifiers(depth);
        state.recompute_inactive_quantifiers();
        self.popped = true;
        Ok(())
    }

    fn check_sat(&mut self) -> &'static str {
        let assumptions = self.selectors.clone();
        let quantified = self.session.state().has_active_quantifiers();
        let result = self.session.check_sat(&assumptions);
        self.solves += 1;
        match result {
            // As in a non-incremental run: with quantifiers, a model of the instances found so
            // far is not known to be a model of the input.
            Status::SATISFIABLE if quantified => "unknown",
            Status::SATISFIABLE => "sat",
            Status::UNSATISFIABLE => "unsat",
            Status::UNKNOWN => "unknown",
        }
    }
}
