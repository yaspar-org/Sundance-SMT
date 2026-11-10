// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Main CDCL decision loop
use crate::arithmetic::incremental_solver::IncrementalArithSolver;
use crate::arithmetic::incremental_solver::lira::LiraIncrementalState;
use crate::arithmetic::incremental_solver::translation::ArithTranslator;
use crate::arithmetic::lia::config::SolverConfig;
use crate::arithmetic::lp::ArithSolver;
use crate::cadical_propagator::{CustomExternalPropagator, EagerQiMode, ObservedSink};
use crate::config::SatBackend;
use crate::debug_println;
use crate::egraphs::EgraphTrait;
use crate::proof::{SMTProofTracer, Theory};
use crate::solver_state::SolverState;
use crate::stats::SolverStats;
use crate::utils::DeterministicHashSet;
use cadical_sys::{CaDiCal, ExternalPropagator, Status, Terminator};
use std::cell::RefCell;
use std::collections::HashMap;
use std::io::Write;
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

#[cfg(feature = "minisat")]
impl sat_interface::Terminator for DeadlineTerminator {
    fn terminated(&mut self) -> bool {
        Terminator::terminated(self)
    }
}

/// The propositional search engine selected by `--sat-backend`
enum Backend {
    Cadical(Box<CaDiCal>),
    #[cfg(feature = "minisat")]
    Minisat(Box<sat_interface::minisat::MiniSat>),
}

/// Everything about a solving session that is fixed when it starts.
pub struct SessionConfig {
    pub proof_file: Option<PathBuf>,
    pub partial_proof_file: Option<PathBuf>,
    pub trail_file: Option<PathBuf>,
    pub arithmetic: ArithSolver,
    /// Wall-clock budget in seconds for the whole session (0 = none).
    pub timeout: u64,
    pub sat_backend: SatBackend,
    pub elevate: i32,
    pub max_arith_conflicts_per_round: usize,
    pub batch_cap: usize,
    pub eager_qi: i32,
    /// Whether the session will call `check_sat` with assumptions or more than once. The eDRAT
    /// proof tracer does not support assumptions, so it is not connected in that case.
    pub incremental: bool,
}

/// A long-lived SAT solver plus theory propagator over one `SolverState`.
///
/// Clauses can be added and `check_sat` called any number of times. Between calls the theory
/// side is reset to decision level 0 before anything mutates the `SolverState`, so terms and
/// clauses added between solves are registered at the root.
pub struct Session<'a> {
    // Field order is drop order: the solver (which holds raw pointers to the propagator and
    // terminator) must go first.
    solver: Backend,
    propagator: Box<CustomExternalPropagator<'a>>,
    proof_tracer: Rc<RefCell<SMTProofTracer>>,
    _terminator: Option<Box<DeadlineTerminator>>,
    tracer_connected: bool,
    proof_file: Option<PathBuf>,
    partial_proof_file: Option<PathBuf>,
    trail_file: Option<PathBuf>,
    last_result: Option<Status>,
}

impl<'a> Session<'a> {
    pub fn new(
        solver_state: &'a mut SolverState,
        config: SessionConfig,
        sorts: HashMap<Str, SortDef>,
        symbol_table: HashMap<Str, Vec<(Sig, FunctionMeta)>>,
    ) -> Self {
        let SessionConfig {
            proof_file,
            partial_proof_file,
            trail_file,
            arithmetic,
            timeout,
            sat_backend,
            elevate,
            max_arith_conflicts_per_round,
            batch_cap,
            eager_qi,
            incremental,
        } = config;
        assert!(
            !incremental || (proof_file.is_none() && partial_proof_file.is_none()),
            "--proof/--partial-proof are not supported for incremental scripts (push/pop, \
             check-sat-assuming, several check-sat commands)"
        );

        // Create proof tracker for real-time proof tracking wrapped in Rc<RefCell<>>
        // todo: for right now always have hid_quantifiers to be true, need to change this
        let proof_tracer = Rc::new(RefCell::new(SMTProofTracer::new(sorts, symbol_table)));

        // A requested proof is trimmed to the clauses the refutation uses, which needs CaDiCaL's
        // clause ids and antecedents
        if proof_file.is_some() {
            proof_tracer.borrow_mut().track_core();
        }

        let tracer_connected = !incremental && sat_backend == SatBackend::Cadical;
        let mut solver = match sat_backend {
            SatBackend::Cadical => {
                // Boxed so the propagator's pointer stays valid when `solver` moves.
                let mut cadical = Box::new(CaDiCal::new());
                assert!(
                    cadical.set("elevate".to_string(), elevate),
                    "CaDiCaL option 'elevate' is unavailable; Sundance requires CaDiCaL >= 3.0.1 for lazy quantifier instantiation"
                );
                // Connect the proof tracer (must be done in CONFIGURING state)
                if tracer_connected {
                    cadical.connect_proof_tracer1(&mut *proof_tracer.borrow_mut(), true); // true for antecedents
                }
                Backend::Cadical(cadical)
            }
            SatBackend::Minisat => {
                assert!(
                    proof_file.is_none() && partial_proof_file.is_none(),
                    "MiniSat currently has no proof tracer; --proof/--partial-proof require --sat-backend cadical"
                );
                assert!(
                    !incremental,
                    "MiniSat has no assumption interface; incremental scripts require --sat-backend cadical"
                );
                #[cfg(feature = "minisat")]
                {
                    let mut minisat = Box::new(sat_interface::minisat::MiniSat::new());
                    assert!(
                        minisat.set("phase", 1),
                        "MiniSat option 'phase' is unavailable"
                    );
                    Backend::Minisat(minisat)
                }
                #[cfg(not(feature = "minisat"))]
                {
                    panic!("--sat-backend minisat requires building with `--features minisat`")
                }
            }
        };

        let deadline =
            (timeout > 0).then(|| Instant::now() + std::time::Duration::from_secs(timeout));
        let mut terminator = deadline.map(|deadline| Box::new(DeadlineTerminator { deadline }));
        if let Some(t) = terminator.as_mut() {
            match &mut solver {
                Backend::Cadical(cadical) => cadical.connect_terminator(&mut **t),
                #[cfg(feature = "minisat")]
                Backend::Minisat(minisat) => minisat.connect_terminator(&mut **t),
            }
        }
        let observed_sink = match &mut solver {
            Backend::Cadical(cadical) => ObservedSink::Cadical(&mut **cadical as *mut CaDiCal),
            #[cfg(feature = "minisat")]
            Backend::Minisat(minisat) => {
                ObservedSink::Minisat(&mut **minisat as *mut sat_interface::minisat::MiniSat)
            }
        };

        // The internal solvers' branch-and-bound runs inside a CaDiCaL callback, where the
        // terminator is not polled, so it checks the deadline itself.
        let lia_config = SolverConfig {
            deadline,
            ..SolverConfig::default()
        };
        let incremental_backend: Option<Box<dyn IncrementalArithSolver>> = match arithmetic {
            ArithSolver::InternalIncremental => Some(Box::new(LiraIncrementalState::with_config(
                lia_config.clone(),
            ))),
            #[cfg(feature = "z3-solver")]
            ArithSolver::Z3Incremental => Some(Box::new(
                crate::arithmetic::incremental_solver::z3::Z3IncrementalState::new(),
            )),
            _ => None,
        };
        solver_state
            .egraph
            .incremental_arithmetic(incremental_backend.is_some());
        let arith_translator = incremental_backend.map(ArithTranslator::new);

        let mut propagator = Box::new(CustomExternalPropagator {
            decision_level: 0,
            solver_state,
            disequalities: RefCell::new(vec![]),
            fixed_literals: DeterministicHashSet::default(),
            proof_tracer: Rc::clone(&proof_tracer),
            assignments: vec![0, 0],
            observed_sink,
            arithmetic,
            stats: SolverStats::new(),
            pending: None,
            eager_qi: EagerQiMode::new(eager_qi),
            materializing_quantifiers: false,
            max_arith_conflicts_per_round,
            last_observed_var: 1,
            batch_cap,
            arith: arith_translator,
            lia_config,
            arith_incomplete: false,
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
        });

        match &mut solver {
            Backend::Cadical(cadical) => cadical.connect_external_propagator(&mut *propagator),
            #[cfg(feature = "minisat")]
            Backend::Minisat(minisat) => minisat.connect_external_propagator(&mut *propagator),
        }
        // note: not using a fixed listener anymore
        // solver.connect_fixed_listener(&mut propagator);

        Session {
            solver,
            propagator,
            proof_tracer,
            _terminator: terminator,
            tracer_connected,
            proof_file,
            partial_proof_file,
            trail_file,
            last_result: None,
        }
    }

    /// Bring the theory side back to decision level 0.
    ///
    /// After `solve` returns, CaDiCaL leaves its trail in place and only backtracks (notifying
    /// the propagator) once it is next modified or solved. Terms registered in the e-graph in
    /// the meantime would land at the stale decision level and be undone by that backtrack, so
    /// anything that mutates the `SolverState` between solves goes through `state()`, which
    /// resets first. The later backtrack notification from CaDiCaL is then a no-op.
    fn ensure_root(&mut self) {
        if self.propagator.decision_level > 0 {
            ExternalPropagator::notify_backtrack(&mut *self.propagator, 0);
        }
    }

    /// The solver state, reset to decision level 0 (see `ensure_root`).
    pub fn state(&mut self) -> &mut SolverState {
        self.ensure_root();
        self.propagator.solver_state
    }

    pub fn stats_mut(&mut self) -> &mut SolverStats {
        &mut self.propagator.stats
    }

    /// Add a permanent clause. A missing `theory` denotes an original CNF clause.
    pub fn add_clause(&mut self, clause: &[i32], theory: Option<Theory>) {
        self.ensure_root();
        add_clause_to_proof_and_solver(clause, &mut self.solver, &self.proof_tracer, theory);
    }

    /// Solve under `assumptions`.
    pub fn check_sat(&mut self, assumptions: &[i32]) -> Status {
        self.ensure_root();
        self.propagator.arith_incomplete = false;
        self.propagator.stats.num_checks += 1;
        // Observe CNF variables created since the last solve (all of them, the first time).
        self.propagator.sync_new_vars();

        debug_println!(2, 1, "Starting solver");
        let result = match &mut self.solver {
            Backend::Cadical(cadical) => {
                for &lit in assumptions {
                    cadical.assume(lit);
                }
                cadical.solve()
            }
            #[cfg(feature = "minisat")]
            Backend::Minisat(minisat) => {
                use sat_interface::minisat::Status as MiniSatStatus;
                assert!(
                    assumptions.is_empty(),
                    "MiniSat has no assumption interface"
                );
                match minisat.solve() {
                    MiniSatStatus::Satisfiable => Status::SATISFIABLE,
                    MiniSatStatus::Unsatisfiable => Status::UNSATISFIABLE,
                    MiniSatStatus::Unknown => Status::UNKNOWN,
                }
            }
        };

        // An accepted model is not known to be a model of the input if an arithmetic check gave
        // up on it, or if the arithmetic solver is inexact (an opaque term).
        let result = if result == Status::SATISFIABLE
            && (self.propagator.arith_incomplete
                || self
                    .propagator
                    .arith
                    .as_ref()
                    .is_some_and(|a| !a.is_exact()))
        {
            Status::UNKNOWN
        } else {
            result
        };
        self.last_result = Some(result);
        result
    }

    /// Tear the session down: write the requested proof and trail files for the last result
    /// and return the accumulated statistics.
    pub fn finish(mut self) -> SolverStats {
        match &mut self.solver {
            Backend::Cadical(cadical) => {
                // Disconnect the proof tracer before dropping the propagator
                if self.tracer_connected {
                    cadical.disconnect_proof_tracer1();
                }
            }
            #[cfg(feature = "minisat")]
            Backend::Minisat(minisat) => {
                minisat.disconnect_external_propagator();
                minisat.disconnect_terminator();
            }
        }
        let result = self.last_result.unwrap_or(Status::UNKNOWN);

        // Write the proof after all borrows are released. `--proof` writes it on unsat only,
        // trimmed to the refutation; `--partial-proof` writes everything recorded, for any result.
        if let Some(p) = &self.proof_file
            && result == Status::UNSATISFIABLE
        {
            if let Err(e) = write_proof_file(p, |w| self.proof_tracer.borrow().write_edrat(w, true))
            {
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

        if let Some(p) = &self.partial_proof_file {
            write_partial_proof(p, result, &self.proof_tracer.borrow());
        }

        // Trails were streamed during the solve; append the now-complete atom map.
        if self.trail_file.is_some() {
            self.propagator.finish_trail_log();
            debug_println!(2, 0, "trail log written");
        }

        // Harvest stats from solver_state, egraph, and proof tracer
        self.propagator.sync_external_stats();
        self.propagator.stats.finish();
        std::mem::take(&mut self.propagator.stats)
    }
}

/// Main CDCL decision loop: one solve over a fixed clause set.
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
    sat_backend: SatBackend,
    elevate: i32,
    max_arith_conflicts_per_round: usize,
    batch_cap: usize,
    eager_qi: i32,
) -> (Status, SolverStats) {
    let config = SessionConfig {
        proof_file,
        partial_proof_file,
        trail_file,
        arithmetic,
        timeout,
        sat_backend,
        elevate,
        max_arith_conflicts_per_round,
        batch_cap,
        eager_qi,
        incremental: false,
    };
    let mut session = Session::new(solver_state, config, sorts, symbol_table);

    debug_println!(2, 0, "CDCL: Starting CDCL solver");
    debug_println!(1, 1, "Adding {} clauses to solver", clauses.len());

    // Add all clauses to the solver
    for (i, clause) in clauses.iter().enumerate() {
        debug_println!(11, 2, "Adding clause #{}: {:?}", i + 1, clause);
        session.add_clause(clause, None);
    }

    // adding this into disequalities instead so that it appears as a theory lemma
    for clause in &boolean_dt_constraints {
        session.add_clause(clause, Some(Theory::Datatypes));
    }
    count_clauses(session.stats_mut(), &boolean_dt_constraints);

    let result = session.check_sat(&[]);
    let stats = session.finish();
    (result, stats)
}

/// Count `clauses` in the clause-size statistics.
pub fn count_clauses(stats: &mut SolverStats, clauses: &[Vec<i32>]) {
    for clause in clauses {
        match clause.len() {
            0 | 1 => {}
            2 => stats.binary_clauses += 1,
            _ => stats.clauses += 1,
        }
    }
}

/// Creates `path` and streams the proof into it through `write`.
fn write_proof_file(
    path: &std::path::Path,
    write: impl FnOnce(&mut std::io::BufWriter<std::fs::File>) -> std::io::Result<()>,
) -> std::io::Result<()> {
    let mut out = std::io::BufWriter::new(std::fs::File::create(path)?);
    write(&mut out)?;
    out.flush()
}

/// Dump the eDRAT proof forest for any result: complete on unsat, else a prefix
/// with no final empty clause. A leading `;` comment records which case it is.
/// Header status: unsat -> unsat, sat -> unknown, unknown (cadical) ->
/// timeout/interrupt.
fn write_partial_proof(path: &std::path::Path, result: Status, proof_tracer: &SMTProofTracer) {
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
    if let Err(e) = write_proof_file(path, |w| {
        w.write_all(header.as_bytes())?;
        proof_tracer.write_edrat(w, false)
    }) {
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

/// Records a clause before the SAT solver can synchronously simplify or delete it.
/// A missing `theory` denotes an original CNF clause.
fn add_clause_to_proof_and_solver(
    clause: &[i32],
    solver: &mut Backend,
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

    match solver {
        Backend::Cadical(cadical) => cadical.clause6(clause), // TODO `clause1()`, `clause2()`, etc. might be more efficient
        #[cfg(feature = "minisat")]
        Backend::Minisat(minisat) => minisat.add_clause(clause),
    }
}
