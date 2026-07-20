// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::fmt;
use std::time::{Duration, Instant};

use crate::arithmetic::lia::stats::Stats as LiaStats;

/// Accumulated statistics from the arithmetic sub-solver
#[derive(Debug, Default, Clone)]
pub struct ArithStats {
    /// Total number of simplex pivots across all arithmetic checks
    pub num_simplex_steps: usize,
    /// Total number of LRA solver invocations across all arithmetic checks
    pub num_lra_solve: usize,
}

impl ArithStats {
    pub fn accumulate(&mut self, lia_stats: &LiaStats) {
        self.num_simplex_steps += lia_stats.num_simplex_steps;
        self.num_lra_solve += lia_stats.num_lra_solve;
    }
}

/// Per-round statistics snapshot (deltas for a single QI round)
#[derive(Debug, Clone)]
pub struct RoundStats {
    pub decisions: u64,
    pub backtracks: u64,
    pub conflicts: u64,
    pub arith_checks: u64,
    pub instantiations: u64,
    pub added_eqs: u64,
    pub mk_bool_vars: u64,
    pub mk_clauses: u64,
    pub del_clauses: u64,
    pub dt_accessor_ax: u64,
    pub dt_constructor_ax: u64,
    pub dt_splits: u64,
    pub arith: ArithStats,
}

/// Statistics about the solver run
#[derive(Debug)]
pub struct SolverStats {
    start_time: Instant,

    /// Number of new decision levels created by CaDiCaL (notify_new_decision_level calls)
    pub decisions: u64,
    /// Number of backtrack notifications from CaDiCaL (notify_backtrack calls)
    pub backtracks: u64,
    /// Number of calls to the arithmetic theory solver (check_integer_constraints_satisfiable)
    pub arith_checks: u64,
    /// Number of quantifier instantiations added as clauses to CaDiCaL
    pub instantiations: u64,
    /// Number of times the quantifier instantiation queue was refreshed
    /// (i.e., number of calls to `instantiate_quantifiers` that produced work)
    pub instantiation_rounds: u64,
    /// Accumulated arithmetic sub-solver statistics
    pub arith: ArithStats,
    /// Number of theory conflicts (cb_check_found_model returning false)
    pub conflicts: u64,
    /// Number of clauses created (initial + theory lemmas fed to CaDiCaL)
    pub mk_clauses: u64,
    /// Number of clauses deleted by CaDiCaL
    pub del_clauses: u64,
    /// Number of boolean variables allocated
    pub mk_bool_vars: u64,
    /// Number of equality merges in the egraph
    pub added_eqs: u64,
    /// Number of datatype accessor axioms (selector projections)
    pub dt_accessor_ax: u64,
    /// Number of datatype constructor axioms (tester/exhaustiveness)
    pub dt_constructor_ax: u64,
    /// Number of datatype case splits (deferred tester clauses)
    pub dt_splits: u64,
    /// Number of check-sat calls
    pub num_checks: u64,
    /// Per-round statistics (one entry per QI round)
    pub per_round: Vec<RoundStats>,
    // Snapshot of totals at the start of the current round
    snapshot_decisions: u64,
    snapshot_backtracks: u64,
    snapshot_conflicts: u64,
    snapshot_arith_checks: u64,
    snapshot_instantiations: u64,
    snapshot_added_eqs: u64,
    snapshot_mk_bool_vars: u64,
    snapshot_mk_clauses: u64,
    snapshot_del_clauses: u64,
    snapshot_dt_accessor_ax: u64,
    snapshot_dt_constructor_ax: u64,
    snapshot_dt_splits: u64,
    snapshot_arith: ArithStats,
}

impl SolverStats {
    pub fn new() -> Self {
        Self {
            start_time: Instant::now(),
            decisions: 0,
            backtracks: 0,
            arith_checks: 0,
            instantiations: 0,
            instantiation_rounds: 0,
            arith: ArithStats::default(),
            conflicts: 0,
            mk_clauses: 0,
            del_clauses: 0,
            mk_bool_vars: 0,
            added_eqs: 0,
            dt_accessor_ax: 0,
            dt_constructor_ax: 0,
            dt_splits: 0,
            num_checks: 1,
            per_round: Vec::new(),
            snapshot_decisions: 0,
            snapshot_backtracks: 0,
            snapshot_conflicts: 0,
            snapshot_arith_checks: 0,
            snapshot_instantiations: 0,
            snapshot_added_eqs: 0,
            snapshot_mk_bool_vars: 0,
            snapshot_mk_clauses: 0,
            snapshot_del_clauses: 0,
            snapshot_dt_accessor_ax: 0,
            snapshot_dt_constructor_ax: 0,
            snapshot_dt_splits: 0,
            snapshot_arith: ArithStats::default(),
        }
    }

    pub fn elapsed(&self) -> Duration {
        self.start_time.elapsed()
    }

    /// Call at the start of each QI round to close out the previous round
    /// and begin tracking a new one.
    pub fn begin_round(&mut self) {
        if self.instantiation_rounds > 0 {
            self.per_round.push(self.round_delta());
        }
        self.take_snapshot();
    }

    /// Flush the final in-progress round (call after solving completes).
    pub fn finish(&mut self) {
        if self.instantiation_rounds > 0 {
            self.per_round.push(self.round_delta());
        }
    }

    fn round_delta(&self) -> RoundStats {
        RoundStats {
            decisions: self.decisions - self.snapshot_decisions,
            backtracks: self.backtracks - self.snapshot_backtracks,
            conflicts: self.conflicts - self.snapshot_conflicts,
            arith_checks: self.arith_checks - self.snapshot_arith_checks,
            instantiations: self.instantiations - self.snapshot_instantiations,
            added_eqs: self.added_eqs - self.snapshot_added_eqs,
            mk_bool_vars: self.mk_bool_vars - self.snapshot_mk_bool_vars,
            mk_clauses: self.mk_clauses - self.snapshot_mk_clauses,
            del_clauses: self.del_clauses - self.snapshot_del_clauses,
            dt_accessor_ax: self.dt_accessor_ax - self.snapshot_dt_accessor_ax,
            dt_constructor_ax: self.dt_constructor_ax - self.snapshot_dt_constructor_ax,
            dt_splits: self.dt_splits - self.snapshot_dt_splits,
            arith: ArithStats {
                num_simplex_steps: self.arith.num_simplex_steps
                    - self.snapshot_arith.num_simplex_steps,
                num_lra_solve: self.arith.num_lra_solve - self.snapshot_arith.num_lra_solve,
            },
        }
    }

    fn take_snapshot(&mut self) {
        self.snapshot_decisions = self.decisions;
        self.snapshot_backtracks = self.backtracks;
        self.snapshot_conflicts = self.conflicts;
        self.snapshot_arith_checks = self.arith_checks;
        self.snapshot_instantiations = self.instantiations;
        self.snapshot_added_eqs = self.added_eqs;
        self.snapshot_mk_bool_vars = self.mk_bool_vars;
        self.snapshot_mk_clauses = self.mk_clauses;
        self.snapshot_del_clauses = self.del_clauses;
        self.snapshot_dt_accessor_ax = self.dt_accessor_ax;
        self.snapshot_dt_constructor_ax = self.dt_constructor_ax;
        self.snapshot_dt_splits = self.dt_splits;
        self.snapshot_arith = self.arith.clone();
    }
}

impl Default for SolverStats {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Display for SolverStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let elapsed = self.elapsed();
        writeln!(f, "{{")?;
        writeln!(f, "  \"decisions\": {},", self.decisions)?;
        writeln!(f, "  \"backtracks\": {},", self.backtracks)?;
        writeln!(f, "  \"conflicts\": {},", self.conflicts)?;
        writeln!(f, "  \"arith_checks\": {},", self.arith_checks)?;
        writeln!(f, "  \"instantiations\": {},", self.instantiations)?;
        writeln!(
            f,
            "  \"instantiation_rounds\": {},",
            self.instantiation_rounds
        )?;
        writeln!(f, "  \"added_eqs\": {},", self.added_eqs)?;
        writeln!(f, "  \"mk_bool_vars\": {},", self.mk_bool_vars)?;
        writeln!(f, "  \"mk_clauses\": {},", self.mk_clauses)?;
        writeln!(f, "  \"del_clauses\": {},", self.del_clauses)?;
        writeln!(f, "  \"dt_accessor_ax\": {},", self.dt_accessor_ax)?;
        writeln!(f, "  \"dt_constructor_ax\": {},", self.dt_constructor_ax)?;
        writeln!(f, "  \"dt_splits\": {},", self.dt_splits)?;
        writeln!(f, "  \"num_checks\": {},", self.num_checks)?;
        writeln!(f, "  \"arith\": {{")?;
        writeln!(
            f,
            "    \"simplex_steps\": {},",
            self.arith.num_simplex_steps
        )?;
        writeln!(f, "    \"lra_solve_calls\": {}", self.arith.num_lra_solve)?;
        writeln!(f, "  }},")?;
        if !self.per_round.is_empty() {
            writeln!(f, "  \"per_round\": [")?;
            for (i, round) in self.per_round.iter().enumerate() {
                writeln!(f, "    {{")?;
                writeln!(f, "      \"round\": {},", i + 1)?;
                writeln!(f, "      \"decisions\": {},", round.decisions)?;
                writeln!(f, "      \"backtracks\": {},", round.backtracks)?;
                writeln!(f, "      \"conflicts\": {},", round.conflicts)?;
                writeln!(f, "      \"arith_checks\": {},", round.arith_checks)?;
                writeln!(f, "      \"instantiations\": {},", round.instantiations)?;
                writeln!(f, "      \"added_eqs\": {},", round.added_eqs)?;
                writeln!(f, "      \"mk_bool_vars\": {},", round.mk_bool_vars)?;
                writeln!(f, "      \"mk_clauses\": {},", round.mk_clauses)?;
                writeln!(f, "      \"del_clauses\": {},", round.del_clauses)?;
                writeln!(f, "      \"dt_accessor_ax\": {},", round.dt_accessor_ax)?;
                writeln!(
                    f,
                    "      \"dt_constructor_ax\": {},",
                    round.dt_constructor_ax
                )?;
                writeln!(f, "      \"dt_splits\": {},", round.dt_splits)?;
                writeln!(f, "      \"arith\": {{")?;
                writeln!(
                    f,
                    "        \"simplex_steps\": {},",
                    round.arith.num_simplex_steps
                )?;
                writeln!(
                    f,
                    "        \"lra_solve_calls\": {}",
                    round.arith.num_lra_solve
                )?;
                write!(f, "      }}")?;
                if i + 1 < self.per_round.len() {
                    writeln!(f, "\n    }},")?;
                } else {
                    writeln!(f, "\n    }}")?;
                }
            }
            writeln!(f, "  ],")?;
        }
        writeln!(f, "  \"solve_time\": {:.3}", elapsed.as_secs_f64())?;
        write!(f, "}}")
    }
}
