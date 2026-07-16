// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::fmt;
use std::time::{Duration, Instant};

use crate::arithmetic::lia::stats::Stats as LiaStats;

/// Accumulated statistics from the arithmetic sub-solver
#[derive(Debug, Default)]
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
    /// Literals skipped by relevancy filtering
    pub relevancy_skipped: u64,
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
            relevancy_skipped: 0,
        }
    }

    pub fn elapsed(&self) -> Duration {
        self.start_time.elapsed()
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
        writeln!(f, "  \"arith_checks\": {},", self.arith_checks)?;
        writeln!(f, "  \"instantiations\": {},", self.instantiations)?;
        writeln!(
            f,
            "  \"instantiation_rounds\": {},",
            self.instantiation_rounds
        )?;
        writeln!(f, "  \"arith\": {{")?;
        writeln!(
            f,
            "    \"simplex_steps\": {},",
            self.arith.num_simplex_steps
        )?;
        writeln!(f, "    \"lra_solve_calls\": {}", self.arith.num_lra_solve)?;
        writeln!(f, "  }},")?;
        writeln!(f, "  \"solve_time\": {:.3},", elapsed.as_secs_f64())?;
        writeln!(f, "  \"relevancy_skipped\": {}", self.relevancy_skipped)?;
        write!(f, "}}")
    }
}
