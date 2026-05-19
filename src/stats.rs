// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::fmt;
use std::time::{Duration, Instant};

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
}

impl SolverStats {
    pub fn new() -> Self {
        Self {
            start_time: Instant::now(),
            decisions: 0,
            backtracks: 0,
            arith_checks: 0,
            instantiations: 0,
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
        writeln!(f, "  \"solve_time\": {:.3}", elapsed.as_secs_f64())?;
        write!(f, "}}")
    }
}
