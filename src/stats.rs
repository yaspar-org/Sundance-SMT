// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::fmt;
use std::time::{Duration, Instant};

/// Statistics about the solver run
#[derive(Debug)]
pub struct SolverStats {
    start_time: Instant,

    pub decisions: u64,
    pub backtracks: u64,
    pub arith_checks: u64,
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
