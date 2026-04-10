// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Statistics for the LRA/LIRA solvers

/// Statistics for the LRA/LIRA solvers
#[derive(Debug, Clone)]
pub struct Stats {
    /// Number of simplex steps (pivots) in total across multiple LRASolver solve() calls
    pub num_simplex_steps: usize,
    /// Number of LRASolver solve() calls
    pub num_lra_solve: usize,
}

impl Stats {
    /// Construct a new [`Stats`] object
    pub fn new() -> Self {
        Self {
            num_simplex_steps: 0,
            num_lra_solve: 0,
        }
    }

    /// Combine stats objects, adding the totals in `other` to `self`.
    pub fn combine(&mut self, other: &Stats) {
        self.num_simplex_steps += other.num_simplex_steps;
        self.num_lra_solve += other.num_lra_solve;
    }
}

impl Default for Stats {
    fn default() -> Self {
        Self::new()
    }
}
