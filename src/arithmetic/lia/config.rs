// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Solver configuration for the LIA arithmetic solver.

use crate::arithmetic::lia::tableau::TableauKind;

/// Configuration parameters for the LIA solver pipeline.
#[derive(Debug, Clone)]
pub struct SolverConfig {
    /// Which tableau implementation to use (dense or sparse).
    pub tableau_kind: TableauKind,
    /// Upper bound on the number of LRA solve calls in branch-and-bound.
    /// `None` means unlimited.
    pub max_lra_solve_calls: Option<usize>,
}

impl Default for SolverConfig {
    fn default() -> Self {
        Self {
            tableau_kind: TableauKind::Dense,
            // 2^17; high enough that regression tests pass as expected
            // i.e. they are either SAT/UNSAT or TIMEOUT. If this is lowered
            // significantly, some will return UNKNOWN instead.
            max_lra_solve_calls: Some(131_072),
        }
    }
}
