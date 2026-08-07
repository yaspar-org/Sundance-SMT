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
    /// Maximum branch-and-bound tree depth explored before giving up.
    ///
    /// Branch-and-bound uses an explicit heap-allocated stack (not recursion), so depth is
    /// bounded by heap memory rather than the OS thread stack; this limit can therefore be
    /// set high without risking stack overflow. When it is reached the search returns
    /// `UNKNOWN` rather than descending further. `None` means unlimited.
    pub max_branch_depth: Option<usize>,
}

impl Default for SolverConfig {
    fn default() -> Self {
        Self {
            tableau_kind: TableauKind::Sparse,
            // Note: 2^17 is high enough that regression tests pass as expected
            // i.e. they are either SAT/UNSAT or TIMEOUT. If this is lowered
            // significantly, some will return UNKNOWN instead since branch-and-bound
            // will return UNKNOWN when the limit is hit.
            max_lra_solve_calls: None,
            // Branch-and-bound runs on an explicit heap stack, so this is no longer capped by
            // the thread stack.
            max_branch_depth: Some(1 << 18),
        }
    }
}
