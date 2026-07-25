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
    /// The branch-and-bound search is recursive, so this doubles as a stack-overflow
    /// guard: a node at depth `d` sits `d` frames deep on the call stack. When the limit
    /// is reached the search returns `UNKNOWN` rather than recursing further. `None`
    /// means unlimited (only safe when running on a thread with a large stack).
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
            // Deep enough that well-behaved problems never hit it, low enough to stay
            // clear of the default thread stack limit on pathological inputs.
            max_branch_depth: Some(4096),
        }
    }
}
