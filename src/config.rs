// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Solver configuration and command line parsing

use crate::arithmetic::lp::ArithSolver;
use clap::Parser;
use std::path::PathBuf;

/// Sundance is an SMT solver for program verification
#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
pub struct Args {
    /// input SMT file name
    #[arg()]
    pub smt_file: PathBuf,
    /// Enable debug output. Level 0-5 controls verbosity
    #[arg(short, long, default_value_t = 0, value_parser = clap::value_parser!(u8).range(0..=30))]
    pub debug: u8,
    /// Enable eDRAT proof production and write to specified file
    #[arg(long)]
    pub proof: Option<PathBuf>,
    // /// Set the maximum activation depth for quantifier instantiations
    // #[arg(long, default_value_t = 5)]
    // pub max_activation_depth: usize,
    // /// Enable instantiation based on goal
    // #[arg(long)]
    // pub goal_based_instantiation: bool,
    #[cfg_attr(feature = "z3-solver", arg(long, default_value_t = ArithSolver::Z3, value_enum))]
    #[cfg_attr(not(feature = "z3-solver"), arg(long, default_value_t = ArithSolver::Internal, value_enum))]
    pub arithmetic: ArithSolver,
    /// Turns on lazy datatype instantiation for certain axioms
    #[arg(long, default_value_t = true)]
    pub lazy_dt: bool,
    /// Turns on certain (buggy) features to get ddsmt to properly shrink features (WARNING: do not use for real queries)
    #[arg(long, default_value_t = false)]
    pub ddsmt: bool,
    /// Eagerly skolemize every quantifier
    #[arg(long, default_value_t = false)]
    pub eager_skolem: bool,
    /// Set timeout in seconds (0 means no timeout)
    #[arg(long, default_value_t = 0)]
    pub timeout: u64,
    /// Directory to dump pure congruence-closure SMT benchmarks.
    /// Files contain only the equality/disequality literals on the current
    /// trail (Boolean structure is dropped). Trigger points are controlled
    /// by --cc-log-mode.
    #[arg(long)]
    pub cc_log: Option<PathBuf>,
    /// When to dump CC benchmarks. `conflict` dumps once per CC conflict
    /// reported by `process_assignment`. `instantiation` dumps once after
    /// each quantifier-instantiation round in `cb_check_found_model`.
    /// `both` enables both triggers.
    #[arg(long, default_value_t = CcLogMode::Conflict, value_enum)]
    pub cc_log_mode: CcLogMode,
}

/// What event triggers a CC benchmark dump.
#[derive(Debug, Clone, Copy, PartialEq, Eq, clap::ValueEnum)]
pub enum CcLogMode {
    /// Dump once per CC conflict reported by `process_assignment`.
    Conflict,
    /// Dump once per quantifier-instantiation round.
    Instantiation,
    /// Dump on both events.
    Both,
}
