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
    #[arg(long, default_value_t = ArithSolver::Z3, value_enum)]
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
}
