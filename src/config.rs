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
    /// Dump the eDRAT proof forest at termination for any result; complete on unsat, else a prefix. Mutually exclusive with --proof
    #[arg(long, conflicts_with = "proof")]
    pub partial_proof: Option<PathBuf>,
    /// Log each refuted propositional model to this file. Line-tagged format, streamed as the search runs: `t <signed lits>` per refuted model, then `m <var> <atom>` map lines appended at the end
    #[arg(long)]
    pub trail_out: Option<PathBuf>,
    // /// Set the maximum activation depth for quantifier instantiations
    // #[arg(long, default_value_t = 5)]
    // pub max_activation_depth: usize,
    // /// Enable instantiation based on goal
    // #[arg(long)]
    // pub goal_based_instantiation: bool,
    #[cfg_attr(feature = "z3-solver", arg(long, default_value_t = ArithSolver::Z3Incremental, value_enum))]
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
    /// Max quantifier instantiations to add eagerly at each decision level.
    /// A negative value exhausts one fresh matching round per level; 0 disables eager QI.
    #[arg(long, default_value_t = 0, allow_negative_numbers = true)]
    pub eager_qi: i32,
    /// Relevancy filtering of e-matching and instantiation : `off` (default), `final` (the complete-model matching round is
    /// filtered, with an unfiltered retry when it yields nothing), or `eager`
    /// (eager matching rounds at every decision level, filtered).
    #[arg(long, default_value = "off", value_parser = ["off", "final", "eager"])]
    pub relevancy: String,
    /// Bound on the generation of quantifier instances (Z3's
    /// `qi.eager_threshold` with the default cost): an input term has
    /// generation 0, an instance one more than the largest generation among
    /// its bindings. A match above the bound is left for a later round; the
    /// complete-model round retries when nothing is below it, raising the
    /// bound one generation at a time. Default 5 (Z3's default threshold);
    /// 0 is unbounded. Same as ``SUNDANCE_QI_MAX_GEN=<n>``, which takes precedence
    /// when set.
    #[arg(long, default_value_t = 5)]
    pub max_generation: u32,
    /// Incremental e-matching (top-down matcher): a round
    /// matches only at root candidates whose class, or a class below it
    /// within the pattern's depth, changed since the previous round. Same as
    /// SUNDANCE_INCR_MATCH=1. Off by default.
    #[arg(long, default_value_t = false)]
    pub incremental_matching: bool,
    /// Infer triggers for `forall` quantifiers that lack a `:pattern` annotation
    /// (Simplify/Z3-style auto-trigger inference). When off (default), an
    /// untriggered `forall` panics instead.
    #[arg(long, default_value_t = false)]
    pub infer_triggers: bool,
    /// CaDiCaL elevate setting for lazy quantifier instantiation (0 to disable)
    #[arg(long, default_value_t = 3)]
    pub elevate: i32,
    /// Set timeout in seconds (0 means no timeout)
    #[arg(long, default_value_t = 0)]
    pub timeout: u64,
    /// Print solver statistics after solving
    #[arg(long, default_value_t = false)]
    pub stats: bool,
    /// Max arithmetic-model conflicts collected per model-check (usize::MAX = uncapped).
    #[arg(long, default_value_t = usize::MAX)]
    pub max_arith_conflicts_per_round: usize,
    /// Max pending quantifier materialization steps per complete-model check (instantiations + skolemizations).
    /// 0 = unbounded (materialize all pending).
    #[arg(long, default_value_t = 85)]
    pub batch_cap: usize,
}
