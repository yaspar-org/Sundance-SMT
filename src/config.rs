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

    // --- Quantifier instantiation cost weights (Z3-style prioritization) ---
    // Candidate instantiations are materialized cheapest-first. Each weight
    // scales one term of the cost function; see `CostWeights`. Raising a weight
    // makes that factor push instantiations later.
    /// Cost weight on instantiation generation (depth).
    #[arg(long, default_value_t = 1.0)]
    pub qi_w_gen: f64,
    /// Cost weight on the quantifier `:weight` annotation.
    #[arg(long, default_value_t = 1.0)]
    pub qi_w_weight: f64,
    /// Cost weight on log2(1 + body size).
    #[arg(long, default_value_t = 0.5)]
    pub qi_w_size: f64,
    /// Cost weight on body term depth.
    #[arg(long, default_value_t = 0.5)]
    pub qi_w_depth: f64,
    /// Cost weight on the number of bound variables.
    #[arg(long, default_value_t = 0.0)]
    pub qi_w_vars: f64,
    /// Cost weight on the firing multipattern width.
    #[arg(long, default_value_t = 0.0)]
    pub qi_w_pattern_width: f64,
    /// Cost weight on (branch-local + total) instances of the quantifier.
    #[arg(long, default_value_t = 1.0)]
    pub qi_w_instances: f64,
    /// Cost weight on the search scope (decision level).
    #[arg(long, default_value_t = 0.0)]
    pub qi_w_scope: f64,
    /// Cost weight on the case-split factor (body disjunct count).
    #[arg(long, default_value_t = 0.0)]
    pub qi_w_cs_factor: f64,
}

/// Weights for the quantifier-instantiation cost function. Bundled out of
/// [`Args`] so they can be threaded through the solver as one value.
#[derive(Debug, Clone, Copy)]
pub struct CostWeights {
    pub generation: f64,
    pub weight: f64,
    pub size: f64,
    pub depth: f64,
    pub vars: f64,
    pub pattern_width: f64,
    pub instances: f64,
    pub scope: f64,
    pub cs_factor: f64,
}

impl Default for CostWeights {
    fn default() -> Self {
        CostWeights {
            generation: 1.0,
            weight: 1.0,
            size: 0.5,
            depth: 0.5,
            vars: 0.0,
            pattern_width: 0.0,
            instances: 1.0,
            scope: 0.0,
            cs_factor: 0.0,
        }
    }
}

impl Args {
    /// Collect the quantifier-instantiation cost weights from parsed args.
    pub fn cost_weights(&self) -> CostWeights {
        CostWeights {
            generation: self.qi_w_gen,
            weight: self.qi_w_weight,
            size: self.qi_w_size,
            depth: self.qi_w_depth,
            vars: self.qi_w_vars,
            pattern_width: self.qi_w_pattern_width,
            instances: self.qi_w_instances,
            scope: self.qi_w_scope,
            cs_factor: self.qi_w_cs_factor,
        }
    }
}
