// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Solver configuration and command line parsing

use crate::arithmetic::lp::ArithSolver;
use clap::Parser;
use std::path::PathBuf;
use std::str::FromStr;

/// Controls when assigned Boolean atoms are sent to the theory solvers.
///
/// These levels mirror Z3's relevancy modes:
/// - 0: disable relevancy filtering;
/// - 1: process irrelevant non-quantifier atoms eagerly;
/// - 2: process an assignment only after it becomes relevant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RelevancyLevel {
    Off,
    Level1,
    Level2,
}

impl RelevancyLevel {
    pub fn is_enabled(self) -> bool {
        !matches!(self, Self::Off)
    }

    pub fn eagerly_processes_irrelevant_atoms(self) -> bool {
        matches!(self, Self::Level1)
    }
}

impl FromStr for RelevancyLevel {
    type Err = String;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        match value.to_ascii_lowercase().as_str() {
            "0" | "false" | "off" => Ok(Self::Off),
            "1" | "true" | "on" => Ok(Self::Level1),
            "2" => Ok(Self::Level2),
            _ => Err(format!(
                "invalid relevancy level '{value}': expected 0, 1, 2, false, or true"
            )),
        }
    }
}

/// Match Z3's QF_UF configuration while preserving Sundance's current level-1
/// behavior for every other logic unless the user explicitly chooses a level.
pub fn resolve_relevancy_level(
    requested: Option<RelevancyLevel>,
    declared_logic: Option<&str>,
) -> RelevancyLevel {
    requested.unwrap_or_else(|| {
        if declared_logic == Some("QF_UF") {
            RelevancyLevel::Off
        } else {
            RelevancyLevel::Level1
        }
    })
}

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
    /// Enable quantifier instantiation garbage collection via activation literals.
    /// Only effective with lazy QI (--eager-qi 0).
    #[arg(long, default_value_t = false)]
    pub qi_gc: bool,
    /// Relevancy filtering level: 0/false=off, 1/true=eager atoms, 2=strict.
    /// Defaults to 0 for QF_UF and 1 for other logics.
    #[arg(long, num_args=0..=1, default_missing_value = "1")]
    pub relevancy: Option<RelevancyLevel>,
}

#[cfg(test)]
mod tests {
    use super::{Args, RelevancyLevel, resolve_relevancy_level};
    use clap::Parser;

    #[test]
    fn parses_legacy_and_numeric_relevancy_values() {
        for (value, expected) in [
            ("false", RelevancyLevel::Off),
            ("0", RelevancyLevel::Off),
            ("true", RelevancyLevel::Level1),
            ("1", RelevancyLevel::Level1),
            ("2", RelevancyLevel::Level2),
        ] {
            let args = Args::try_parse_from(["sundance-smt", "input.smt2", "--relevancy", value])
                .expect("relevancy value should parse");
            assert_eq!(args.relevancy, Some(expected));
        }
    }

    #[test]
    fn bare_relevancy_flag_selects_level_one() {
        let args = Args::try_parse_from(["sundance-smt", "input.smt2", "--relevancy"])
            .expect("bare relevancy flag should parse");
        assert_eq!(args.relevancy, Some(RelevancyLevel::Level1));
    }

    #[test]
    fn defaults_qf_uf_to_relevancy_off() {
        assert_eq!(
            resolve_relevancy_level(None, Some("QF_UF")),
            RelevancyLevel::Off
        );
        assert_eq!(
            resolve_relevancy_level(None, Some("UFDTLIA")),
            RelevancyLevel::Level1
        );
    }

    #[test]
    fn explicit_level_overrides_qf_uf_default() {
        assert_eq!(
            resolve_relevancy_level(Some(RelevancyLevel::Level2), Some("QF_UF")),
            RelevancyLevel::Level2
        );
    }
}
