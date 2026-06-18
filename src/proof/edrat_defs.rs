// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Definitions necessary for building eDRAT proofs.
//!
use yaspar_ir::ast::{Sort, Str};

/// An SMT theory. They are represented by a `usize`.
/// At the top of the eDRAT proof, `define-theory` lines are included
/// so theory lemmas can reference the theory succinctly.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[allow(unused)]
pub enum Theory {
    QfUf,
    QfLra,
    QfLia,
    QfLira,
    Datatypes,
    Boolean,
    Background,
}

#[derive(Debug, Clone)]
pub enum ProofStepType {
    /// A constraint found in the original SMT formula, translated to SAT.
    OriginalClause,
    /// A learned clause, derived via CDCL by the SAT solver. See `ProofTracer.add_derived_clause()`.
    SATClause,
    /// A DRAT-style clause deletion. Despite CaDiCaL returning a clause ID, we store the entire clause.
    Deletion,
    /// A constraint derived via theory reasoning in the SMT solver.
    TheoryClause(Theory),
    /// A clause derived via Skolemization of an existential/negated-forall term.
    Skolemization {
        /// The DIMACS literal for the term getting Skolemized. Should be a literal in the clause.
        parent_term: i32,
        /// The fresh Skolem variables allocated for the Skolemization.
        skolem_vars: Vec<(Str, Sort)>,
    },
    /// A clause derived via quantifier instantiation.
    Instantiation,
}

/// Represents a single step in the eDRAT proof.
#[derive(Debug, Clone)]
pub struct ProofStep {
    /// The DIMACS-style literals of the clause.
    pub(crate) clause: Vec<i32>,
    /// What kind of clause it is.
    pub(crate) typ: ProofStepType,
}

////////////////////////////////////////////////////////////////////////////////
// Theory
////////////////////////////////////////////////////////////////////////////////

impl Theory {
    /// Gets the short "tag" string that appears after the leading `t` in an eDRAT proof line.
    fn get_tag(&self) -> &str {
        match self {
            Self::QfUf => "uf",
            Self::QfLra => "lra",
            Self::QfLia => "lia",
            Self::QfLira => "lira",
            Self::Datatypes => "dt",
            Self::Boolean => "b",
            Self::Background => "bg",
        }
    }
}
impl std::fmt::Display for Theory {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.get_tag())
    }
}

////////////////////////////////////////////////////////////////////////////////
// ProofStepType
////////////////////////////////////////////////////////////////////////////////

impl ProofStepType {
    fn get_prefix_str(&self) -> String {
        match self {
            Self::OriginalClause => "a ".to_string(),
            Self::SATClause => "".to_string(),
            Self::Deletion => "d ".to_string(),
            Self::TheoryClause(t) => format!("t {} ", t.get_tag()).to_string(),
            Self::Skolemization { .. } => "s ".to_string(),
            Self::Instantiation => "q ".to_string(),
        }
    }
}

impl ProofStep {
    pub fn push_line_to(&self, output: &mut String) {
        output.push_str(&self.typ.get_prefix_str());
        for lit in &self.clause {
            output.push_str(&format!("{} ", lit));
        }
        output.push_str("0\n");
    }
}
