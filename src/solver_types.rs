// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Solver-level types that don't belong in the egraph module.
//! These types use solver UIDs (u64) and reference yaspar Term/Str types.

use std::fmt;
use yaspar_ir::ast::{Str, Term};

/// Represents an assertion that we may need to process
#[derive(Debug, Clone, PartialEq)]
pub enum Assertion {
    Equality {
        t1: u64,
        t2: u64,
        level: usize,
        hash: u32,
    },
    Disequality {
        t1: u64,
        t2: u64,
        level: usize,
        hash: u32,
    },
    Distinct {
        terms: Vec<u64>,
        level: usize,
        hash: u32,
    },
    Tester {
        ctor_name: Str,
        inner_term: Term,
        term: Term,
    },
    Other,
}

/// Represents a Datatype Type
pub enum ConstructorType {
    Uninitialized,
    Constructor {
        name: Str,
        tester_term: Term,
        /// UIDs of the constructor's child terms (selector applications or direct subterms)
        children: Vec<u64>,
        level: usize,
        hash: u32,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct Quantifier {
    pub triggers: Vec<Vec<crate::egraphs::repr::PatternId>>,
    pub variables: Vec<String>,
    pub body: u64,
    pub id: u64,
    pub guard: Option<u64>,
    pub polarity: Polarity,
    pub skolemized: bool,
    /// SMT-LIB `:weight` annotation (default 1). Higher weight => more expensive
    /// => instantiated later. Feeds the instantiation cost function.
    pub weight: u32,
    /// Number of sub-expressions in the quantifier body (cached at registration).
    pub body_size: u32,
    /// Term depth of the quantifier body (cached at registration).
    pub body_depth: u32,
    /// Case-split factor: number of top-level disjuncts in the body (>= 1).
    pub cs_factor: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Polarity {
    Universal,
    Existential,
}

/// An enum representing different states of a term
#[derive(Debug, Clone, PartialEq)]
pub enum TermOption {
    None,
    Some(Term),
    Uninitialized(Term),
}

impl TermOption {
    pub fn unwrap(self) -> Term {
        match self {
            TermOption::Some(term) => term,
            TermOption::Uninitialized(term) => term,
            TermOption::None => panic!("called `TermOption::unwrap()` on a `None` value"),
        }
    }

    pub fn is_none(&self) -> bool {
        matches!(self, TermOption::None)
    }

    pub fn display(&self) -> String {
        match self {
            TermOption::Some(term) => term.to_string(),
            TermOption::Uninitialized(term) => term.to_string(),
            TermOption::None => "None".to_string(),
        }
    }
}

impl fmt::Display for TermOption {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.display())
    }
}
