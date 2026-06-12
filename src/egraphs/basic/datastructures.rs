// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Egraph-internal datastructures (use u32 egraph IDs, no yaspar dependency).

use std::{cmp::Ordering, fmt};

/// Keeps track of disequalities used between multiple terms
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct DisequalTerm {
    pub(crate) term: u32,
    pub(crate) level: usize,
    pub(crate) diseq_lit: i32,
    pub(crate) hash: u32,
    pub(crate) original_disequality: (u32, u32),
}

impl fmt::Display for DisequalTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "DisequalTerm(term: {}, level: {}, hash: {}, original_disequality: {:?})",
            self.term, self.level, self.hash, self.original_disequality
        )
    }
}

/// Identifies the "operator" of a canonical term form for the purposes of
/// congruence-closure lookup.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum CanonicalOp {
    App(String),
    Eq,
    Ite,
}

/// The canonical form of a term, produced by `Egraph::get_canonical_form`.
#[derive(Debug, Clone)]
pub(crate) struct CanonicalForm {
    pub(crate) original_subterms: Vec<u32>,
    pub(crate) op: CanonicalOp,
    pub(crate) canonical_subterms: Vec<u32>,
}

/// Represents a predecessor of a term
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub(crate) struct Predecessor {
    pub(crate) level: usize,
    pub(crate) hash: u32,
    pub(crate) predecessor: u32,
    pub(crate) inner_term: u32,
}

impl Ord for Predecessor {
    fn cmp(&self, other: &Self) -> Ordering {
        self.level.cmp(&(other.level))
    }
}

impl PartialOrd for Predecessor {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
