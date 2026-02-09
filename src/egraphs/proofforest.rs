// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! datastructures for proof forest inside of the egraph
use crate::egraphs::datastructures::DisequalTerm;
use crate::utils::{DeterministicHashMap, DeterministicHashSet};
use std::fmt;

/// Represents an edge in the egraph's proof forest
/// Each edge is either a root (i.e. it has not parent)
/// or is created by an equality or
#[derive(Debug, Clone)]
pub enum ProofForestEdge {
    /// Represents being the root
    Root {
        size: u64, // TODO: I don't know of a good way to recover the size when backtracking, so I need to figure out an efficient way to do this or maybe just remove size
        child: u64, // TODO: I am not 100% sure if child actually does anything, I think it is useful for reversing edges in the proof forest, but not 100% sure
        disequalities: DeterministicHashMap<u64, DisequalTerm>, // TODO: this might lead to a lot of allocations
        children: DeterministicHashSet<u64>,
    },
    /// Represents a node with an equality relationship
    Equality {
        term: Option<(u64, u64)>,
        size: u64,
        parent: u64,
        child: u64,
        disequalities: DeterministicHashMap<u64, DisequalTerm>,
        level: usize,
        hash: u64,
        children: DeterministicHashSet<u64>,
    },
    /// Represents a node with congruence relationships
    Congruence {
        pairs: Vec<(u64, u64)>,
        size: u64,
        parent: u64,
        child: u64,
        disequalities: DeterministicHashMap<u64, DisequalTerm>,
        level: usize,
        hash: u64,
        children: DeterministicHashSet<u64>,
    },
}

impl fmt::Display for ProofForestEdge {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProofForestEdge::Root {
                size,
                child,
                disequalities,
                children,
            } => {
                write!(
                    f,
                    "Root(size: {}, child: {:?}, disequalities: {:?}, children: {:?})",
                    size, child, disequalities, children
                )
            }
            ProofForestEdge::Equality {
                term: Some((t1, t2)),
                size,
                parent,
                child,
                disequalities,
                level,
                hash,
                children,
            } => {
                write!(
                    f,
                    "Equality({} = {}, size : {}, parent: {}, child : {:?}, disequalities: {:?}, level : {}, hash: {}, children : {:?})",
                    t1, t2, size, parent, child, disequalities, level, hash, children
                )
            }
            ProofForestEdge::Equality {
                term: None,
                size,
                parent,
                child,
                disequalities,
                level,
                hash,
                children,
            } => {
                write!(
                    f,
                    "Equality(None, size : {}, parent: {}, child: {:?}, disequalities: {:?}, level: {}, hash: {}, children: {:?})",
                    size, parent, child, disequalities, level, hash, children
                )
            }
            ProofForestEdge::Congruence {
                pairs,
                size,
                parent,
                child,
                disequalities,
                level,
                hash,
                children,
            } => {
                write!(
                    f,
                    "Congruence(pairs: {:?}, size : {}, parent: {}, child: {:?}, disequalities: {:?}, level: {}, hash: {}, children: {:?})",
                    pairs, size, parent, child, disequalities, level, hash, children
                )
            }
        }
    }
}

// TODO: equality used in comparison in proof_forest_backtrack, we don't want to actually compare disequalities because that could changes
impl PartialEq for ProofForestEdge {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                ProofForestEdge::Root { child: child1, .. },
                ProofForestEdge::Root { child: child2, .. },
            ) => child1 == child2,
            (
                ProofForestEdge::Equality {
                    term: term1,
                    parent: parent1,
                    child: child1,
                    ..
                },
                ProofForestEdge::Equality {
                    term: term2,
                    parent: parent2,
                    child: child2,
                    ..
                },
            ) => term1 == term2 && parent1 == parent2 && child1 == child2,
            (
                ProofForestEdge::Congruence {
                    parent: parent1,
                    child: child1,
                    ..
                },
                ProofForestEdge::Congruence {
                    parent: parent2,
                    child: child2,
                    ..
                },
            ) => parent1 == parent2 && child1 == child2,
            _ => false,
        }
    }
}

impl ProofForestEdge {
    /// Get the child of any ProofForestEdge
    pub fn get_child(&self) -> u64 {
        match self {
            ProofForestEdge::Root { child, .. }
            | ProofForestEdge::Equality { child, .. }
            | ProofForestEdge::Congruence { child, .. } => *child,
        }
    }

    /// Get the parent of a ProofForestEdge
    pub fn get_parent(&self) -> u64 {
        match self {
            ProofForestEdge::Root { .. } => panic!("Root does not have a parent"),
            ProofForestEdge::Equality { parent, .. }
            | ProofForestEdge::Congruence { parent, .. } => *parent,
        }
    }

    /// Get a reference to the disequalities vector for any ProofForestEdge variant
    pub fn disequalities(&self) -> &DeterministicHashMap<u64, DisequalTerm> {
        match self {
            ProofForestEdge::Root { disequalities, .. } => disequalities,
            ProofForestEdge::Equality { disequalities, .. } => disequalities,
            ProofForestEdge::Congruence { disequalities, .. } => disequalities,
        }
    }

    /// Get a reference to the children vector for any ProofForestEdge variant
    pub fn get_children(&self) -> &DeterministicHashSet<u64> {
        match self {
            ProofForestEdge::Root { children, .. }
            | ProofForestEdge::Equality { children, .. }
            | ProofForestEdge::Congruence { children, .. } => children,
        }
    }

    /// Get a mutable reference to the disequalities vector for any ProofForestEdge variant
    pub fn disequalities_mut(&mut self) -> &mut DeterministicHashMap<u64, DisequalTerm> {
        match self {
            ProofForestEdge::Root { disequalities, .. } => disequalities,
            ProofForestEdge::Equality { disequalities, .. } => disequalities,
            ProofForestEdge::Congruence { disequalities, .. } => disequalities,
        }
    }

    /// Set the disequalities in a ProofForestEdge
    pub fn set_disequalities(
        self,
        diseq: DeterministicHashMap<u64, DisequalTerm>,
    ) -> ProofForestEdge {
        match self {
            ProofForestEdge::Root {
                size,
                child,
                children,
                ..
            } => ProofForestEdge::Root {
                size,
                child,
                disequalities: diseq,
                children,
            },
            ProofForestEdge::Equality {
                term,
                size,
                parent,
                child,
                level,
                hash,
                children,
                ..
            } => ProofForestEdge::Equality {
                term,
                size,
                parent,
                child,
                level,
                hash,
                disequalities: diseq,
                children,
            },
            ProofForestEdge::Congruence {
                pairs,
                size,
                parent,
                child,
                level,
                hash,
                children,
                ..
            } => ProofForestEdge::Congruence {
                pairs,
                size,
                parent,
                child,
                level,
                hash,
                disequalities: diseq,
                children,
            },
        }
    }

    /// Add a single disequality to a ProofForestEdge
    pub fn add_disequality(&mut self, key: u64, t: DisequalTerm, hash_level_map: &[u64]) {
        let disequalities = match self {
            ProofForestEdge::Root { disequalities, .. } => disequalities, // TODO: not sure if I want this clone here, but its kind've hard to do references for disequalities
            ProofForestEdge::Equality { disequalities, .. } => disequalities,
            ProofForestEdge::Congruence { disequalities, .. } => disequalities,
        };
        // will only insert a disequality if is not already in the map
        // or if the hash is outdated (i.e. we have already backtracked on this disequality)
        if let Some(disequality) = disequalities.get(&key) {
            if disequality.hash != hash_level_map[disequality.level] && disequality.hash != 0 {
                debug_println!(
                    5,
                    0,
                    "We are inserting a disequality {:?} with key {}",
                    t,
                    key
                );
                // should only insert if the key hash is outdated (i.e. we have backtracked on this)
                disequalities.insert(key, t);
            }
        } else {
            debug_println!(
                5,
                0,
                "We are inserting a disequality {:?} with key {}",
                t,
                key
            );
            // should only insert if there is not a value for key
            disequalities.insert(key, t);
        }
    }
}
