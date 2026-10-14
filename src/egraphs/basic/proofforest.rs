// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! datastructures for proof forest inside of the egraph
use super::datastructures::DisequalTerm;
use super::egraph::valid_hash;
use crate::debug_println;
use crate::utils::{DeterministicHashMap, DeterministicHashSet};
use std::fmt;

/// Represents an edge in the egraph's proof forest
/// Each edge is either a root (i.e. it has not parent)
/// or is created by an equality or
#[derive(Debug, Clone)]
pub(super) enum ProofForestEdge {
    /// Represents being the root
    Root {
        size: u32, // TODO: I don't know of a good way to recover the size when backtracking, so I need to figure out an efficient way to do this or maybe just remove size
        child: u32, // TODO: I am not 100% sure if child actually does anything, I think it is useful for reversing edges in the proof forest, but not 100% sure
        disequalities: DeterministicHashMap<u32, DisequalTerm>, // TODO: this might lead to a lot of allocations
        children: DeterministicHashSet<u32>,
        /// True iff the class contains an Int-sorted term. `cc_union`
        /// propagates the flag with OR: if either pre-merge root is tagged,
        /// the surviving root becomes tagged.
        arithmetic: bool,
    },
    /// Represents a node with an equality relationship
    Equality {
        term: Option<(u32, u32)>,
        size: u32,
        parent: u32,
        child: u32,
        disequalities: DeterministicHashMap<u32, DisequalTerm>,
        level: usize,
        hash: u32,
        children: DeterministicHashSet<u32>,
    },
    /// Represents a node with congruence relationships
    Congruence {
        pairs: Vec<(u32, u32)>,
        size: u32,
        parent: u32,
        child: u32,
        disequalities: DeterministicHashMap<u32, DisequalTerm>,
        level: usize,
        hash: u32,
        children: DeterministicHashSet<u32>,
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
                arithmetic,
            } => {
                write!(
                    f,
                    "Root(size: {}, child: {:?}, disequalities: {:?}, children: {:?}, arithmetic: {})",
                    size, child, disequalities, children, arithmetic
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
    pub(super) fn get_child(&self) -> u32 {
        match self {
            ProofForestEdge::Root { child, .. }
            | ProofForestEdge::Equality { child, .. }
            | ProofForestEdge::Congruence { child, .. } => *child,
        }
    }

    /// Get the parent of a ProofForestEdge
    pub(super) fn get_parent(&self) -> u32 {
        match self {
            ProofForestEdge::Root { .. } => panic!("Root does not have a parent"),
            ProofForestEdge::Equality { parent, .. }
            | ProofForestEdge::Congruence { parent, .. } => *parent,
        }
    }

    /// Get a reference to the disequalities vector for any ProofForestEdge variant
    pub(super) fn disequalities(&self) -> &DeterministicHashMap<u32, DisequalTerm> {
        match self {
            ProofForestEdge::Root { disequalities, .. } => disequalities,
            ProofForestEdge::Equality { disequalities, .. } => disequalities,
            ProofForestEdge::Congruence { disequalities, .. } => disequalities,
        }
    }

    /// Get a mutable reference to the disequalities vector for any ProofForestEdge variant
    pub(super) fn disequalities_mut(&mut self) -> &mut DeterministicHashMap<u32, DisequalTerm> {
        match self {
            ProofForestEdge::Root { disequalities, .. } => disequalities,
            ProofForestEdge::Equality { disequalities, .. } => disequalities,
            ProofForestEdge::Congruence { disequalities, .. } => disequalities,
        }
    }

    /// Set the disequalities in a ProofForestEdge
    pub(super) fn set_disequalities(
        self,
        diseq: DeterministicHashMap<u32, DisequalTerm>,
    ) -> ProofForestEdge {
        match self {
            ProofForestEdge::Root {
                size,
                child,
                children,
                arithmetic,
                ..
            } => ProofForestEdge::Root {
                size,
                child,
                disequalities: diseq,
                children,
                arithmetic,
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

    /// Set the parent and child fields of a non-root edge.
    pub(super) fn with_parent(
        self,
        parent: u32,
        new_child: u32,
        level: usize,
        hash: u32,
    ) -> ProofForestEdge {
        match self {
            ProofForestEdge::Root { .. } => {
                panic!("Cannot add a parent to a root");
            }
            ProofForestEdge::Congruence {
                size,
                pairs,
                disequalities,
                children,
                ..
            } => ProofForestEdge::Congruence {
                size,
                pairs,
                parent,
                child: new_child,
                disequalities,
                level,
                hash,
                children,
            },
            ProofForestEdge::Equality {
                size,
                term,
                disequalities,
                children,
                ..
            } => ProofForestEdge::Equality {
                size,
                term,
                parent,
                child: new_child,
                disequalities,
                level,
                hash,
                children,
            },
        }
    }

    /// Add a single disequality to a ProofForestEdge
    pub(super) fn add_disequality(&mut self, key: u32, t: DisequalTerm, hash_level_map: &[u32]) {
        let disequalities = match self {
            ProofForestEdge::Root { disequalities, .. } => disequalities, // TODO: not sure if I want this clone here, but its kind've hard to do references for disequalities
            ProofForestEdge::Equality { disequalities, .. } => disequalities,
            ProofForestEdge::Congruence { disequalities, .. } => disequalities,
        };
        // will only insert a disequality if is not already in the map
        // or if the hash is outdated (i.e. we have already backtracked on this disequality).
        // Use the same validity test as everywhere else (`valid_hash`): an entry recorded
        // after a backtrack to a level above its own carries a hash *greater* than
        // `hash_level_map[level]` and is still in force. Treating it as outdated would
        // replace it with this (higher-level) disequality, and backtracking past that
        // level would then leave the class with no record of the still-asserted one.
        if let Some(disequality) = disequalities.get(&key) {
            if !valid_hash(disequality.hash, disequality.level, hash_level_map) {
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

#[cfg(test)]
mod tests {
    use super::*;

    fn diseq(diseq_lit: i32, level: usize, hash: u32) -> DisequalTerm {
        DisequalTerm {
            term: 7,
            level,
            diseq_lit,
            hash,
            original_disequality: (3, 7),
        }
    }

    fn root() -> ProofForestEdge {
        ProofForestEdge::Root {
            size: 1,
            child: 0,
            disequalities: DeterministicHashMap::new(),
            children: DeterministicHashSet::new(),
            arithmetic: false,
        }
    }

    /// A disequality recorded at level 2 after the solver had already backtracked
    /// (so its hash, 5, is newer than level 2's invalidation stamp, 4) is still in
    /// force. Adding a second disequality between the same classes at level 3 must
    /// keep it: otherwise backtracking to level 2 drops the only record of a
    /// disequality that is still asserted.
    #[test]
    fn add_disequality_keeps_valid_lower_level_entry() {
        // predecessor_level stamps per level: level 2 was last invalidated at hash 4.
        let stamps = [0, 0, 4, 4];
        let mut edge = root();
        edge.add_disequality(7, diseq(-10, 2, 5), &stamps);
        edge.add_disequality(7, diseq(-11, 3, 5), &stamps);
        assert_eq!(edge.disequalities()[&7].diseq_lit, -10);
    }

    /// An entry whose level was backtracked over (hash older than the stamp) is
    /// replaced.
    #[test]
    fn add_disequality_replaces_outdated_entry() {
        let stamps = [0, 0, 6, 6];
        let mut edge = root();
        edge.add_disequality(7, diseq(-10, 2, 5), &stamps);
        edge.add_disequality(7, diseq(-11, 2, 6), &stamps);
        assert_eq!(edge.disequalities()[&7].diseq_lit, -11);
    }
}
