// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Proof forest helpers (add_parent, get_parent, get_child).

use crate::debug_println;
use crate::egraphs::proofforest::ProofForestEdge;

pub fn add_parent(
    proof_parent: ProofForestEdge,
    parent: u64,
    new_child: u64,
    level: usize,
    hash: u64,
) -> ProofForestEdge {
    match proof_parent {
        ProofForestEdge::Root {
            size: _,
            child: _,
            disequalities: _,
            children: _,
        } => {
            panic!("ERROR: We are trying to add a parent to a root1");
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

pub fn get_parent(proof_parent: &ProofForestEdge) -> u64 {
    debug_println!(6, 0, "We are getting the parent of {:?}", proof_parent);
    match proof_parent {
        ProofForestEdge::Root { .. } => {
            panic!("ERROR: We are trying to add a parent to a root2");
        }
        ProofForestEdge::Congruence {
            parent: proof_parent,
            ..
        } => *proof_parent,
        ProofForestEdge::Equality {
            parent: proof_parent,
            ..
        } => *proof_parent,
    }
}

pub fn get_child(proof_parent: &ProofForestEdge) -> u64 {
    match proof_parent {
        ProofForestEdge::Root {
            child,
            disequalities: _,
            ..
        } => *child,
        ProofForestEdge::Congruence { child, .. } => *child,
        ProofForestEdge::Equality { child, .. } => *child,
    }
}
