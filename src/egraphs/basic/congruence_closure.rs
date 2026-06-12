// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Proof forest helpers (add_parent, get_parent, get_child).

use crate::debug_println;
use super::proofforest::ProofForestEdge;

pub(crate) fn add_parent(
    proof_parent: ProofForestEdge,
    parent: u32,
    new_child: u32,
    level: usize,
    hash: u32,
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

pub fn get_parent(proof_parent: &ProofForestEdge) -> u32 {
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

pub fn get_child(proof_parent: &ProofForestEdge) -> u32 {
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
