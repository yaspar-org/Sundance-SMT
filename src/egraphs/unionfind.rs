// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! A Union Find implementation that is used for finding short conflict clauses from the egraph
//! Once congruence closure discovers a conflict clause, we can sometimes shrink it further by
//! running a new union find algorithm
use std::collections::HashMap;

/// Value keeps of if a node is a root or what its parent is
#[derive(Debug, Clone)]
pub(crate) enum ProofTrackerValue {
    Root { size: i32 },
    Parent { parent: u64 },
}

/// Forest of the different proof trackers
pub struct ProofTracker {
    forest: HashMap<u64, ProofTrackerValue>,
}

impl ProofTracker {
    pub(crate) fn new() -> Self {
        ProofTracker {
            forest: HashMap::default(),
        }
    }

    /// unioning terms x and y
    pub fn union(&mut self, x: u64, y: u64) -> bool {
        debug_println!(
            5,
            2,
            "START OF PROCESS: We have the forest {:?} and x {} and y {}",
            self.forest,
            x,
            y
        );
        let x_root = self.find(x);
        let y_root = self.find(y);
        if x_root == y_root {
            debug_println!(4, 3, "Pair ({}, {}) already in same set", x, y);
            return false;
        }
        debug_println!(4, 2, "Processing pair ({}, {})", x, y);
        // this is safe because x_root and y_root get set in find
        let x_root_val = self.forest[&x_root].clone();
        let y_root_val = self.forest[&y_root].clone();

        let x_root_size = match x_root_val {
            ProofTrackerValue::Root { size } => size,
            ProofTrackerValue::Parent { .. } => {
                panic!("This should be a root")
            }
        };
        let y_root_size = match y_root_val {
            ProofTrackerValue::Root { size } => size,
            ProofTrackerValue::Parent { .. } => {
                panic!("This should be a root")
            }
        };

        debug_println!(
            4,
            2,
            "x_root: {}, x_root_val: {:?}, y_root: {}, y_root_val: {:?}",
            x_root,
            x_root_val,
            y_root,
            y_root_val
        );

        debug_println!(4, 2, "PRE-UNION We have the forest {:?}", self.forest);

        // picking the smaller root to be the head
        if x_root_size < y_root_size {
            debug_println!(
                4,
                2,
                "Making {} have value {} and {} have value {}",
                y_root,
                x_root,
                x_root,
                x_root_size + y_root_size
            );
            self.forest
                .insert(y_root, ProofTrackerValue::Parent { parent: x_root });
            self.forest.insert(
                x_root,
                ProofTrackerValue::Root {
                    size: x_root_size + y_root_size,
                },
            );
        } else {
            debug_println!(
                4,
                2,
                "Making {} have value {} and {} have value {}",
                x_root,
                y_root,
                y_root,
                x_root_size + y_root_size
            );
            self.forest
                .insert(x_root, ProofTrackerValue::Parent { parent: y_root });
            self.forest.insert(
                y_root,
                ProofTrackerValue::Root {
                    size: x_root_size + y_root_size,
                },
            );
        }
        debug_println!(4, 2, "POST-UNION We have the forest {:?}", self.forest);
        true
    }

    fn find(&mut self, x: u64) -> u64 {
        debug_println!(
            5,
            0,
            "We are in find with x {} and forest {:?}",
            x,
            self.forest
        );
        let next = self.forest.get(&x);
        if let Some(next) = next {
            debug_println!(0, 3, "Following path {} -> {:?} in proof tracker", x, next);
            match next {
                ProofTrackerValue::Root { size: _ } => x,
                ProofTrackerValue::Parent { parent } => self.find(*parent),
            }
        } else {
            debug_println!(0, 3, "Found root {} in proof tracker", x);
            self.forest.insert(x, ProofTrackerValue::Root { size: 1 });
            x
        }
    }
}
