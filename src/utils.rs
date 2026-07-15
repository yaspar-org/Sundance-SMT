// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! A file containting functions that may be useful elswhere

use rustc_hash::FxHasher;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::hash::BuildHasherDefault;
use yaspar_ir::ast::Term;

// Hash-based deterministic map using a fixed-seed FxHash. O(1) average ops
// and deterministic across runs (unlike std's RandomState), but iteration
// order depends on insertion sequence.
pub type DeterministicHashMap<K, V> = HashMap<K, V, BuildHasherDefault<FxHasher>>;
pub type DeterministicHashSet<T> = HashSet<T, BuildHasherDefault<FxHasher>>;

// Sorted-order map that implements Hash (required for use as a key/element
// in hash-based containers). Use only when the map itself must be hashable.
pub type HashableBTreeMap<K, V> = BTreeMap<K, V>;
pub type HashableBTreeSet<T> = BTreeSet<T>;

// Legacy alias — same as DeterministicHashMap now.
pub type FastDeterministicHashMap<K, V> = HashMap<K, V, BuildHasherDefault<FxHasher>>;
pub type FastDeterministicHashSet<T> = HashSet<T, BuildHasherDefault<FxHasher>>;

// Takes in a List of terms and returns a String (useful for debugging)
pub fn fmt_termlist(terms: Vec<Term>) -> String {
    let mut term_string = String::new();

    for term in terms {
        term_string.push_str(&term.to_string());
        term_string.push_str(", ");
    }

    term_string
}
