// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! A file containting functions that may be useful elswhere

use rustc_hash::FxHasher;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::hash::BuildHasherDefault;
use yaspar_ir::ast::Term;

// Sorted-order deterministic map. Iteration order is canonical (sorted by key),
// so these also implement Hash and can be used as keys in other hash-based
// containers. Use this when you need canonical equality or sorted iteration.
pub type DeterministicHashMap<K, V> = BTreeMap<K, V>;
pub type DeterministicHashSet<T> = BTreeSet<T>;

// Hash-based deterministic map using a fixed-seed FxHash. O(1) average ops
// and deterministic across runs (unlike std's RandomState), but iteration
// order depends on insertion sequence and these do not implement Hash.
// Prefer this on hot paths where sorted iteration is not required.
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
