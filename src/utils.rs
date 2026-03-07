// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! A file containting functions that may be useful elswhere

use std::collections::{BTreeMap, BTreeSet};
use yaspar_ir::ast::Term;

// For collections that need deterministic iteration, we use BTreeMap/BTreeSet
// These maintain sorted order naturally, so iteration is always deterministic
pub type DeterministicHashMap<K, V> = BTreeMap<K, V>;
pub type DeterministicHashSet<T> = BTreeSet<T>;

// Takes in a List of terms and returns a String (useful for debugging)
pub fn fmt_termlist(terms: Vec<Term>) -> String {
    let mut term_string = String::new();

    for term in terms {
        term_string.push_str(&term.to_string());
        term_string.push_str(", ");
    }

    term_string
}
