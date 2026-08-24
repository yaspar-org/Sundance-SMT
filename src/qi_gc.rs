// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Bookkeeping for garbage collection of quantifier-instantiation (QI) clauses.
//!
//! Quantifier instantiations are lemmas: sound, but only some of them turn out
//! to be useful. Left in CaDiCaL's clause database they slow every propagation
//! down for the rest of the search. To be able to drop them we gate each QI
//! implication behind a fresh *activation literal* `g`:
//!
//! ```text
//!   (-quantifier \/ body)        becomes        (-quantifier \/ body \/ -g)
//! ```
//!
//! `g` is handed to CaDiCaL through `cb_decide`, so it is a plain decision: no
//! reason clause is ever requested and `g` is never fixed at the root. That
//! makes the unit `[-g]` a sound thing to add later, and adding it permanently
//! satisfies — and therefore retires — every clause of that generation. A new
//! generation then gets a fresh `g`.
//!
//! The catch is that CaDiCaL's learned clauses mention `-g` too (as decision
//! context), so retiring a generation also throws away everything learned from
//! it. To avoid losing that work we record, per generation:
//!
//! * which original clauses are gated QI clauses (id -> ungated literals),
//! * which derived clauses mention an activation literal, and their antecedents.
//!
//! Since nothing ever contains `+g`, resolution can never remove `-g`: a derived
//! clause is reachable from a gated QI clause **iff** it mentions an activation
//! literal. That makes "mentions `g`" an exact taint test and keeps the recorded
//! antecedent graph small.
//!
//! At GC time [`QiGcTracker::plan`] walks that graph and returns the clauses to
//! re-add: every still-live tainted derived clause with its activation literals
//! stripped, plus the ungated form of every QI clause transitively needed to
//! derive them.

use crate::utils::{DeterministicHashMap, DeterministicHashSet};

/// Clauses that must be re-added to CaDiCaL when a QI generation is retired.
pub(crate) struct QiGcPlan {
    /// Ungated QI clauses that (transitively) justify a kept derived clause.
    pub(crate) qi_clauses: Vec<Vec<i32>>,
    /// Still-live derived clauses, with activation literals stripped.
    pub(crate) derived_clauses: Vec<Vec<i32>>,
}

#[derive(Default)]
pub(crate) struct QiGcTracker {
    /// Every activation variable ever allocated. Retired generations stay in
    /// here so that late `delete_clause` callbacks are still recognised as
    /// tainted.
    activation_vars: DeterministicHashSet<i32>,
    /// Gated QI clause id -> the same clause without its activation literal.
    qi_clauses: DeterministicHashMap<u64, Vec<i32>>,
    /// Tainted derived clause id -> antecedent ids. Kept even after the clause
    /// is deleted, since deleted clauses can still be intermediate steps on the
    /// path from a live derived clause to the QI clauses that justify it.
    antecedents: DeterministicHashMap<u64, Vec<u64>>,
    /// Live tainted derived clause id -> the clause with activation literals
    /// stripped. Entries are removed when CaDiCaL deletes the clause, so what
    /// remains at GC time is exactly what CaDiCaL still considers worth keeping.
    live_derived: DeterministicHashMap<u64, Vec<i32>>,
}

impl QiGcTracker {
    /// Start observing `var` as an activation variable.
    pub(crate) fn register_activation_var(&mut self, var: i32) {
        self.activation_vars.insert(var.abs());
    }

    /// Whether any literal of `clause` is an activation literal.
    pub(crate) fn is_tainted(&self, clause: &[i32]) -> bool {
        clause.iter().any(|lit| self.is_activation_lit(*lit))
    }

    pub(crate) fn is_activation_lit(&self, lit: i32) -> bool {
        self.activation_vars.contains(&lit.abs())
    }

    /// `clause` without its activation literals.
    pub(crate) fn strip(&self, clause: &[i32]) -> Vec<i32> {
        clause
            .iter()
            .copied()
            .filter(|lit| !self.is_activation_lit(*lit))
            .collect()
    }

    /// Record a gated QI clause CaDiCaL just took ownership of.
    pub(crate) fn note_gated_qi_clause(&mut self, id: u64, clause: &[i32]) {
        self.qi_clauses.insert(id, self.strip(clause));
    }

    /// Record a derived clause. Untainted clauses cannot reach a QI clause, so
    /// they are dropped immediately and cost nothing.
    pub(crate) fn note_derived_clause(&mut self, id: u64, clause: &[i32], antecedents: &[u64]) {
        if !self.is_tainted(clause) {
            return;
        }
        self.antecedents.insert(id, antecedents.to_vec());
        self.live_derived.insert(id, self.strip(clause));
    }

    /// Record that CaDiCaL dropped a clause; a dropped derived clause is one we
    /// will not bother re-adding.
    pub(crate) fn note_deleted_clause(&mut self, id: u64) {
        self.live_derived.remove(&id);
    }

    /// The clauses to re-add before retiring the current generation.
    pub(crate) fn plan(&self) -> QiGcPlan {
        // Walk back from every live tainted derived clause, collecting the QI
        // clauses that justify it. Intermediate derived clauses may already be
        // deleted, which is why `antecedents` outlives `live_derived`.
        let mut seen: DeterministicHashSet<u64> = DeterministicHashSet::default();
        let mut queue: Vec<u64> = self.live_derived.keys().copied().collect();
        let mut qi_ids: DeterministicHashSet<u64> = DeterministicHashSet::default();
        while let Some(id) = queue.pop() {
            if !seen.insert(id) {
                continue;
            }
            if self.qi_clauses.contains_key(&id) {
                qi_ids.insert(id);
            }
            if let Some(parents) = self.antecedents.get(&id) {
                queue.extend(parents.iter().copied());
            }
        }

        QiGcPlan {
            qi_clauses: qi_ids
                .iter()
                .map(|id| self.qi_clauses[id].clone())
                .collect(),
            derived_clauses: self.live_derived.values().cloned().collect(),
        }
    }

    /// Forget everything about the generation just retired. Activation variables
    /// are deliberately kept: their clauses are still being deleted by CaDiCaL
    /// and those callbacks must stay recognisable.
    pub(crate) fn start_new_generation(&mut self) {
        self.qi_clauses.clear();
        self.antecedents.clear();
        self.live_derived.clear();
    }

    /// Whether this generation has any gated QI clause worth retiring.
    pub(crate) fn has_gated_clauses(&self) -> bool {
        !self.qi_clauses.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tracker() -> QiGcTracker {
        let mut t = QiGcTracker::default();
        t.register_activation_var(100);
        t
    }

    #[test]
    fn taints_and_strips_only_activation_literals() {
        let t = tracker();
        assert!(t.is_tainted(&[1, -2, -100]));
        assert!(!t.is_tainted(&[1, -2]));
        assert_eq!(t.strip(&[1, -100, -2]), vec![1, -2]);
    }

    #[test]
    fn plan_collects_transitively_needed_qi_clauses() {
        let mut t = tracker();
        // Two gated QI clauses.
        t.note_gated_qi_clause(1, &[-5, 6, -100]);
        t.note_gated_qi_clause(2, &[-7, 8, -100]);
        // A derived clause from QI #1 only, then a second derived from that one.
        t.note_derived_clause(10, &[6, -100], &[1, 42]);
        t.note_derived_clause(11, &[6, 9, -100], &[10, 43]);
        // CaDiCaL keeps only the second one.
        t.note_deleted_clause(10);

        let plan = t.plan();
        assert_eq!(plan.derived_clauses, vec![vec![6, 9]]);
        // QI #1 is reached through the *deleted* clause 10; QI #2 is unrelated.
        assert_eq!(plan.qi_clauses, vec![vec![-5, 6]]);
    }

    #[test]
    fn untainted_derived_clauses_are_not_tracked() {
        let mut t = tracker();
        t.note_gated_qi_clause(1, &[-5, 6, -100]);
        t.note_derived_clause(10, &[6, 9], &[1]);
        let plan = t.plan();
        assert!(plan.derived_clauses.is_empty());
        assert!(plan.qi_clauses.is_empty());
    }

    #[test]
    fn new_generation_forgets_clauses_but_not_activation_vars() {
        let mut t = tracker();
        t.note_gated_qi_clause(1, &[-5, 6, -100]);
        assert!(t.has_gated_clauses());
        t.start_new_generation();
        assert!(!t.has_gated_clauses());
        assert!(t.is_tainted(&[-100]));
    }
}
