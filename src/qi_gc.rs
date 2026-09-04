// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Clause-dependency tracking for quantifier-instantiation garbage collection.
//!
//! Every QI clause in an epoch contains the negative activation literal
//! `-activation`. Since no clause contains the positive activation literal,
//! resolution cannot remove `-activation`. A derived clause contains it if and
//! only if it still depends on some guarded QI clause from the epoch.

use crate::utils::{DeterministicHashMap, DeterministicHashSet};
use yaspar_ir::ast::{Local, Term};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct QiInstantiationKey {
    pub(crate) quantifier_id: u64,
    pub(crate) substitution: DeterministicHashMap<Local, Term>,
}

#[derive(Debug, Clone)]
pub(crate) struct QiRetainedInstance {
    pub(crate) key: QiInstantiationKey,
    pub(crate) clauses: Vec<Vec<i32>>,
    pub(crate) clause_terms: DeterministicHashSet<u64>,
}

#[derive(Debug, Default)]
pub(crate) struct QiGcPlan {
    /// Complete instance groups needed by a live derived clause.
    pub(crate) retained_instances: Vec<QiRetainedInstance>,
    /// Guarded QI clauses whose source instance could not be recovered, with
    /// `-activation` removed.
    pub(crate) retained_orphan_clauses: Vec<Vec<i32>>,
    /// Live derived clauses, with `-activation` removed.
    pub(crate) derived_clauses: Vec<Vec<i32>>,
    /// Number of guarded QI clauses observed in this epoch.
    pub(crate) observed_qi_clauses: usize,
    /// Number of derived-clause ancestry edges retained for the epoch.
    pub(crate) antecedent_edges: usize,
    /// Exact clause-term closure retained from this or earlier epochs.
    pub(crate) retained_term_uids: DeterministicHashSet<u64>,
    /// Terms pinned independently of the current epoch's guarded instances.
    pub(crate) permanent_term_uids: DeterministicHashSet<u64>,
    /// Every solver term owned by the current epoch. This includes terms first
    /// registered by its instances and dead terms carried from an earlier
    /// epoch because the egraph could not safely retire them yet.
    pub(crate) epoch_owned_term_uids: DeterministicHashSet<u64>,
}

#[derive(Debug, Default)]
pub(crate) struct QiGcTracker {
    next_group_id: u64,
    /// Instance group ID -> substitution identity and all ungated clauses.
    instance_groups: DeterministicHashMap<u64, QiRetainedInstance>,
    /// Normalized guarded clause -> instance groups awaiting the original
    /// clause callback that assigns a CaDiCaL clause ID.
    pending_clause_groups: DeterministicHashMap<Vec<i32>, Vec<u64>>,
    /// Guarded QI clause ID -> instance group ID.
    qi_clause_groups: DeterministicHashMap<u64, u64>,
    /// Fallback for a guarded QI clause whose registration callback could not
    /// be paired with an instance group.
    orphan_qi_clauses: DeterministicHashMap<u64, Vec<i32>>,
    /// Tainted derived clause ID -> antecedent IDs. Deleted clauses remain here
    /// because they may be intermediate nodes in a live clause's derivation.
    antecedents: DeterministicHashMap<u64, Vec<u64>>,
    /// Tainted derived clauses CaDiCaL has not deleted.
    live_derived: DeterministicHashMap<u64, Vec<i32>>,
    /// Terms whose lifetime is owned by the current guarded epoch.
    epoch_owned_term_uids: DeterministicHashSet<u64>,
    /// Terms referenced by permanent clauses from earlier transitions.
    permanent_term_uids: DeterministicHashSet<u64>,
}

#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct QiGcTrackerProfile {
    pub(crate) qi_clauses: usize,
    pub(crate) antecedent_nodes: usize,
    pub(crate) antecedent_edges: usize,
    pub(crate) live_derived: usize,
    pub(crate) instance_groups: usize,
    pub(crate) permanent_term_uids: usize,
}

impl QiGcTracker {
    fn normalize_clause(clause: &[i32]) -> Vec<i32> {
        let mut normalized = clause.to_vec();
        normalized.sort_unstable();
        normalized.dedup();
        normalized
    }

    fn strip_activation(clause: &[i32], activation: i32) -> Vec<i32> {
        clause
            .iter()
            .copied()
            .filter(|lit| *lit != -activation)
            .collect()
    }

    pub(crate) fn register_instance(
        &mut self,
        key: QiInstantiationKey,
        clauses: &[Vec<i32>],
        activation: i32,
        created_terms: &DeterministicHashSet<u64>,
        clause_terms: &DeterministicHashSet<u64>,
    ) {
        self.epoch_owned_term_uids
            .extend(created_terms.iter().copied());
        self.register_retained_instance(
            QiRetainedInstance {
                key,
                clauses: clauses.to_vec(),
                clause_terms: clause_terms.clone(),
            },
            activation,
        );
    }

    pub(crate) fn register_retained_instance(
        &mut self,
        instance: QiRetainedInstance,
        activation: i32,
    ) {
        let group_id = self.next_group_id;
        self.next_group_id += 1;
        for clause in &instance.clauses {
            let mut guarded = clause.clone();
            guarded.push(-activation);
            self.pending_clause_groups
                .entry(Self::normalize_clause(&guarded))
                .or_default()
                .push(group_id);
        }
        self.instance_groups.insert(group_id, instance);
    }

    pub(crate) fn note_gated_qi_clause(
        &mut self,
        id: u64,
        clause: &[i32],
        activation: i32,
    ) -> bool {
        if !clause.contains(&-activation) {
            return false;
        }
        let key = Self::normalize_clause(clause);
        let group = self.pending_clause_groups.get_mut(&key).and_then(Vec::pop);
        if self
            .pending_clause_groups
            .get(&key)
            .is_some_and(Vec::is_empty)
        {
            self.pending_clause_groups.remove(&key);
        }
        if let Some(group) = group {
            self.qi_clause_groups.insert(id, group);
        } else {
            self.orphan_qi_clauses
                .insert(id, Self::strip_activation(clause, activation));
        }
        true
    }

    pub(crate) fn note_derived_clause(
        &mut self,
        id: u64,
        clause: &[i32],
        antecedents: &[u64],
        activation: i32,
    ) -> bool {
        if !clause.contains(&-activation) {
            return false;
        }
        self.antecedents.insert(id, antecedents.to_vec());
        self.live_derived
            .insert(id, Self::strip_activation(clause, activation));
        true
    }

    pub(crate) fn note_deleted_clause(&mut self, id: u64) {
        self.live_derived.remove(&id);
    }

    pub(crate) fn plan(&self) -> QiGcPlan {
        let mut seen = DeterministicHashSet::default();
        let mut worklist: Vec<u64> = self.live_derived.keys().copied().collect();
        let mut required_groups = DeterministicHashSet::default();
        let mut required_orphans = DeterministicHashSet::default();

        while let Some(id) = worklist.pop() {
            if !seen.insert(id) {
                continue;
            }
            if let Some(group) = self.qi_clause_groups.get(&id) {
                required_groups.insert(*group);
            }
            if self.orphan_qi_clauses.contains_key(&id) {
                required_orphans.insert(id);
            }
            if let Some(parents) = self.antecedents.get(&id) {
                worklist.extend(parents.iter().copied());
            }
        }

        let mut retained_instances = Vec::new();
        let mut retained_term_uids = self.permanent_term_uids.clone();
        for group_id in &required_groups {
            let group = &self.instance_groups[group_id];
            retained_instances.push(group.clone());
            retained_term_uids.extend(group.clause_terms.iter().copied());
        }
        let retained_orphan_clauses = required_orphans
            .into_iter()
            .map(|id| self.orphan_qi_clauses[&id].clone())
            .collect();

        QiGcPlan {
            retained_instances,
            retained_orphan_clauses,
            derived_clauses: self.live_derived.values().cloned().collect(),
            observed_qi_clauses: self.qi_clause_groups.len() + self.orphan_qi_clauses.len(),
            antecedent_edges: self.antecedents.values().map(Vec::len).sum(),
            retained_term_uids,
            permanent_term_uids: self.permanent_term_uids.clone(),
            epoch_owned_term_uids: self.epoch_owned_term_uids.clone(),
        }
    }

    pub(crate) fn pending_clause_registrations(&self) -> usize {
        self.pending_clause_groups.values().map(Vec::len).sum()
    }

    pub(crate) fn pin_permanent_terms(&mut self, term_uids: impl IntoIterator<Item = u64>) {
        self.permanent_term_uids.extend(term_uids);
    }

    pub(crate) fn set_epoch_owned_terms(&mut self, term_uids: impl IntoIterator<Item = u64>) {
        self.epoch_owned_term_uids.clear();
        self.epoch_owned_term_uids.extend(term_uids);
    }

    pub(crate) fn clear_epoch(&mut self) {
        self.instance_groups.clear();
        self.pending_clause_groups.clear();
        self.qi_clause_groups.clear();
        self.orphan_qi_clauses.clear();
        self.antecedents.clear();
        self.live_derived.clear();
        self.epoch_owned_term_uids.clear();
    }

    pub(crate) fn profile(&self) -> QiGcTrackerProfile {
        QiGcTrackerProfile {
            qi_clauses: self.qi_clause_groups.len() + self.orphan_qi_clauses.len(),
            antecedent_nodes: self.antecedents.len(),
            antecedent_edges: self.antecedents.values().map(Vec::len).sum(),
            live_derived: self.live_derived.len(),
            instance_groups: self.instance_groups.len(),
            permanent_term_uids: self.permanent_term_uids.len(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn plan_keeps_only_qi_ancestors_of_live_tainted_clauses() {
        let mut tracker = QiGcTracker::default();
        assert!(tracker.note_gated_qi_clause(1, &[-5, 6, -100], 100));
        assert!(tracker.note_gated_qi_clause(2, &[-7, 8, -100], 100));
        assert!(tracker.note_derived_clause(10, &[6, -100], &[1, 40], 100));
        assert!(tracker.note_derived_clause(11, &[6, 9, -100], &[10, 41], 100));
        tracker.note_deleted_clause(10);

        let plan = tracker.plan();
        assert_eq!(plan.retained_orphan_clauses, vec![vec![-5, 6]]);
        assert!(plan.retained_instances.is_empty());
        assert_eq!(plan.derived_clauses, vec![vec![6, 9]]);
        assert_eq!(plan.observed_qi_clauses, 2);
        assert_eq!(plan.antecedent_edges, 4);
    }

    #[test]
    fn ignores_clauses_from_other_epochs() {
        let mut tracker = QiGcTracker::default();
        assert!(!tracker.note_gated_qi_clause(1, &[1, -99], 100));
        assert!(!tracker.note_derived_clause(2, &[2, -99], &[1], 100));
        assert_eq!(tracker.profile().qi_clauses, 0);
        assert_eq!(tracker.profile().live_derived, 0);
    }

    #[test]
    fn deleted_intermediate_clause_remains_in_ancestry() {
        let mut tracker = QiGcTracker::default();
        tracker.note_gated_qi_clause(1, &[3, -100], 100);
        tracker.note_derived_clause(2, &[4, -100], &[1], 100);
        tracker.note_derived_clause(3, &[5, -100], &[2], 100);
        tracker.note_deleted_clause(2);

        let plan = tracker.plan();
        assert_eq!(plan.retained_orphan_clauses, vec![vec![3]]);
        assert_eq!(plan.derived_clauses, vec![vec![5]]);
    }

    #[test]
    fn retained_clause_pins_terms_created_by_another_instance() {
        let mut tracker = QiGcTracker::default();
        let key = |quantifier_id| QiInstantiationKey {
            quantifier_id,
            substitution: DeterministicHashMap::default(),
        };
        let first_created = DeterministicHashSet::from_iter([10, 11]);
        let first_clause_terms = first_created.clone();
        tracker.register_instance(key(1), &[vec![1]], 100, &first_created, &first_clause_terms);

        let second_created = DeterministicHashSet::from_iter([20, 21]);
        let second_clause_terms = DeterministicHashSet::from_iter([10, 20]);
        tracker.register_instance(
            key(2),
            &[vec![2]],
            100,
            &second_created,
            &second_clause_terms,
        );

        tracker.note_gated_qi_clause(1, &[1, -100], 100);
        tracker.note_gated_qi_clause(2, &[2, -100], 100);
        tracker.note_derived_clause(3, &[3, -100], &[2], 100);

        let plan = tracker.plan();
        assert_eq!(plan.retained_instances.len(), 1);
        assert_eq!(plan.retained_instances[0].key.quantifier_id, 2);
        assert_eq!(plan.retained_term_uids, second_clause_terms);
        assert_eq!(
            plan.epoch_owned_term_uids,
            DeterministicHashSet::from_iter([10, 11, 20, 21])
        );
    }

    #[test]
    fn migrated_instances_remain_collectible_in_the_next_epoch() {
        let mut tracker = QiGcTracker::default();
        let instance = QiRetainedInstance {
            key: QiInstantiationKey {
                quantifier_id: 7,
                substitution: DeterministicHashMap::default(),
            },
            clauses: vec![vec![1, 2]],
            clause_terms: DeterministicHashSet::from_iter([10, 11]),
        };

        tracker.set_epoch_owned_terms([10, 11, 12]);
        tracker.register_retained_instance(instance, 200);
        assert!(tracker.note_gated_qi_clause(20, &[1, 2, -200], 200));
        assert!(tracker.note_derived_clause(21, &[2, -200], &[20], 200));

        let retained = tracker.plan();
        assert_eq!(retained.retained_instances.len(), 1);
        assert_eq!(
            retained.epoch_owned_term_uids,
            DeterministicHashSet::from_iter([10, 11, 12])
        );

        tracker.note_deleted_clause(21);
        let discarded = tracker.plan();
        assert!(discarded.retained_instances.is_empty());
        assert_eq!(
            discarded.epoch_owned_term_uids,
            DeterministicHashSet::from_iter([10, 11, 12])
        );
    }
}
