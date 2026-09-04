// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Clause-dependency tracking for quantifier-instantiation garbage collection.
//!
//! Every QI clause in an epoch contains the negative activation literal
//! `-activation`. Since no clause contains the positive activation literal,
//! resolution cannot remove `-activation`. A derived clause contains it if and
//! only if it still depends on some guarded QI clause from the epoch.

use crate::utils::{DeterministicHashMap, DeterministicHashSet};
use std::collections::HashSet;
use yaspar_ir::ast::{Local, Term};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct QiInstantiationKey {
    pub(crate) quantifier_id: u64,
    pub(crate) substitution: DeterministicHashMap<Local, Term>,
}

#[derive(Debug)]
struct QiInstanceGroup {
    key: QiInstantiationKey,
    clauses: Vec<Vec<i32>>,
    created_terms: DeterministicHashSet<u64>,
    referenced_terms: DeterministicHashSet<u64>,
}

#[derive(Debug, Default)]
pub(crate) struct QiGcPlan {
    /// Guarded QI clauses needed by a live derived clause, with `-activation`
    /// removed.
    pub(crate) qi_clauses: Vec<Vec<i32>>,
    /// Live derived clauses, with `-activation` removed.
    pub(crate) derived_clauses: Vec<Vec<i32>>,
    /// Number of guarded QI clauses observed in this epoch.
    pub(crate) observed_qi_clauses: usize,
    /// Number of derived-clause ancestry edges retained for the epoch.
    pub(crate) antecedent_edges: usize,
    /// Instantiations whose complete clause groups were retained.
    pub(crate) retained_instantiations: Vec<QiInstantiationKey>,
    /// Terms referenced by retained instances from this or earlier epochs.
    pub(crate) retained_term_uids: DeterministicHashSet<u64>,
    /// Terms created only by discarded instances and not referenced by any
    /// retained instance. These are candidates for physical reclamation.
    pub(crate) retired_candidate_term_uids: DeterministicHashSet<u64>,
}

#[derive(Debug, Default)]
pub(crate) struct QiGcTracker {
    next_group_id: u64,
    /// Instance group ID -> substitution identity and all ungated clauses.
    instance_groups: DeterministicHashMap<u64, QiInstanceGroup>,
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
    /// Substitutions whose QI clauses were promoted in an earlier transition.
    permanent_instantiations: HashSet<QiInstantiationKey>,
    /// Terms referenced by promoted instance groups from earlier transitions.
    permanent_term_uids: DeterministicHashSet<u64>,
}

#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct QiGcTrackerProfile {
    pub(crate) qi_clauses: usize,
    pub(crate) antecedent_nodes: usize,
    pub(crate) antecedent_edges: usize,
    pub(crate) live_derived: usize,
    pub(crate) instance_groups: usize,
    pub(crate) permanent_instantiations: usize,
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
        referenced_terms: &DeterministicHashSet<u64>,
    ) {
        let group_id = self.next_group_id;
        self.next_group_id += 1;
        self.instance_groups.insert(
            group_id,
            QiInstanceGroup {
                key,
                clauses: clauses.to_vec(),
                created_terms: created_terms.clone(),
                referenced_terms: referenced_terms.clone(),
            },
        );
        for clause in clauses {
            let mut guarded = clause.clone();
            guarded.push(-activation);
            self.pending_clause_groups
                .entry(Self::normalize_clause(&guarded))
                .or_default()
                .push(group_id);
        }
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

        let mut qi_clauses = Vec::new();
        let mut retained_instantiations = Vec::new();
        let mut retained_term_uids = self.permanent_term_uids.clone();
        let mut retired_candidate_term_uids = DeterministicHashSet::default();
        for (group_id, group) in &self.instance_groups {
            if !required_groups.contains(group_id) {
                retired_candidate_term_uids.extend(group.created_terms.iter().copied());
            }
        }
        for group_id in required_groups {
            let group = &self.instance_groups[&group_id];
            qi_clauses.extend(group.clauses.iter().cloned());
            retained_instantiations.push(group.key.clone());
            retained_term_uids.extend(group.referenced_terms.iter().copied());
            retained_term_uids.extend(group.created_terms.iter().copied());
        }
        retired_candidate_term_uids.retain(|uid| !retained_term_uids.contains(uid));
        qi_clauses.extend(
            required_orphans
                .into_iter()
                .map(|id| self.orphan_qi_clauses[&id].clone()),
        );

        QiGcPlan {
            qi_clauses,
            derived_clauses: self.live_derived.values().cloned().collect(),
            observed_qi_clauses: self.qi_clause_groups.len() + self.orphan_qi_clauses.len(),
            antecedent_edges: self.antecedents.values().map(Vec::len).sum(),
            retained_instantiations,
            retained_term_uids,
            retired_candidate_term_uids,
        }
    }

    pub(crate) fn promote_instantiations(
        &mut self,
        keys: &[QiInstantiationKey],
        retained_term_uids: &DeterministicHashSet<u64>,
    ) {
        self.permanent_instantiations.extend(keys.iter().cloned());
        self.permanent_term_uids
            .extend(retained_term_uids.iter().copied());
    }

    pub(crate) fn permanent_instantiations(&self) -> impl Iterator<Item = &QiInstantiationKey> {
        self.permanent_instantiations.iter()
    }

    pub(crate) fn clear_epoch(&mut self) {
        self.instance_groups.clear();
        self.pending_clause_groups.clear();
        self.qi_clause_groups.clear();
        self.orphan_qi_clauses.clear();
        self.antecedents.clear();
        self.live_derived.clear();
    }

    pub(crate) fn profile(&self) -> QiGcTrackerProfile {
        QiGcTrackerProfile {
            qi_clauses: self.qi_clause_groups.len() + self.orphan_qi_clauses.len(),
            antecedent_nodes: self.antecedents.len(),
            antecedent_edges: self.antecedents.values().map(Vec::len).sum(),
            live_derived: self.live_derived.len(),
            instance_groups: self.instance_groups.len(),
            permanent_instantiations: self.permanent_instantiations.len(),
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
        assert_eq!(plan.qi_clauses, vec![vec![-5, 6]]);
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
        assert_eq!(plan.qi_clauses, vec![vec![3]]);
        assert_eq!(plan.derived_clauses, vec![vec![5]]);
    }

    #[test]
    fn retained_instance_pins_terms_created_by_discarded_instance() {
        let mut tracker = QiGcTracker::default();
        let key = |quantifier_id| QiInstantiationKey {
            quantifier_id,
            substitution: DeterministicHashMap::default(),
        };
        let first_created = DeterministicHashSet::from_iter([10, 11]);
        let first_referenced = first_created.clone();
        tracker.register_instance(key(1), &[vec![1]], 100, &first_created, &first_referenced);

        let second_created = DeterministicHashSet::from_iter([20]);
        let second_referenced = DeterministicHashSet::from_iter([10, 20]);
        tracker.register_instance(key(2), &[vec![2]], 100, &second_created, &second_referenced);

        tracker.note_gated_qi_clause(1, &[1, -100], 100);
        tracker.note_gated_qi_clause(2, &[2, -100], 100);
        tracker.note_derived_clause(3, &[3, -100], &[2], 100);

        let plan = tracker.plan();
        assert_eq!(plan.retained_term_uids, second_referenced);
        assert_eq!(
            plan.retired_candidate_term_uids,
            DeterministicHashSet::from_iter([11])
        );
    }
}
