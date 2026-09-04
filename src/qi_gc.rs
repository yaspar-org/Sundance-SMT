// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Clause-dependency tracking for quantifier-instantiation garbage collection.
//!
//! QI source clauses are paired with CaDiCaL clause IDs at registration.
//! Derived dependency is then propagated through proof antecedent IDs. This
//! permits source-clause collection without adding synthetic selector literals
//! to the SAT problem.

use crate::utils::{DeterministicHashMap, DeterministicHashSet};
use std::collections::{BTreeMap, HashSet};
use std::time::Instant;
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
    pub(crate) created_terms: DeterministicHashSet<u64>,
    pub(crate) clause_terms: DeterministicHashSet<u64>,
}

#[derive(Debug, Clone)]
pub(crate) struct QiCollectibleInstanceGroup {
    pub(crate) group_id: u64,
    pub(crate) clauses: Vec<(u64, Vec<i32>)>,
}

#[derive(Debug, Default)]
pub(crate) struct QiGcSolverRebuildPlan {
    /// QI source clauses that remain unsatisfied after hardening the current
    /// level-zero assignment. These are re-added through the external-clause
    /// interface so they remain forgettable and receive fresh clause IDs.
    pub(crate) source_clauses: Vec<Vec<i32>>,
    /// QI-dependent learned clauses that are valid activation-free
    /// consequences. A fresh solver has no redundant-clause database, so
    /// these are replayed explicitly.
    pub(crate) learned_clauses: Vec<Vec<i32>>,
    pub(crate) source_clauses_before: usize,
    pub(crate) root_satisfied_source_clauses: usize,
    pub(crate) root_satisfied_instance_groups: usize,
    /// Root-satisfied instances no longer need SAT clauses, but their exact
    /// substitutions remain compact e-matching frontier obligations.
    pub(crate) root_satisfied_instances: Vec<QiInstantiationKey>,
    /// Instances whose surviving SAT clauses referenced variables reclaimed by
    /// the term collector. Their substitution keys remain model-check
    /// obligations, but their stale clauses and term closures are not replayed.
    pub(crate) retired_instances: Vec<QiRetainedInstance>,
    pub(crate) retired_instance_source_clauses: usize,
    pub(crate) permanent_clause_owners_awaiting_rekey: usize,
}

#[derive(Debug, Clone)]
struct ClauseTermOwnership {
    clause: Vec<i32>,
    term_uids: DeterministicHashSet<u64>,
    forgettable_theory: bool,
}

#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct QiGcPermanentOwnershipRebuildProfile {
    pub(crate) live_owners_before: usize,
    pub(crate) rekeyed_owners: usize,
    pub(crate) rekeyed_clause_shapes: usize,
    pub(crate) dropped_owners: usize,
    pub(crate) rekeyed_term_uids: usize,
    pub(crate) pending_owners_after: usize,
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
    /// Live guarded QI clauses occurring in the ancestry of a live learned
    /// clause. Other live source clauses can be collected while preserving
    /// the learned consequence.
    pub(crate) retained_qi_clause_ids: DeterministicHashSet<u64>,
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
    /// Substitutions that were collected, found necessary by complete-model
    /// checking, and restored. Recollecting them would repeat the same
    /// collect/restore cycle without reclaiming durable state.
    gc_protected_instance_keys: HashSet<QiInstantiationKey>,
    /// Exact normalized external form of every guarded QI clause.  CaDiCaL
    /// can replace a simplified external clause with a fresh clause ID, so
    /// GC diagnostics retain both identity- and content-based accounting.
    qi_clause_contents: DeterministicHashMap<u64, Vec<i32>>,
    /// Fallback for a guarded QI clause whose registration callback could not
    /// be paired with an instance group.
    orphan_qi_clauses: DeterministicHashMap<u64, Vec<i32>>,
    /// Tainted derived clause ID -> antecedent IDs. Deleted clauses remain here
    /// because they may be intermediate nodes in a live clause's derivation.
    antecedents: DeterministicHashMap<u64, Vec<u64>>,
    /// Tainted derived clauses CaDiCaL has not deleted.
    live_derived: DeterministicHashMap<u64, Vec<i32>>,
    /// Clauses already deleted by CaDiCaL. QI clause ownership remains in
    /// `qi_clause_groups` so live derived ancestry can still reach its source.
    deleted_clause_ids: DeterministicHashSet<u64>,
    /// Terms whose lifetime is owned by the current guarded epoch.
    epoch_owned_term_uids: DeterministicHashSet<u64>,
    /// Terms that must remain alive independently of a deletable SAT clause.
    permanent_term_uids: DeterministicHashSet<u64>,
    /// Theory-clause term ownership is reference-counted by exact CaDiCaL
    /// clause ID. Non-unit theory lemmas are marked forgettable and can be
    /// targeted when they pin terms owned by a collectible QI epoch.
    pending_permanent_clause_terms: DeterministicHashMap<Vec<i32>, Vec<ClauseTermOwnership>>,
    live_permanent_clause_terms: DeterministicHashMap<u64, ClauseTermOwnership>,
    permanent_clause_term_refcounts: DeterministicHashMap<u64, usize>,
}

#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct QiGcTrackerProfile {
    pub(crate) qi_clauses: usize,
    pub(crate) antecedent_nodes: usize,
    pub(crate) antecedent_edges: usize,
    pub(crate) live_derived: usize,
    pub(crate) instance_groups: usize,
    pub(crate) gc_protected_instances: usize,
    pub(crate) permanent_term_uids: usize,
    pub(crate) pending_permanent_clauses: usize,
    pub(crate) live_permanent_clauses: usize,
    pub(crate) live_forgettable_theory_clauses: usize,
    pub(crate) clause_pinned_term_uids: usize,
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

    fn simplify_clause_at_root(clause: &[i32], assignments: &[i32]) -> Option<Vec<i32>> {
        let mut simplified = Vec::with_capacity(clause.len());
        for &lit in clause {
            let assignment = assignments
                .get(lit.unsigned_abs() as usize)
                .copied()
                .unwrap_or(0);
            if assignment.abs() != 1 {
                simplified.push(lit);
                continue;
            }
            if assignment.signum() == lit.signum() {
                return None;
            }
        }
        Some(simplified)
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
                created_terms: created_terms.clone(),
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
            if activation != 0 {
                guarded.push(-activation);
            }
            self.pending_clause_groups
                .entry(Self::normalize_clause(&guarded))
                .or_default()
                .push(group_id);
        }
        self.instance_groups.insert(group_id, instance);
    }

    pub(crate) fn protect_instance_from_collection(&mut self, key: &QiInstantiationKey) -> bool {
        self.gc_protected_instance_keys.insert(key.clone())
    }

    pub(crate) fn note_gated_qi_clause(
        &mut self,
        id: u64,
        clause: &[i32],
        activation: i32,
    ) -> bool {
        if activation != 0 && !clause.contains(&-activation) {
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
        } else if activation == 0 {
            // Without a selector literal, only an explicitly registered
            // source clause is a QI clause. Other theory/original clauses may
            // have identical shapes and must not be classified by syntax.
            return false;
        } else {
            self.orphan_qi_clauses
                .insert(id, Self::strip_activation(clause, activation));
        }
        self.qi_clause_contents.insert(id, key);
        true
    }

    pub(crate) fn note_derived_clause(
        &mut self,
        id: u64,
        clause: &[i32],
        antecedents: &[u64],
        activation: i32,
    ) -> bool {
        let depends_on_qi = if activation == 0 {
            antecedents.iter().any(|antecedent| {
                self.qi_clause_contents.contains_key(antecedent)
                    || self.antecedents.contains_key(antecedent)
            })
        } else {
            clause.contains(&-activation)
        };
        if !depends_on_qi {
            return false;
        }
        self.antecedents.insert(id, antecedents.to_vec());
        self.live_derived.insert(
            id,
            if activation == 0 {
                clause.to_vec()
            } else {
                Self::strip_activation(clause, activation)
            },
        );
        true
    }

    /// Returns true when deleting this clause releases an epoch-term owner and
    /// a root-level term collection should be reconsidered.
    pub(crate) fn note_deleted_clause(&mut self, id: u64) -> bool {
        self.deleted_clause_ids.insert(id);
        self.live_derived.remove(&id);
        let mut released_epoch_term_owner = false;
        if let Some(ownership) = self.live_permanent_clause_terms.remove(&id) {
            released_epoch_term_owner = ownership.forgettable_theory
                && ownership
                    .term_uids
                    .iter()
                    .any(|uid| self.epoch_owned_term_uids.contains(uid));
            for uid in ownership.term_uids {
                let remove = {
                    let count = self
                        .permanent_clause_term_refcounts
                        .get_mut(&uid)
                        .expect("live permanent clause term must have a reference count");
                    *count -= 1;
                    *count == 0
                };
                if remove {
                    self.permanent_clause_term_refcounts.remove(&uid);
                }
            }
        }
        released_epoch_term_owner
    }

    pub(crate) fn live_qi_clauses(&self) -> Vec<(u64, Vec<i32>)> {
        self.qi_clause_contents
            .iter()
            .filter(|(id, _)| !self.deleted_clause_ids.contains(id))
            .map(|(id, clause)| (*id, clause.clone()))
            .collect()
    }

    pub(crate) fn collectible_qi_clauses(&self) -> Vec<(u64, Vec<i32>)> {
        let plan = self.plan();
        let mut clauses: Vec<_> = self
            .qi_clause_contents
            .iter()
            .filter(|(id, clause)| {
                !self.deleted_clause_ids.contains(id)
                    && !plan.retained_qi_clause_ids.contains(id)
                    // Guarded units are not stored in CaDiCaL's clause arena.
                    && clause.len() >= 2
            })
            .map(|(id, clause)| (*id, clause.clone()))
            .collect();
        clauses.sort_unstable_by_key(|(id, _)| *id);
        clauses
    }

    /// Return complete instantiation groups that CaDiCaL can physically
    /// remove. Retired groups remain in Sundance's duplicate filter and are
    /// checked against every complete SAT model; a violated group is restored
    /// lazily instead of being regenerated by every matching round.
    pub(crate) fn collectible_instance_groups(&self) -> Vec<QiCollectibleInstanceGroup> {
        let started = Instant::now();
        let pending_groups: DeterministicHashSet<u64> = self
            .pending_clause_groups
            .values()
            .flatten()
            .copied()
            .collect();
        let mut registered_ids_by_group: DeterministicHashMap<u64, Vec<u64>> =
            DeterministicHashMap::default();
        for (&id, &group_id) in &self.qi_clause_groups {
            registered_ids_by_group
                .entry(group_id)
                .or_default()
                .push(id);
        }
        for ids in registered_ids_by_group.values_mut() {
            ids.sort_unstable();
        }

        let mut group_ids: Vec<u64> = self.instance_groups.keys().copied().collect();
        group_ids.sort_unstable();
        let mut result = Vec::new();
        for group_id in group_ids {
            if pending_groups.contains(&group_id) {
                continue;
            }
            let instance = &self.instance_groups[&group_id];
            if self.gc_protected_instance_keys.contains(&instance.key) {
                continue;
            }
            let Some(registered_ids) = registered_ids_by_group.get(&group_id) else {
                continue;
            };

            // If CaDiCaL did not provide one source-clause identity for every
            // clause in the instance, do not partially retire the group.
            if registered_ids.len() != instance.clauses.len() {
                continue;
            }

            let mut clauses = Vec::new();
            for id in registered_ids {
                if self.deleted_clause_ids.contains(id) {
                    continue;
                }
                let clause = &self.qi_clause_contents[id];
                // Units are represented by assignments rather than entries in
                // CaDiCaL's clause arena and cannot be targeted by clause ID.
                if clause.len() < 2 {
                    continue;
                }
                clauses.push((*id, clause.clone()));
            }
            if !clauses.is_empty() {
                result.push(QiCollectibleInstanceGroup { group_id, clauses });
            }
        }
        if std::env::var_os("SUNDANCE_QI_GC_PROFILE").is_some() {
            eprintln!(
                "[qi-gc-profile] collectible-instance-scan duration={:.6}s \
                 tracked_groups={} registered_source_clauses={} pending_groups={} \
                 collectible_groups={} collectible_clauses={}",
                started.elapsed().as_secs_f64(),
                self.instance_groups.len(),
                self.qi_clause_groups.len(),
                pending_groups.len(),
                result.len(),
                result
                    .iter()
                    .map(|group| group.clauses.len())
                    .sum::<usize>(),
            );
        }
        result
    }

    /// Drop tracker ownership for groups whose complete live source-clause
    /// sets have been physically deleted. The returned instances supply the
    /// substitution keys that must be removed from `added_instantiations`.
    pub(crate) fn finalize_collected_instance_groups(
        &mut self,
        group_ids: &DeterministicHashSet<u64>,
        activation: i32,
    ) -> Vec<QiRetainedInstance> {
        let mut clause_ids_by_group: DeterministicHashMap<u64, Vec<u64>> =
            DeterministicHashMap::default();
        for (&id, &group_id) in &self.qi_clause_groups {
            if group_ids.contains(&group_id) {
                clause_ids_by_group.entry(group_id).or_default().push(id);
            }
        }
        for clause_ids in clause_ids_by_group.values_mut() {
            clause_ids.sort_unstable();
        }

        let mut ordered_groups: Vec<u64> = group_ids.iter().copied().collect();
        ordered_groups.sort_unstable();
        let mut finalized = Vec::new();
        for group_id in ordered_groups {
            let clause_ids = clause_ids_by_group.remove(&group_id).unwrap_or_default();
            let deleted_clause_ids: Vec<u64> = clause_ids
                .iter()
                .copied()
                .filter(|id| self.deleted_clause_ids.contains(id))
                .collect();
            assert!(
                !deleted_clause_ids.is_empty(),
                "QI instance group finalized without a deleted source clause"
            );
            let mut deleted_clauses = Vec::new();
            for id in deleted_clause_ids {
                if let Some(clause) = self.qi_clause_contents.get(&id) {
                    deleted_clauses.push(Self::strip_activation(clause, activation));
                }
                self.qi_clause_groups.remove(&id);
                self.qi_clause_contents.remove(&id);
                self.deleted_clause_ids.remove(&id);
            }

            let mut live_clauses: Vec<Vec<i32>> = clause_ids
                .iter()
                .filter_map(|id| self.qi_clause_contents.get(id))
                .map(|clause| Self::strip_activation(clause, activation))
                .collect();
            live_clauses.sort();
            if let Some(mut instance) = self.instance_groups.remove(&group_id) {
                let retired = QiRetainedInstance {
                    key: instance.key.clone(),
                    clauses: deleted_clauses,
                    created_terms: instance.created_terms.clone(),
                    clause_terms: instance.clause_terms.clone(),
                };
                if !live_clauses.is_empty() {
                    instance.clauses = live_clauses;
                    self.instance_groups.insert(group_id, instance);
                }
                finalized.push(retired);
            }
        }

        // Every surviving QI-dependent learned clause is itself a valid
        // theorem consequence. Keep it as a dependency root for future proof
        // callbacks instead of retaining an ever-growing historical ancestry.
        self.antecedents.clear();
        self.antecedents
            .extend(self.live_derived.keys().map(|id| (*id, Vec::new())));
        self.deleted_clause_ids
            .retain(|id| self.qi_clause_contents.contains_key(id));
        finalized
    }

    pub(crate) fn live_term_uids(&self) -> DeterministicHashSet<u64> {
        let mut result = self.effective_permanent_term_uids();
        let live_groups: DeterministicHashSet<u64> = self
            .qi_clause_groups
            .iter()
            .filter_map(|(id, group)| (!self.deleted_clause_ids.contains(id)).then_some(*group))
            .chain(self.pending_clause_groups.values().flatten().copied())
            .collect();
        for group_id in live_groups {
            if let Some(instance) = self.instance_groups.get(&group_id) {
                result.extend(instance.clause_terms.iter().copied());
            }
        }
        result
    }

    pub(crate) fn live_derived_clauses(&self) -> Vec<Vec<i32>> {
        self.live_derived.values().cloned().collect()
    }

    /// Discard every clause identity owned by the old CaDiCaL instance and
    /// construct the exact external-clause replay for a fresh solver.
    ///
    /// Root-satisfied source clauses are omitted because their satisfying
    /// assignments are hardened as units by the caller. Root-falsified
    /// literals are removed so the callback shape matches CaDiCaL's
    /// root-level simplification. Theory-clause ownership is re-keyed after
    /// the caller has constructed the exact fresh-solver replay.
    pub(crate) fn prepare_for_solver_rebuild(
        &mut self,
        assignments: &[i32],
        retired_sat_vars: &DeterministicHashSet<i32>,
    ) -> QiGcSolverRebuildPlan {
        let source_clauses_before = self
            .instance_groups
            .values()
            .map(|instance| instance.clauses.len())
            .sum();
        let learned_clauses = self.live_derived.values().cloned().collect();

        let permanent_clause_owners_awaiting_rekey = self.live_permanent_clause_terms.len();

        self.pending_clause_groups.clear();
        self.qi_clause_groups.clear();
        self.qi_clause_contents.clear();
        self.orphan_qi_clauses.clear();
        self.antecedents.clear();
        self.live_derived.clear();
        self.deleted_clause_ids.clear();

        let mut source_clauses = Vec::new();
        let mut root_satisfied_source_clauses = 0;
        let mut root_satisfied_instance_groups = 0;
        let mut root_satisfied_instances = Vec::new();
        let mut retired_instances = Vec::new();
        let mut retired_instance_source_clauses = 0;
        let mut empty_groups = Vec::new();
        let mut group_ids: Vec<u64> = self.instance_groups.keys().copied().collect();
        group_ids.sort_unstable();
        for group_id in group_ids {
            let instance = self
                .instance_groups
                .get_mut(&group_id)
                .expect("instance group disappeared during SAT rebuild preparation");
            let mut replayed = Vec::new();
            for clause in std::mem::take(&mut instance.clauses) {
                match Self::simplify_clause_at_root(&clause, assignments) {
                    Some(clause) => replayed.push(clause),
                    None => root_satisfied_source_clauses += 1,
                }
            }
            if replayed.is_empty() {
                root_satisfied_instance_groups += 1;
                if self.gc_protected_instance_keys.contains(&instance.key) {
                    instance.clauses.clear();
                } else {
                    root_satisfied_instances.push(instance.key.clone());
                    empty_groups.push(group_id);
                }
                continue;
            }
            if replayed.iter().any(|clause| {
                clause
                    .iter()
                    .any(|lit| retired_sat_vars.contains(&lit.abs()))
            }) {
                retired_instance_source_clauses += replayed.len();
                retired_instances.push(QiRetainedInstance {
                    key: instance.key.clone(),
                    clauses: Vec::new(),
                    created_terms: instance.created_terms.clone(),
                    clause_terms: DeterministicHashSet::default(),
                });
                empty_groups.push(group_id);
                continue;
            }
            for clause in &replayed {
                self.pending_clause_groups
                    .entry(Self::normalize_clause(clause))
                    .or_default()
                    .push(group_id);
                source_clauses.push(clause.clone());
            }
            instance.clauses = replayed;
        }
        for group_id in empty_groups {
            self.instance_groups.remove(&group_id);
        }

        QiGcSolverRebuildPlan {
            source_clauses,
            learned_clauses,
            source_clauses_before,
            root_satisfied_source_clauses,
            root_satisfied_instance_groups,
            root_satisfied_instances,
            retired_instances,
            retired_instance_source_clauses,
            permanent_clause_owners_awaiting_rekey,
        }
    }

    /// Replace old CaDiCaL clause IDs with pending ownership registrations for
    /// the exact clauses replayed into the fresh solver. Root-satisfied,
    /// retired-variable, and otherwise absent clauses release their term pins.
    pub(crate) fn rekey_permanent_clause_ownership_for_solver_rebuild(
        &mut self,
        replay_clauses: &[Vec<i32>],
        assignments: &[i32],
        retired_sat_vars: &DeterministicHashSet<i32>,
    ) -> QiGcPermanentOwnershipRebuildProfile {
        let replay_shapes: DeterministicHashSet<Vec<i32>> = replay_clauses
            .iter()
            .map(|clause| Self::normalize_clause(clause))
            .collect();
        let live_owners_before = self.live_permanent_clause_terms.len();
        let mut rekeyed_owners = 0usize;
        let mut dropped_owners = 0usize;
        let mut merged = DeterministicHashMap::<Vec<i32>, ClauseTermOwnership>::default();

        for (_, mut ownership) in std::mem::take(&mut self.live_permanent_clause_terms) {
            let Some(simplified) = Self::simplify_clause_at_root(&ownership.clause, assignments)
            else {
                dropped_owners += 1;
                continue;
            };
            let key = Self::normalize_clause(&simplified);
            if key.iter().any(|lit| retired_sat_vars.contains(&lit.abs()))
                || !replay_shapes.contains(&key)
            {
                dropped_owners += 1;
                continue;
            }

            rekeyed_owners += 1;
            ownership.clause = key.clone();
            match merged.get_mut(&key) {
                Some(existing) => {
                    existing.term_uids.extend(ownership.term_uids);
                    existing.forgettable_theory &= ownership.forgettable_theory;
                }
                None => {
                    merged.insert(key, ownership);
                }
            }
        }

        let rekeyed_clause_shapes = merged.len();
        let mut rekeyed_term_uids = DeterministicHashSet::default();
        for (key, ownership) in merged {
            rekeyed_term_uids.extend(ownership.term_uids.iter().copied());
            self.pending_permanent_clause_terms
                .entry(key)
                .or_default()
                .push(ownership);
        }

        self.permanent_clause_term_refcounts.clear();
        for ownerships in self.pending_permanent_clause_terms.values() {
            for ownership in ownerships {
                for uid in &ownership.term_uids {
                    *self
                        .permanent_clause_term_refcounts
                        .entry(*uid)
                        .or_default() += 1;
                }
            }
        }
        let pending_owners_after = self
            .pending_permanent_clause_terms
            .values()
            .map(Vec::len)
            .sum();

        QiGcPermanentOwnershipRebuildProfile {
            live_owners_before,
            rekeyed_owners,
            rekeyed_clause_shapes,
            dropped_owners,
            rekeyed_term_uids: rekeyed_term_uids.len(),
            pending_owners_after,
        }
    }

    pub(crate) fn derived_clause_size_histogram(&self) -> BTreeMap<usize, usize> {
        let mut histogram = BTreeMap::new();
        for clause in self.live_derived.values() {
            *histogram.entry(clause.len()).or_default() += 1;
        }
        histogram
    }

    /// QI instances are theory-valid lemmas, so every SAT clause derived from
    /// them remains valid after the source instance is physically retired.
    /// Preserve the learned clauses as dependency roots while dropping their
    /// historical source ancestry.
    pub(crate) fn promote_live_derived_roots(&mut self) -> usize {
        let promoted = self
            .live_derived
            .keys()
            .filter(|id| {
                self.antecedents
                    .get(id)
                    .is_some_and(|antecedents| !antecedents.is_empty())
            })
            .count();
        self.antecedents.clear();
        self.antecedents
            .extend(self.live_derived.keys().map(|id| (*id, Vec::new())));
        promoted
    }

    pub(crate) fn permanent_term_uids(&self) -> DeterministicHashSet<u64> {
        self.effective_permanent_term_uids()
    }

    pub(crate) fn live_substitution_terms(&self) -> Vec<Term> {
        self.instance_groups
            .values()
            .flat_map(|instance| instance.key.substitution.values().cloned())
            .collect()
    }

    pub(crate) fn gc_protected_term_uids(&self) -> DeterministicHashSet<u64> {
        let mut protected = DeterministicHashSet::default();
        for instance in self
            .instance_groups
            .values()
            .filter(|instance| self.gc_protected_instance_keys.contains(&instance.key))
        {
            protected.extend(instance.created_terms.iter().copied());
            protected.extend(instance.clause_terms.iter().copied());
        }
        protected
    }

    pub(crate) fn observed_qi_clause_count(&self) -> usize {
        self.qi_clause_contents
            .keys()
            .filter(|id| !self.deleted_clause_ids.contains(id))
            .count()
    }

    pub(crate) fn retained_qi_clause_count(&self) -> usize {
        let mut seen = DeterministicHashSet::default();
        let mut worklist: Vec<u64> = self.live_derived.keys().copied().collect();
        let mut retained_qi_clause_ids = DeterministicHashSet::default();

        while let Some(id) = worklist.pop() {
            if !seen.insert(id) {
                continue;
            }
            if (self.qi_clause_groups.contains_key(&id) || self.orphan_qi_clauses.contains_key(&id))
                && !self.deleted_clause_ids.contains(&id)
            {
                retained_qi_clause_ids.insert(id);
            }
            if let Some(parents) = self.antecedents.get(&id) {
                worklist.extend(parents.iter().copied());
            }
        }
        retained_qi_clause_ids.len()
    }

    pub(crate) fn live_derived_clause_count(&self) -> usize {
        self.live_derived.len()
    }

    pub(crate) fn epoch_owned_term_count(&self) -> usize {
        self.epoch_owned_term_uids.len()
    }

    pub(crate) fn unpinned_epoch_owned_term_count(
        &self,
        pinned: &DeterministicHashSet<u64>,
    ) -> usize {
        self.epoch_owned_term_uids.difference(pinned).count()
    }

    pub(crate) fn plan(&self) -> QiGcPlan {
        let mut seen = DeterministicHashSet::default();
        let mut worklist: Vec<u64> = self.live_derived.keys().copied().collect();
        let mut required_groups = DeterministicHashSet::default();
        let mut required_orphans = DeterministicHashSet::default();
        let mut retained_qi_clause_ids = DeterministicHashSet::default();

        while let Some(id) = worklist.pop() {
            if !seen.insert(id) {
                continue;
            }
            if let Some(group) = self.qi_clause_groups.get(&id) {
                required_groups.insert(*group);
                if !self.deleted_clause_ids.contains(&id) {
                    retained_qi_clause_ids.insert(id);
                }
            }
            if self.orphan_qi_clauses.contains_key(&id) {
                required_orphans.insert(id);
                if !self.deleted_clause_ids.contains(&id) {
                    retained_qi_clause_ids.insert(id);
                }
            }
            if let Some(parents) = self.antecedents.get(&id) {
                worklist.extend(parents.iter().copied());
            }
        }

        let mut retained_instances = Vec::new();
        let permanent_term_uids = self.effective_permanent_term_uids();
        let mut retained_term_uids = permanent_term_uids.clone();
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
            observed_qi_clauses: self
                .qi_clause_contents
                .keys()
                .filter(|id| !self.deleted_clause_ids.contains(id))
                .count(),
            retained_qi_clause_ids,
            antecedent_edges: self.antecedents.values().map(Vec::len).sum(),
            retained_term_uids,
            permanent_term_uids,
            epoch_owned_term_uids: self.epoch_owned_term_uids.clone(),
        }
    }

    pub(crate) fn pending_clause_registrations(&self) -> usize {
        self.pending_clause_groups.values().map(Vec::len).sum()
    }

    pub(crate) fn pin_permanent_terms(&mut self, term_uids: impl IntoIterator<Item = u64>) {
        self.permanent_term_uids.extend(term_uids);
    }

    pub(crate) fn register_pending_permanent_clause(
        &mut self,
        clause: &[i32],
        term_uids: DeterministicHashSet<u64>,
    ) {
        self.register_pending_clause_ownership(clause, term_uids, false);
    }

    pub(crate) fn register_pending_forgettable_theory_clause(
        &mut self,
        clause: &[i32],
        term_uids: DeterministicHashSet<u64>,
    ) {
        self.register_pending_clause_ownership(clause, term_uids, true);
    }

    fn register_pending_clause_ownership(
        &mut self,
        clause: &[i32],
        term_uids: DeterministicHashSet<u64>,
        forgettable_theory: bool,
    ) {
        if term_uids.is_empty() {
            return;
        }
        for uid in &term_uids {
            *self
                .permanent_clause_term_refcounts
                .entry(*uid)
                .or_default() += 1;
        }
        self.pending_permanent_clause_terms
            .entry(Self::normalize_clause(clause))
            .or_default()
            .push(ClauseTermOwnership {
                clause: Self::normalize_clause(clause),
                term_uids,
                forgettable_theory,
            });
    }

    pub(crate) fn note_permanent_clause_added(&mut self, id: u64, clause: &[i32]) -> bool {
        let key = Self::normalize_clause(clause);
        let ownership = self
            .pending_permanent_clause_terms
            .get_mut(&key)
            .and_then(Vec::pop);
        if self
            .pending_permanent_clause_terms
            .get(&key)
            .is_some_and(Vec::is_empty)
        {
            self.pending_permanent_clause_terms.remove(&key);
        }
        let Some(ownership) = ownership else {
            return false;
        };
        let old = self.live_permanent_clause_terms.insert(id, ownership);
        debug_assert!(old.is_none(), "CaDiCaL clause IDs must be unique");
        true
    }

    pub(crate) fn collectible_forgettable_theory_clause_ids(&self) -> Vec<u64> {
        let mut ids: Vec<u64> = self
            .live_permanent_clause_terms
            .iter()
            .filter_map(|(id, ownership)| {
                (ownership.forgettable_theory
                    && ownership
                        .term_uids
                        .iter()
                        .any(|uid| self.epoch_owned_term_uids.contains(uid)))
                .then_some(*id)
            })
            .collect();
        ids.sort_unstable();
        ids
    }

    fn is_permanent_term(&self, uid: u64) -> bool {
        self.permanent_term_uids.contains(&uid)
            || self.permanent_clause_term_refcounts.contains_key(&uid)
    }

    fn effective_permanent_term_uids(&self) -> DeterministicHashSet<u64> {
        let mut result = self.permanent_term_uids.clone();
        result.extend(self.permanent_clause_term_refcounts.keys().copied());
        result
    }

    pub(crate) fn count_epoch_owned_terms(&self, term_uids: &DeterministicHashSet<u64>) -> usize {
        term_uids
            .iter()
            .filter(|uid| self.epoch_owned_term_uids.contains(uid))
            .count()
    }

    pub(crate) fn is_epoch_owned_term(&self, uid: u64) -> bool {
        self.epoch_owned_term_uids.contains(&uid)
    }

    pub(crate) fn count_collectible_epoch_terms(
        &self,
        term_uids: &DeterministicHashSet<u64>,
    ) -> usize {
        term_uids
            .iter()
            .filter(|uid| {
                self.epoch_owned_term_uids.contains(uid) && !self.is_permanent_term(**uid)
            })
            .count()
    }

    pub(crate) fn set_epoch_owned_terms(&mut self, term_uids: impl IntoIterator<Item = u64>) {
        self.epoch_owned_term_uids.clear();
        self.epoch_owned_term_uids.extend(term_uids);
    }

    pub(crate) fn clear_epoch(&mut self) {
        self.instance_groups.clear();
        self.pending_clause_groups.clear();
        self.qi_clause_groups.clear();
        self.qi_clause_contents.clear();
        self.orphan_qi_clauses.clear();
        self.antecedents.clear();
        self.live_derived.clear();
        self.deleted_clause_ids.clear();
        self.epoch_owned_term_uids.clear();
        self.gc_protected_instance_keys.clear();
    }

    pub(crate) fn profile(&self) -> QiGcTrackerProfile {
        QiGcTrackerProfile {
            qi_clauses: self.qi_clause_groups.len() + self.orphan_qi_clauses.len(),
            antecedent_nodes: self.antecedents.len(),
            antecedent_edges: self.antecedents.values().map(Vec::len).sum(),
            live_derived: self.live_derived.len(),
            instance_groups: self.instance_groups.len(),
            gc_protected_instances: self.gc_protected_instance_keys.len(),
            permanent_term_uids: self.effective_permanent_term_uids().len(),
            pending_permanent_clauses: self
                .pending_permanent_clause_terms
                .values()
                .map(Vec::len)
                .sum(),
            live_permanent_clauses: self.live_permanent_clause_terms.len(),
            live_forgettable_theory_clauses: self
                .live_permanent_clause_terms
                .values()
                .filter(|ownership| ownership.forgettable_theory)
                .count(),
            clause_pinned_term_uids: self.permanent_clause_term_refcounts.len(),
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
    fn unguarded_mode_propagates_dependency_through_antecedent_ids() {
        let mut tracker = QiGcTracker::default();
        tracker.register_instance(
            QiInstantiationKey {
                quantifier_id: 1,
                substitution: DeterministicHashMap::default(),
            },
            &[vec![3, 4]],
            0,
            &DeterministicHashSet::default(),
            &DeterministicHashSet::default(),
        );

        assert!(tracker.note_gated_qi_clause(1, &[4, 3], 0));
        assert!(tracker.note_derived_clause(2, &[5, 6], &[1, 20], 0));
        assert!(tracker.note_derived_clause(3, &[6], &[2], 0));
        assert!(!tracker.note_derived_clause(4, &[7], &[20], 0));

        let plan = tracker.plan();
        assert_eq!(
            plan.retained_qi_clause_ids,
            DeterministicHashSet::from_iter([1])
        );
        assert_eq!(plan.derived_clauses.len(), 2);
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
    fn promoting_live_derived_clauses_releases_source_ancestry() {
        let mut tracker = QiGcTracker::default();
        assert!(tracker.note_gated_qi_clause(10, &[1, 2, -100], 100));
        assert!(tracker.note_derived_clause(20, &[2, 3, -100], &[10], 100));
        assert_eq!(
            tracker.plan().retained_qi_clause_ids,
            DeterministicHashSet::from_iter([10])
        );

        assert_eq!(tracker.promote_live_derived_roots(), 1);
        assert!(tracker.plan().retained_qi_clause_ids.is_empty());
        assert_eq!(tracker.live_derived_clauses(), vec![vec![2, 3]]);
    }

    #[test]
    fn collectible_qi_clauses_exclude_live_learned_support() {
        let mut tracker = QiGcTracker::default();
        assert!(tracker.note_gated_qi_clause(1, &[3, -100], 100));
        assert!(tracker.note_gated_qi_clause(2, &[4, -100], 100));
        assert!(tracker.note_gated_qi_clause(3, &[5, -100], 100));
        assert!(tracker.note_derived_clause(10, &[6, -100], &[1], 100));
        tracker.note_deleted_clause(3);

        let plan = tracker.plan();
        assert_eq!(plan.observed_qi_clauses, 2);
        assert_eq!(
            plan.retained_qi_clause_ids,
            DeterministicHashSet::from_iter([1])
        );
        assert_eq!(tracker.collectible_qi_clauses(), vec![(2, vec![-100, 4])]);
    }

    #[test]
    fn collectible_instance_groups_are_atomic_even_with_learned_support() {
        let mut tracker = QiGcTracker::default();
        let key = |quantifier_id| QiInstantiationKey {
            quantifier_id,
            substitution: DeterministicHashMap::default(),
        };
        tracker.register_instance(
            key(1),
            &[vec![1, 2], vec![3, 4]],
            0,
            &DeterministicHashSet::default(),
            &DeterministicHashSet::default(),
        );
        tracker.register_instance(
            key(2),
            &[vec![5, 6]],
            0,
            &DeterministicHashSet::default(),
            &DeterministicHashSet::default(),
        );
        tracker.register_instance(
            key(3),
            &[vec![7]],
            0,
            &DeterministicHashSet::default(),
            &DeterministicHashSet::default(),
        );
        assert!(tracker.note_gated_qi_clause(10, &[1, 2], 0));
        assert!(tracker.note_gated_qi_clause(11, &[3, 4], 0));
        assert!(tracker.note_gated_qi_clause(12, &[5, 6], 0));
        assert!(tracker.note_gated_qi_clause(13, &[7], 0));
        assert!(tracker.note_derived_clause(20, &[8, 9], &[10], 0));

        let groups = tracker.collectible_instance_groups();
        assert_eq!(
            groups
                .iter()
                .map(|group| (
                    group.group_id,
                    group.clauses.iter().map(|(id, _)| *id).collect::<Vec<_>>()
                ))
                .collect::<Vec<_>>(),
            vec![(0, vec![10, 11]), (1, vec![12])]
        );
    }

    #[test]
    fn restored_instance_is_not_collected_again() {
        let mut tracker = QiGcTracker::default();
        let key = |quantifier_id| QiInstantiationKey {
            quantifier_id,
            substitution: DeterministicHashMap::default(),
        };
        let restored_key = key(1);
        tracker.register_instance(
            restored_key.clone(),
            &[vec![1, 2]],
            0,
            &DeterministicHashSet::default(),
            &DeterministicHashSet::default(),
        );
        tracker.register_instance(
            key(2),
            &[vec![3, 4]],
            0,
            &DeterministicHashSet::default(),
            &DeterministicHashSet::default(),
        );
        assert!(tracker.note_gated_qi_clause(10, &[1, 2], 0));
        assert!(tracker.note_gated_qi_clause(11, &[3, 4], 0));
        assert!(tracker.protect_instance_from_collection(&restored_key));

        let groups = tracker.collectible_instance_groups();
        assert_eq!(groups.len(), 1);
        assert_eq!(groups[0].group_id, 1);
        assert_eq!(tracker.profile().gc_protected_instances, 1);
    }

    #[test]
    fn finalized_instance_group_releases_its_key_and_compacts_ancestry() {
        let mut tracker = QiGcTracker::default();
        let key = QiInstantiationKey {
            quantifier_id: 7,
            substitution: DeterministicHashMap::default(),
        };
        tracker.register_instance(
            key.clone(),
            &[vec![1, 2], vec![3, 4]],
            0,
            &DeterministicHashSet::default(),
            &DeterministicHashSet::default(),
        );
        assert!(tracker.note_gated_qi_clause(10, &[1, 2], 0));
        assert!(tracker.note_gated_qi_clause(11, &[3, 4], 0));
        assert!(tracker.note_derived_clause(20, &[5, 6], &[10], 0));
        tracker.note_deleted_clause(20);
        tracker.note_deleted_clause(10);
        tracker.note_deleted_clause(11);

        let finalized =
            tracker.finalize_collected_instance_groups(&DeterministicHashSet::from_iter([0]), 0);
        assert_eq!(finalized.len(), 1);
        assert_eq!(finalized[0].key, key);
        assert_eq!(tracker.profile().instance_groups, 0);
        assert_eq!(tracker.profile().qi_clauses, 0);
        assert_eq!(tracker.profile().antecedent_edges, 0);
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
            created_terms: DeterministicHashSet::from_iter([10, 11]),
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

    #[test]
    fn deletable_permanent_clause_releases_its_term_pins() {
        let mut tracker = QiGcTracker::default();
        tracker.set_epoch_owned_terms([10, 11, 12]);
        tracker
            .register_pending_permanent_clause(&[3, -4], DeterministicHashSet::from_iter([10, 11]));

        let pending = tracker.plan();
        assert_eq!(
            pending.permanent_term_uids,
            DeterministicHashSet::from_iter([10, 11])
        );
        assert_eq!(tracker.profile().pending_permanent_clauses, 1);

        assert!(tracker.note_permanent_clause_added(50, &[-4, 3]));
        assert_eq!(tracker.profile().pending_permanent_clauses, 0);
        assert_eq!(tracker.profile().live_permanent_clauses, 1);
        assert_eq!(tracker.profile().clause_pinned_term_uids, 2);

        assert!(!tracker.note_deleted_clause(50));
        assert!(tracker.plan().permanent_term_uids.is_empty());
        assert_eq!(tracker.profile().live_permanent_clauses, 0);
        assert_eq!(tracker.profile().clause_pinned_term_uids, 0);
    }

    #[test]
    fn forgettable_theory_clause_is_collectible_when_it_pins_epoch_terms() {
        let mut tracker = QiGcTracker::default();
        tracker.set_epoch_owned_terms([10, 11, 12]);
        tracker.register_pending_forgettable_theory_clause(
            &[3, -4],
            DeterministicHashSet::from_iter([10, 20]),
        );

        assert!(tracker.note_permanent_clause_added(50, &[-4, 3]));
        assert_eq!(
            tracker.collectible_forgettable_theory_clause_ids(),
            vec![50]
        );
        assert_eq!(tracker.profile().live_forgettable_theory_clauses, 1);

        assert!(tracker.note_deleted_clause(50));
        assert!(
            tracker
                .collectible_forgettable_theory_clause_ids()
                .is_empty()
        );
        assert_eq!(tracker.profile().live_forgettable_theory_clauses, 0);
    }

    #[test]
    fn forgettable_theory_clause_over_permanent_terms_is_not_targeted() {
        let mut tracker = QiGcTracker::default();
        tracker.set_epoch_owned_terms([10, 11, 12]);
        tracker.register_pending_forgettable_theory_clause(
            &[3, -4],
            DeterministicHashSet::from_iter([20, 21]),
        );

        assert!(tracker.note_permanent_clause_added(50, &[-4, 3]));
        assert!(
            tracker
                .collectible_forgettable_theory_clause_ids()
                .is_empty()
        );
        assert!(!tracker.note_deleted_clause(50));
    }

    #[test]
    fn solver_rebuild_rekeys_live_sources_and_simplifies_them_at_root() {
        let mut tracker = QiGcTracker::default();
        let key = |quantifier_id| QiInstantiationKey {
            quantifier_id,
            substitution: DeterministicHashMap::default(),
        };
        tracker.register_instance(
            key(1),
            &[vec![1, 2], vec![-1, 3]],
            0,
            &DeterministicHashSet::default(),
            &DeterministicHashSet::default(),
        );
        tracker.register_instance(
            key(2),
            &[vec![1, 4]],
            0,
            &DeterministicHashSet::default(),
            &DeterministicHashSet::default(),
        );
        assert!(tracker.note_gated_qi_clause(10, &[1, 2], 0));
        assert!(tracker.note_gated_qi_clause(11, &[-1, 3], 0));
        assert!(tracker.note_gated_qi_clause(12, &[1, 4], 0));
        assert!(tracker.note_derived_clause(20, &[5, 6], &[10], 0));

        // Variable 1 is fixed true at level zero.
        let plan = tracker
            .prepare_for_solver_rebuild(&[0, 1, 0, 0, 0, 0, 0], &DeterministicHashSet::default());
        assert_eq!(plan.source_clauses_before, 3);
        assert_eq!(plan.root_satisfied_source_clauses, 2);
        assert_eq!(plan.root_satisfied_instance_groups, 1);
        assert_eq!(plan.source_clauses, vec![vec![3]]);
        assert_eq!(plan.learned_clauses, vec![vec![5, 6]]);
        assert_eq!(tracker.pending_clause_registrations(), 1);
        assert_eq!(tracker.profile().qi_clauses, 0);
        assert_eq!(tracker.profile().live_derived, 0);

        // Fresh CaDiCaL clause IDs are accepted and associated with the
        // surviving instance instead of colliding with old IDs.
        assert!(tracker.note_gated_qi_clause(1, &[3], 0));
        assert_eq!(tracker.pending_clause_registrations(), 0);
        assert_eq!(tracker.profile().qi_clauses, 1);
        assert_eq!(tracker.profile().instance_groups, 1);
    }

    #[test]
    fn solver_rebuild_rekeys_old_clause_term_ownership_before_ids_restart() {
        let mut tracker = QiGcTracker::default();
        tracker.set_epoch_owned_terms([10, 11]);
        tracker.register_pending_forgettable_theory_clause(
            &[3, 4],
            DeterministicHashSet::from_iter([10, 20]),
        );
        assert!(tracker.note_permanent_clause_added(50, &[4, 3]));

        let plan = tracker.prepare_for_solver_rebuild(&[], &DeterministicHashSet::default());
        assert_eq!(plan.permanent_clause_owners_awaiting_rekey, 1);
        let profile = tracker.rekey_permanent_clause_ownership_for_solver_rebuild(
            &[vec![4, 3]],
            &[],
            &DeterministicHashSet::default(),
        );
        assert_eq!(profile.live_owners_before, 1);
        assert_eq!(profile.rekeyed_owners, 1);
        assert_eq!(profile.rekeyed_clause_shapes, 1);
        assert_eq!(profile.dropped_owners, 0);
        assert_eq!(profile.rekeyed_term_uids, 2);
        assert_eq!(profile.pending_owners_after, 1);
        assert_eq!(
            tracker.permanent_term_uids(),
            DeterministicHashSet::from_iter([10, 20])
        );
        assert_eq!(tracker.profile().live_permanent_clauses, 0);
        assert_eq!(tracker.profile().pending_permanent_clauses, 1);
        assert_eq!(tracker.profile().clause_pinned_term_uids, 2);

        // The replay callback assigns a fresh numeric ID to the same owner.
        assert!(tracker.note_permanent_clause_added(1, &[3, 4]));
        assert_eq!(tracker.profile().pending_permanent_clauses, 0);
        assert_eq!(tracker.profile().live_permanent_clauses, 1);
        assert!(!tracker.note_deleted_clause(50));
        assert!(tracker.note_deleted_clause(1));
        assert!(tracker.permanent_term_uids().is_empty());
    }

    #[test]
    fn solver_rebuild_drops_root_satisfied_clause_term_ownership() {
        let mut tracker = QiGcTracker::default();
        tracker.set_epoch_owned_terms([10, 11]);
        tracker.register_pending_forgettable_theory_clause(
            &[3, 4],
            DeterministicHashSet::from_iter([10, 20]),
        );
        assert!(tracker.note_permanent_clause_added(50, &[4, 3]));

        let plan =
            tracker.prepare_for_solver_rebuild(&[0, 0, 0, 1, 0], &DeterministicHashSet::default());
        assert_eq!(plan.permanent_clause_owners_awaiting_rekey, 1);
        let profile = tracker.rekey_permanent_clause_ownership_for_solver_rebuild(
            &[],
            &[0, 0, 0, 1, 0],
            &DeterministicHashSet::default(),
        );
        assert_eq!(profile.live_owners_before, 1);
        assert_eq!(profile.rekeyed_owners, 0);
        assert_eq!(profile.dropped_owners, 1);
        assert_eq!(profile.pending_owners_after, 0);
        assert_eq!(tracker.profile().live_permanent_clauses, 0);
        assert_eq!(tracker.profile().pending_permanent_clauses, 0);
        assert_eq!(tracker.profile().clause_pinned_term_uids, 0);
        assert_eq!(
            tracker.permanent_term_uids(),
            DeterministicHashSet::default()
        );
    }

    #[test]
    fn protected_root_satisfied_instance_retains_its_term_frontier() {
        let mut tracker = QiGcTracker::default();
        let key = QiInstantiationKey {
            quantifier_id: 7,
            substitution: DeterministicHashMap::default(),
        };
        tracker.register_instance(
            key.clone(),
            &[vec![1, 2]],
            0,
            &DeterministicHashSet::from_iter([10, 11]),
            &DeterministicHashSet::from_iter([10, 12]),
        );
        assert!(tracker.note_gated_qi_clause(50, &[1, 2], 0));
        assert!(tracker.protect_instance_from_collection(&key));

        let plan = tracker.prepare_for_solver_rebuild(&[0, 1, 0], &DeterministicHashSet::default());
        assert_eq!(plan.root_satisfied_instance_groups, 1);
        assert!(plan.root_satisfied_instances.is_empty());
        assert_eq!(tracker.profile().instance_groups, 1);
        assert_eq!(
            tracker.gc_protected_term_uids(),
            DeterministicHashSet::from_iter([10, 11, 12])
        );
    }

    #[test]
    fn solver_rebuild_converts_stale_source_clauses_to_compact_obligations() {
        let mut tracker = QiGcTracker::default();
        let key = QiInstantiationKey {
            quantifier_id: 7,
            substitution: DeterministicHashMap::default(),
        };
        tracker.register_instance(
            key.clone(),
            &[vec![3, 4]],
            0,
            &DeterministicHashSet::from_iter([10]),
            &DeterministicHashSet::from_iter([10]),
        );
        assert!(tracker.note_gated_qi_clause(50, &[3, 4], 0));

        let plan =
            tracker.prepare_for_solver_rebuild(&[0; 5], &DeterministicHashSet::from_iter([3]));
        assert!(plan.source_clauses.is_empty());
        assert_eq!(plan.retired_instance_source_clauses, 1);
        assert_eq!(plan.retired_instances.len(), 1);
        assert_eq!(plan.retired_instances[0].key, key);
        assert!(plan.retired_instances[0].clauses.is_empty());
        assert!(plan.retired_instances[0].clause_terms.is_empty());
        assert_eq!(tracker.profile().instance_groups, 0);
        assert_eq!(tracker.pending_clause_registrations(), 0);
    }
}
