// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use super::datastructures::{CanonicalOp, DisequalTerm, Predecessor};
use super::proofforest::*;
use super::repr::{Children, Op, Pattern, PatternId, TermEntry, TermSlot};
use crate::debug_println;
use crate::egraphs::traits::{
    Conflict, EClassMemberRange, EgraphMergeEvent, EgraphResult, EgraphTrait, Lit,
};
use crate::log::is_important;
use crate::relevancy::relevancy_trace_enabled;
use crate::utils::{
    DeterministicHashMap, DeterministicHashSet, FastDeterministicHashMap, FastDeterministicHashSet,
};
use std::cell::Cell;
use std::default::Default;
use std::fmt;
use yaspar_ir::ast::Local;

/// Key for the signature table: (operator, canonical children).
type SigKey = (CanonicalOp, Children);

/// Trail entry for undoing sig_table modifications on backtrack.
/// Stores the actual key used, so undo doesn't depend on UF state.
/// (level, key, term_id, was_inserted)
type SigTrailEntry = (usize, SigKey, u32, bool);

/// Exact predecessor-map mutation made at one decision level.
///
/// The hash stamps make discarded entries logically stale after backtracking,
/// but retaining every historical copy causes predecessor storage to grow
/// monotonically. The trail lets the solver reclaim only mutations from
/// discarded levels without rescanning every predecessor map.
#[derive(Debug, Clone)]
struct PredecessorTrailEntry {
    term: u32,
    key: u32,
    previous: Option<Predecessor>,
    installed: Predecessor,
}

impl fmt::Display for Egraph {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "=== Egraph Summary ===")?;

        // Basic statistics
        writeln!(f, "Proof forest entries: {}", self.proof_forest.len())?;
        writeln!(f, "Predecessor relationships: {}", self.predecessors.len())?;
        writeln!(f, "Function maps: {}", self.function_maps.len())?;

        // Proof forest structure
        if !self.proof_forest.is_empty() {
            writeln!(f, "\n=== Proof Forest ===")?;
            for (term_id, edge) in self.proof_forest.iter().enumerate() {
                if matches!(self.terms[term_id], TermSlot::Empty) {
                    continue;
                }

                // TODO: think about a clean way to represent the proof forest. One option is to go back to using a hashmap, but
                // vector might be more efficient since the prevalence of roots is so dense
                if let ProofForestEdge::Root {
                    size: 1000,
                    child: 0,
                    disequalities,
                    ..
                } = edge
                    && disequalities.is_empty()
                {
                    continue;
                }

                match edge {
                    ProofForestEdge::Root {
                        size,
                        child,
                        disequalities,
                        children,
                        arithmetic,
                    } => {
                        // we use get_term_safe here for child, because it could be that there actually is no child
                        writeln!(
                            f,
                            "  {} -> root [Root (size: {}, child: {:?}, disequalities: {:?}, children: {:?}, arithmetic: {}])",
                            self.display_term(term_id as u32),
                            size,
                            self.display_term(*child),
                            disequalities,
                            children,
                            arithmetic,
                        )?;
                    }
                    ProofForestEdge::Equality {
                        term: Some((t1, t2)),
                        size,
                        parent,
                        child,
                        disequalities,
                        level,
                        hash,
                        children,
                    } => {
                        writeln!(
                            f,
                            "  {} -> {} [Equality {} = {} (size: {}, parent: {}, child: {}, disequalities: {:?}, level: {}, hash: {}, children: {:?})]",
                            self.display_term(term_id as u32),
                            self.display_term(*parent),
                            self.display_term(*t1),
                            self.display_term(*t2),
                            size,
                            self.display_term(*parent),
                            self.display_term(*child),
                            disequalities,
                            level,
                            hash,
                            children
                        )?;
                    }
                    ProofForestEdge::Equality {
                        term: Option::None,
                        size,
                        parent,
                        child,
                        disequalities,
                        level,
                        hash,
                        children,
                    } => {
                        writeln!(
                            f,
                            "  {} -> {} [Equality None (size: {}, parent: {}, child: {}, disequalities: {:?}, level: {}, hash: {}, children: {:?})]",
                            self.display_term(term_id as u32),
                            self.display_term(*parent),
                            size,
                            self.display_term(*parent),
                            self.display_term(*child),
                            disequalities,
                            level,
                            hash,
                            children
                        )?;
                    }
                    ProofForestEdge::Congruence {
                        pairs,
                        size,
                        parent,
                        child,
                        disequalities,
                        level,
                        hash,
                        children,
                    } => {
                        writeln!(
                            f,
                            "  {} -> {} [Congruence {:?} (size: {}, parent: {}, child: {}, disequalities: {:?}, level: {}, hash: {}, children: {:?})]",
                            self.display_term(term_id as u32),
                            self.display_term(*parent),
                            pairs
                                .iter()
                                .map(|(t1, t2)| (self.display_term(*t1), self.display_term(*t2)))
                                .collect::<Vec<_>>(),
                            size,
                            self.display_term(*parent),
                            self.display_term(*child),
                            disequalities,
                            level,
                            hash,
                            children
                        )?;
                    }
                }
            }
        }

        // Predecessor relationships
        if !self.predecessors.is_empty() {
            writeln!(f, "\n=== Predecessor Relationships ===")?;
            for (term, preds) in self.predecessors.iter().enumerate() {
                writeln!(
                    f,
                    "  {}: {} predecessors",
                    self.display_term(term as u32),
                    preds.len()
                )?;
                for pred in preds.values() {
                    writeln!(
                        f,
                        "    -> {} (level: {}, hash: {})",
                        self.display_term(pred.predecessor),
                        pred.level,
                        pred.hash
                    )?; // TODO: it is bad form to use self.false_term as the fallback here
                }
            }
        }

        // Function maps
        if !self.function_maps.is_empty() {
            writeln!(f, "\n=== Function Applications ===")?;
            for (func_name, applications) in self.function_maps.iter() {
                writeln!(f, "  {}: {} applications", func_name, applications.len())?;
                for (term_id, subterms) in applications {
                    write!(f, "    {} (", self.display_term(*term_id))?;
                    for subterm in subterms {
                        write!(f, " {}, ", self.display_term(*subterm))?;
                    }
                    writeln!(f, ")")?;
                }
            }
        }

        writeln!(f, "=== End Egraph Summary ===")?;
        Ok(())
    }
}

/// The egraph datastructure that keeps track of terms, equalities and parents
pub struct Egraph {
    /// Next ID to assign
    next_id: u32,
    /// Tombstoned IDs available for reuse after QI garbage collection.
    free_ids: Vec<u32>,
    /// Internal term representation per term ID
    terms: Vec<TermSlot>,
    /// Compiled patterns for e-matching (indexed by PatternId)
    compiled_patterns: Vec<Pattern>,
    /// map from vertices (u32) -> ProofForestEdge
    proof_forest: Vec<ProofForestEdge>,
    /// Circular linked lists of e-class members. For each class root `r`,
    /// following `member_next` from `r` visits every member exactly once and
    /// returns to `r`. Merging two classes is a swap of their root links.
    member_next: Vec<u32>,
    /// keeps track of a stack of "edges" to backtrack on
    proof_forest_backtrack_stack: Vec<(usize, ProofForestEdge, u32, ProofForestEdge, u32, u32)>,
    /// this is a map from terms (u32) -> (term in the same egraph, predecessor of term in same egraph)
    predecessors: Vec<FastDeterministicHashMap<u32, Predecessor>>,
    /// Exact predecessor-map mutations, grouped by decision level.
    predecessor_trail: Vec<Vec<PredecessorTrailEntry>>,
    /// number to keep track of the current hash
    predecessor_hash: u32,
    /// mapping from levels -> corresponding hash
    predecessor_level: Vec<u32>,
    /// map from functions (String) -> terms of this function
    function_maps: DeterministicHashMap<String, Vec<(u32, Vec<u32>)>>,
    /// Function applications that have become relevant at least once. Entries
    /// are appended once; `e_matching_relevance_levels` determines whether an
    /// entry is active after backtracking.
    relevant_function_maps: DeterministicHashMap<String, Vec<(u32, Vec<u32>)>>,
    /// Earliest active relevance level for each egraph term.
    e_matching_relevance_levels: Vec<Option<usize>>,
    /// Terms whose active e-matching relevance level was established at each
    /// nonzero decision level.
    e_matching_relevance_trail: Vec<Vec<u32>>,
    /// Prevent duplicate insertion into `relevant_function_maps` when a term
    /// becomes relevant again on a later branch.
    ever_e_matching_relevant: Vec<bool>,
    /// the current decision level of the SAT solver, useful to keep track for backtracking
    decision_level: usize,
    /// keeps track of terms created by quantifier instantiation and their predecessors.
    /// Inner map: parent term id -> decision level at which the (child, parent) pair
    /// was registered. Used by `backtrack_to` to skip re-registering entries that
    /// were added at or below the target level (their predecessors are already
    /// valid at that level and don't need refreshing).
    predecessors_created_by_quantifiers:
        DeterministicHashMap<u32, DeterministicHashMap<u32, usize>>,
    /// if a quantifier instantiates (f t) and t = s, then we want to add (f.uid(), "f", [t.uid()]).
    /// Value is the decision level at which the term was registered; entries added
    /// at or below the backtrack target level are skipped during `backtrack_to`.
    union_to_eclass: DeterministicHashMap<u32, usize>,
    /// Signature table: maps (op, [find(c1),...,find(cn)]) → term_id.
    /// Maintained in parallel with the existing congruence detection for now.
    sig_table: FastDeterministicHashMap<SigKey, u32>,
    /// Trail for backtracking the sig_table.
    sig_trail: Vec<SigTrailEntry>,
    /// Whether to collect arithmetic-relevant merges for an incremental
    /// arithmetic backend.
    incremental_arithmetic: bool,
    /// Pre-merge (surviving_root, demoted_root) pairs from direct or
    /// congruence-derived unions where either root was arithmetic-tagged.
    /// The incremental backend drains this to propagate equalities to Z3.
    arithmetic_merge_queue: Vec<(u32, u32)>,
    /// Pre-merge events from ALL unions (direct or congruence-derived), for
    /// egraph-driven relevancy propagation. Only populated when
    /// `track_all_merges` is true.
    ///
    /// TODO: merge this with `arithmetic_merge_queue` — they carry the same
    /// info; the current separation is just because arithmetic gates on the
    /// arithmetic tag. Unify into one queue with per-consumer draining.
    relevancy_merge_queue: Vec<EgraphMergeEvent<u32>>,
    /// Whether to populate `relevancy_merge_queue`.
    track_all_merges: bool,
    /// Accumulated egraph statistics.
    pub(crate) stats: EgraphStats,
    /// Low-overhead counters used to diagnose e-matching and QI-GC growth.
    e_match_calls: Cell<u64>,
    e_match_candidates_scanned: Cell<u64>,
    e_match_relevant_candidates_scanned: Cell<u64>,
    e_match_results: Cell<u64>,
}

/// Statistics accumulated by the egraph.
#[derive(Debug, Default, Clone)]
pub(crate) struct EgraphStats {
    /// Number of successful equality merges (where roots differed).
    pub(crate) merges: u64,
    /// Number of incremental predecessor cleanup passes after backtracking.
    pub(crate) predecessor_gc_runs: u64,
    /// Historical predecessor entries physically removed by those passes.
    pub(crate) predecessor_gc_removed: u64,
    /// Earlier predecessor entries restored after a branch-local replacement.
    pub(crate) predecessor_gc_restored: u64,
    /// Enodes physically tombstoned by QI garbage collection.
    pub(crate) retired_terms: u64,
    /// Tombstoned enode IDs consumed by later registrations.
    pub(crate) reused_term_ids: u64,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct EgraphGcProfile {
    pub(crate) registered_terms: usize,
    pub(crate) reusable_ids: usize,
    pub(crate) function_entries: usize,
    pub(crate) relevant_function_entries: usize,
    pub(crate) active_relevant_terms: usize,
    pub(crate) predecessor_entries: usize,
    pub(crate) predecessor_trail_entries: usize,
    pub(crate) qi_predecessor_entries: usize,
    pub(crate) union_to_eclass_entries: usize,
    pub(crate) signature_entries: usize,
    pub(crate) signature_trail_entries: usize,
    pub(crate) backtrack_entries: usize,
    pub(crate) merges: u64,
    pub(crate) predecessor_gc_runs: u64,
    pub(crate) predecessor_gc_removed: u64,
    pub(crate) predecessor_gc_restored: u64,
    pub(crate) retired_terms: u64,
    pub(crate) reused_term_ids: u64,
    pub(crate) e_match_calls: u64,
    pub(crate) e_match_candidates_scanned: u64,
    pub(crate) e_match_relevant_candidates_scanned: u64,
    pub(crate) e_match_results: u64,
}

#[derive(Debug, Default)]
pub(crate) struct EgraphRetireReport {
    pub(crate) requested: usize,
    pub(crate) candidate_classes: usize,
    pub(crate) fully_candidate_classes: usize,
    pub(crate) retired_classes: usize,
    pub(crate) pruned_mixed_classes: usize,
    pub(crate) pruned_mixed_class_terms: usize,
    pub(crate) retired_ids: Vec<u32>,
    pub(crate) predecessor_entries_before: usize,
    pub(crate) predecessor_entries_after_compaction: usize,
    pub(crate) predecessor_entries_after_retirement: usize,
    pub(crate) blocked_mixed_class_roots: usize,
    pub(crate) blocked_live_parent_terms: usize,
    pub(crate) blocked_proof_reference_terms: usize,
    pub(crate) blocked_disequality_terms: usize,
    pub(crate) blocked_pattern_terms: usize,
    pub(crate) blocked_trigger_head_terms: usize,
    pub(crate) blocked_pending_event_terms: usize,
    pub(crate) missing: usize,
}

#[derive(Debug, Default)]
pub(crate) struct EgraphPredecessorGcReport {
    pub(crate) examined_mutations: usize,
    pub(crate) removed_entries: usize,
    pub(crate) restored_entries: usize,
}

impl Default for Egraph {
    fn default() -> Self {
        Self::new()
    }
}

impl Egraph {
    pub fn new() -> Self {
        Egraph {
            next_id: 0,
            free_ids: Vec::new(),
            terms: vec![TermSlot::Empty],
            compiled_patterns: Vec::new(),
            proof_forest: vec![ProofForestEdge::Root {
                size: 1000,
                child: 0,
                disequalities: DeterministicHashMap::new(),
                children: DeterministicHashSet::new(),
                arithmetic: false,
            }],
            member_next: vec![0],
            proof_forest_backtrack_stack: Vec::new(),
            predecessors: vec![FastDeterministicHashMap::default()],
            predecessor_trail: vec![Vec::new()],
            predecessor_hash: 1,
            predecessor_level: vec![1, 1],
            function_maps: DeterministicHashMap::default(),
            relevant_function_maps: DeterministicHashMap::default(),
            e_matching_relevance_levels: vec![None],
            e_matching_relevance_trail: vec![Vec::new()],
            ever_e_matching_relevant: vec![false],
            decision_level: 0,
            predecessors_created_by_quantifiers: DeterministicHashMap::new(),
            union_to_eclass: DeterministicHashMap::new(),
            sig_table: FastDeterministicHashMap::default(),
            sig_trail: Vec::new(),
            incremental_arithmetic: false,
            arithmetic_merge_queue: Vec::new(),
            relevancy_merge_queue: Vec::new(),
            track_all_merges: false,
            stats: EgraphStats::default(),
            e_match_calls: Cell::new(0),
            e_match_candidates_scanned: Cell::new(0),
            e_match_relevant_candidates_scanned: Cell::new(0),
            e_match_results: Cell::new(0),
        }
    }

    pub(crate) fn gc_profile(&self) -> EgraphGcProfile {
        EgraphGcProfile {
            registered_terms: self
                .terms
                .iter()
                .filter(|slot| !matches!(slot, TermSlot::Empty))
                .count(),
            reusable_ids: self.free_ids.len(),
            function_entries: self.function_maps.values().map(Vec::len).sum(),
            relevant_function_entries: self.relevant_function_maps.values().map(Vec::len).sum(),
            active_relevant_terms: self
                .e_matching_relevance_levels
                .iter()
                .filter(|level| level.is_some())
                .count(),
            predecessor_entries: self.predecessors.iter().map(|entries| entries.len()).sum(),
            predecessor_trail_entries: self.predecessor_trail.iter().map(Vec::len).sum(),
            qi_predecessor_entries: self
                .predecessors_created_by_quantifiers
                .values()
                .map(|entries| entries.len())
                .sum(),
            union_to_eclass_entries: self.union_to_eclass.len(),
            signature_entries: self.sig_table.len(),
            signature_trail_entries: self.sig_trail.len(),
            backtrack_entries: self.proof_forest_backtrack_stack.len(),
            merges: self.stats.merges,
            predecessor_gc_runs: self.stats.predecessor_gc_runs,
            predecessor_gc_removed: self.stats.predecessor_gc_removed,
            predecessor_gc_restored: self.stats.predecessor_gc_restored,
            retired_terms: self.stats.retired_terms,
            reused_term_ids: self.stats.reused_term_ids,
            e_match_calls: self.e_match_calls.get(),
            e_match_candidates_scanned: self.e_match_candidates_scanned.get(),
            e_match_relevant_candidates_scanned: self.e_match_relevant_candidates_scanned.get(),
            e_match_results: self.e_match_results.get(),
        }
    }

    /// Returns the u32 corresponding to a given lit with the correct polarity
    /// Display a term recursively using the internal representation.
    pub fn display_term(&self, id: u32) -> String {
        if id as usize >= self.terms.len() {
            return format!("?{}", id);
        }
        match &self.terms[id as usize] {
            TermSlot::Empty => format!("?{}", id),
            TermSlot::Opaque => format!("[opaque:{}]", id),
            TermSlot::Term(entry) => {
                if entry.children.is_empty() {
                    entry.op.to_function_map_key()
                } else {
                    let children_str: Vec<String> = entry
                        .children
                        .as_slice()
                        .iter()
                        .map(|c| self.display_term(*c))
                        .collect();
                    format!(
                        "({} {})",
                        entry.op.to_function_map_key(),
                        children_str.join(" ")
                    )
                }
            }
        }
    }

    /// Register a single term in the egraph
    /// Sets up terms_list, proof_forest, predecessors, function_maps for this term.
    /// Register a single term (non-recursive). Children must already be registered.
    /// If `dynamic` is true, calls find_and_union_to_eclass to merge with any
    /// existing congruent term (needed for quantifier instantiation and datatype axioms).
    /// Returns true if the term was already registered.
    fn register_term_internal(&mut self, id: u32, op: Op, children: &[u32], dynamic: bool) -> bool {
        self.ensure_capacity(id);

        // Check if already inserted
        if !matches!(self.terms[id as usize], TermSlot::Empty) {
            return true;
        }

        // Store internal representation
        self.terms[id as usize] = TermSlot::Term(TermEntry {
            op: op.clone(),
            children: Children::from_slice(children),
        });

        self.proof_forest[id as usize] = ProofForestEdge::Root {
            size: 1,
            disequalities: DeterministicHashMap::new(),
            child: 0,
            children: DeterministicHashSet::new(),
            arithmetic: false,
        };
        self.member_next[id as usize] = id;

        // Add to function_maps using the op's string key
        let func_key = op.to_function_map_key();
        if !func_key.is_empty() {
            self.function_maps
                .entry(func_key.clone())
                .or_default()
                .push((id, children.to_vec()));
        }

        // Add this term as a predecessor of each child
        for &child_uid in children {
            let predecessor = Predecessor {
                level: 0,
                hash: 0,
                predecessor: id,
                inner_term: child_uid,
            };
            self.predecessors[child_uid as usize]
                .entry(id)
                .or_insert(predecessor);

            if dynamic {
                let (root, level, hash) = self.find_with_level(child_uid, 0, 0);
                let root_predecessor = Predecessor {
                    level,
                    hash,
                    predecessor: id,
                    inner_term: child_uid,
                };

                self.predecessors_created_by_quantifiers
                    .entry(child_uid)
                    .or_default()
                    .insert(id, self.decision_level);

                self.add_predecessor(root, id, root_predecessor);
            }
        }

        // Insert into sig_table; if dynamic and sig already exists, merge via congruence.
        if let Some(sig) = self.compute_signature(id) {
            if let Some(&existing) = self.sig_table.get(&sig) {
                if dynamic && self.find(existing) != self.find(id) {
                    // TODO: propagate conflict — requires register_term_internal to return EgraphResult
                    self.congruence_merge(existing, id, self.decision_level);
                }
            } else {
                self.sig_table_insert(sig, id, self.decision_level);
            }
        }

        if dynamic && !children.is_empty() {
            self.union_to_eclass.insert(id, self.decision_level);
        }

        false
    }

    fn allocate_id(&mut self) -> u32 {
        if let Some(id) = self.free_ids.pop() {
            debug_assert!(matches!(self.terms[id as usize], TermSlot::Empty));
            self.stats.reused_term_ids += 1;
            id
        } else {
            let id = self.next_id;
            self.next_id += 1;
            id
        }
    }

    fn collect_pattern_ground_ids(pattern: &Pattern, ids: &mut DeterministicHashSet<u32>) {
        match pattern {
            Pattern::Var(_) => {}
            Pattern::Ground(id) => {
                ids.insert(*id);
            }
            Pattern::App(_, children) => {
                for child in children {
                    Self::collect_pattern_ground_ids(child, ids);
                }
            }
        }
    }

    fn class_members(&self, root: u32) -> Vec<u32> {
        debug_assert_eq!(self.find(root), root);
        let mut members = vec![root];
        let mut member = self.member_next[root as usize];
        while member != root {
            members.push(member);
            assert!(
                members.len() <= self.next_id as usize,
                "e-class member list rooted at {root} did not form a cycle"
            );
            member = self.member_next[member as usize];
        }
        members
    }

    /// Equalities between live members of arithmetic classes that survive at
    /// level zero. A rebuilt arithmetic backend can assert these permanently
    /// instead of depending on historical merge callbacks.
    pub(crate) fn arithmetic_root_equalities(&self) -> Vec<(u32, u32)> {
        let mut equalities = Vec::new();
        for root in 0..self.next_id {
            if matches!(self.terms[root as usize], TermSlot::Empty) {
                continue;
            }
            let ProofForestEdge::Root {
                arithmetic: true, ..
            } = &self.proof_forest[root as usize]
            else {
                continue;
            };
            let mut member = self.member_next[root as usize];
            while member != root {
                debug_assert!(!matches!(self.terms[member as usize], TermSlot::Empty));
                equalities.push((root, member));
                member = self.member_next[member as usize];
            }
        }
        equalities
    }

    /// Restore or remove exact predecessor-map mutations from levels that
    /// have already been backtracked.
    pub(crate) fn collect_backtracked_predecessors(&mut self) -> EgraphPredecessorGcReport {
        let mut report = EgraphPredecessorGcReport::default();
        for level in (self.decision_level + 1..self.predecessor_trail.len()).rev() {
            let entries = std::mem::take(&mut self.predecessor_trail[level]);
            for entry in entries.into_iter().rev() {
                report.examined_mutations += 1;
                let predecessors = &mut self.predecessors[entry.term as usize];
                if predecessors.get(&entry.key) != Some(&entry.installed) {
                    // A lower-level dynamic predecessor may have been
                    // re-established after the backtrack. It supersedes the
                    // discarded branch mutation and must remain installed.
                    continue;
                }
                if let Some(previous) = entry.previous {
                    predecessors.insert(entry.key, previous);
                    report.restored_entries += 1;
                } else {
                    predecessors.remove(&entry.key);
                    report.removed_entries += 1;
                }
            }
        }
        self.stats.predecessor_gc_runs += 1;
        self.stats.predecessor_gc_removed += report.removed_entries as u64;
        self.stats.predecessor_gc_restored += report.restored_entries as u64;
        report
    }

    /// Rebuild the predecessor index from live level-zero enodes.
    ///
    /// This remains a full-compaction fallback for root QI collection. Normal
    /// SAT backtracks use `collect_backtracked_predecessors` and touch only
    /// entries mutated on discarded decision levels.
    fn compact_level_zero_predecessors(&mut self) -> (usize, usize) {
        assert_eq!(self.decision_level, 0);
        assert!(
            self.proof_forest_backtrack_stack.is_empty() && self.sig_trail.is_empty(),
            "predecessor compaction requires all transient proof state to be backtracked"
        );

        let before = self.predecessors.iter().map(|entries| entries.len()).sum();
        let live_parents: Vec<(u32, Vec<u32>)> = self
            .terms
            .iter()
            .enumerate()
            .filter_map(|(id, slot)| match slot {
                TermSlot::Term(entry) => Some((id as u32, entry.children.as_slice().to_vec())),
                TermSlot::Empty | TermSlot::Opaque => None,
            })
            .collect();

        for entries in &mut self.predecessors {
            entries.clear();
        }
        for entries in &mut self.predecessor_trail {
            entries.clear();
        }
        for (parent, children) in live_parents {
            for child in children {
                debug_assert!(
                    !matches!(self.terms[child as usize], TermSlot::Empty),
                    "live parent {} refers to retired child {}",
                    parent,
                    child
                );
                let predecessor = Predecessor {
                    level: 0,
                    hash: 0,
                    predecessor: parent,
                    inner_term: child,
                };
                self.predecessors[child as usize].insert(parent, predecessor.clone());
                let root = self.find(child);
                if root != child {
                    self.predecessors[root as usize].insert(parent, predecessor);
                }
            }
        }

        let after = self.predecessors.iter().map(|entries| entries.len()).sum();
        (before, after)
    }

    /// Physically remove dead QI-created enodes at decision level zero.
    ///
    /// Collection can prune dead members from otherwise-live equivalence
    /// classes. A term remains pinned if it is a class root with surviving
    /// members, occurs in a trigger or pending merge event, has a surviving
    /// syntactic parent, or is referenced by a surviving proof/disequality
    /// edge. This fixed-point closure preserves every path that can still be
    /// used for congruence, conflict explanation, or e-matching while allowing
    /// irrelevant leaves in the large Boolean true/false classes to disappear.
    pub(crate) fn retire_terms(
        &mut self,
        candidates: &DeterministicHashSet<u32>,
    ) -> EgraphRetireReport {
        assert_eq!(
            self.decision_level, 0,
            "egraph terms may only be retired at decision level zero"
        );
        assert!(
            self.proof_forest_backtrack_stack.is_empty() && self.sig_trail.is_empty(),
            "egraph retirement requires all transient proof state to be backtracked"
        );

        let mut report = EgraphRetireReport {
            requested: candidates.len(),
            ..EgraphRetireReport::default()
        };
        (
            report.predecessor_entries_before,
            report.predecessor_entries_after_compaction,
        ) = self.compact_level_zero_predecessors();
        let mut removable = DeterministicHashSet::default();
        for &id in candidates {
            if id as usize >= self.terms.len() || matches!(self.terms[id as usize], TermSlot::Empty)
            {
                report.missing += 1;
            } else {
                removable.insert(id);
            }
        }

        let mut class_members_by_root: DeterministicHashMap<u32, Vec<u32>> =
            DeterministicHashMap::default();
        for &id in &removable {
            let root = self.find(id);
            class_members_by_root
                .entry(root)
                .or_insert_with(|| self.class_members(root));
        }
        report.candidate_classes = class_members_by_root.len();
        for members in class_members_by_root.values() {
            if members.iter().all(|member| removable.contains(member)) {
                report.fully_candidate_classes += 1;
            }
        }

        let mut pattern_ids = DeterministicHashSet::default();
        for pattern in &self.compiled_patterns {
            Self::collect_pattern_ground_ids(pattern, &mut pattern_ids);
        }
        for id in pattern_ids {
            if removable.remove(&id) {
                report.blocked_pattern_terms += 1;
            }
        }

        // Every ground application whose head can match a compiled trigger
        // remains part of the future e-matching search space even when no live
        // SAT/theory clause refers to it. Retiring it can make a later
        // quantifier round incorrectly saturate.
        let mut trigger_heads = Vec::new();
        let mut wildcard_trigger = false;
        for pattern in &self.compiled_patterns {
            match pattern {
                Pattern::App(op, _) => {
                    if !trigger_heads.contains(op) {
                        trigger_heads.push(op.clone());
                    }
                }
                Pattern::Var(_) => wildcard_trigger = true,
                Pattern::Ground(_) => {}
            }
        }
        let trigger_head_ids: Vec<u32> = removable
            .iter()
            .copied()
            .filter(|id| {
                wildcard_trigger
                    || matches!(
                        &self.terms[*id as usize],
                        TermSlot::Term(entry) if trigger_heads.contains(&entry.op)
                    )
            })
            .collect();
        for id in trigger_head_ids {
            if removable.remove(&id) {
                report.blocked_trigger_head_terms += 1;
            }
        }

        // Pending class-relevancy events contain pre-merge member ranges.
        // Keep those ranges stable until their consumer drains them.
        let mut pending_event_ids = DeterministicHashSet::default();
        for event in &self.relevancy_merge_queue {
            pending_event_ids.insert(event.survivor);
            pending_event_ids.insert(event.demoted);
            pending_event_ids.extend(self.collect_member_range(event.survivor_members));
            pending_event_ids.extend(self.collect_member_range(event.demoted_members));
        }
        for id in pending_event_ids {
            if removable.remove(&id) {
                report.blocked_pending_event_terms += 1;
            }
        }

        // Compute the transitive live-reference closure. Blocking a term can
        // expose its parent/proof edge as live, which can pin another
        // candidate on the next iteration.
        loop {
            let mut changed = false;

            // A root can only disappear when its complete class disappears.
            let mixed_roots: Vec<u32> = class_members_by_root
                .iter()
                .filter_map(|(root, members)| {
                    (removable.contains(root)
                        && members.iter().any(|member| !removable.contains(member)))
                    .then_some(*root)
                })
                .collect();
            for root in mixed_roots {
                if removable.remove(&root) {
                    report.blocked_mixed_class_roots += 1;
                    changed = true;
                }
            }

            let parent_blocked: Vec<u32> = removable
                .iter()
                .copied()
                .filter(|id| {
                    self.predecessors[*id as usize].keys().any(|parent| {
                        (*parent as usize) < self.terms.len()
                            && !matches!(self.terms[*parent as usize], TermSlot::Empty)
                            && !removable.contains(parent)
                    })
                })
                .collect();
            for id in parent_blocked {
                if removable.remove(&id) {
                    report.blocked_live_parent_terms += 1;
                    changed = true;
                }
            }

            let mut proof_blocked = DeterministicHashSet::default();
            let mut disequality_blocked = DeterministicHashSet::default();
            for (id, edge) in self.proof_forest.iter().enumerate() {
                if matches!(self.terms[id], TermSlot::Empty) || removable.contains(&(id as u32)) {
                    continue;
                }

                match edge {
                    ProofForestEdge::Root { children, .. } => {
                        proof_blocked.extend(
                            children
                                .iter()
                                .copied()
                                .filter(|child| removable.contains(child)),
                        );
                    }
                    ProofForestEdge::Equality {
                        term,
                        parent,
                        children,
                        ..
                    } => {
                        if removable.contains(parent) {
                            proof_blocked.insert(*parent);
                        }
                        if let Some((left, right)) = term {
                            if removable.contains(left) {
                                proof_blocked.insert(*left);
                            }
                            if removable.contains(right) {
                                proof_blocked.insert(*right);
                            }
                        }
                        proof_blocked.extend(
                            children
                                .iter()
                                .copied()
                                .filter(|child| removable.contains(child)),
                        );
                    }
                    ProofForestEdge::Congruence {
                        pairs,
                        parent,
                        children,
                        ..
                    } => {
                        if removable.contains(parent) {
                            proof_blocked.insert(*parent);
                        }
                        for (left, right) in pairs {
                            if removable.contains(left) {
                                proof_blocked.insert(*left);
                            }
                            if removable.contains(right) {
                                proof_blocked.insert(*right);
                            }
                        }
                        proof_blocked.extend(
                            children
                                .iter()
                                .copied()
                                .filter(|child| removable.contains(child)),
                        );
                    }
                }

                for (key, disequality) in edge.disequalities() {
                    if !valid_hash(disequality.hash, disequality.level, &self.predecessor_level) {
                        continue;
                    }
                    for referenced in [
                        *key,
                        disequality.term,
                        disequality.original_disequality.0,
                        disequality.original_disequality.1,
                    ] {
                        if removable.contains(&referenced) {
                            disequality_blocked.insert(referenced);
                        }
                    }
                }
            }

            for id in proof_blocked {
                if removable.remove(&id) {
                    report.blocked_proof_reference_terms += 1;
                    changed = true;
                }
            }
            for id in disequality_blocked {
                if removable.remove(&id) {
                    report.blocked_disequality_terms += 1;
                    changed = true;
                }
            }

            if !changed {
                break;
            }
        }

        for members in class_members_by_root.values() {
            let retired = members
                .iter()
                .filter(|member| removable.contains(member))
                .count();
            if retired == members.len() {
                report.retired_classes += 1;
            } else if retired > 0 {
                report.pruned_mixed_classes += 1;
                report.pruned_mixed_class_terms += retired;
            }
        }

        if removable.is_empty() {
            report.predecessor_entries_after_retirement =
                report.predecessor_entries_after_compaction;
            return report;
        }

        // Splice collected members out of surviving circular class lists.
        for members in class_members_by_root.values() {
            let survivors: Vec<u32> = members
                .iter()
                .copied()
                .filter(|member| !removable.contains(member))
                .collect();
            if survivors.is_empty() {
                continue;
            }
            debug_assert!(
                !removable.contains(&members[0]),
                "surviving class lost its proof root"
            );
            for (index, member) in survivors.iter().enumerate() {
                self.member_next[*member as usize] = survivors[(index + 1) % survivors.len()];
            }
        }

        // Verify the closure before making IDs reusable.
        for (id, edge) in self.proof_forest.iter().enumerate() {
            if matches!(self.terms[id], TermSlot::Empty) || removable.contains(&(id as u32)) {
                continue;
            }
            match edge {
                ProofForestEdge::Root { children, .. } => {
                    debug_assert!(children.iter().all(|child| !removable.contains(child)));
                }
                ProofForestEdge::Equality {
                    term,
                    parent,
                    children,
                    ..
                } => {
                    debug_assert!(!removable.contains(parent));
                    debug_assert!(children.iter().all(|child| !removable.contains(child)));
                    if let Some((left, right)) = term {
                        debug_assert!(!removable.contains(left));
                        debug_assert!(!removable.contains(right));
                    }
                }
                ProofForestEdge::Congruence {
                    pairs,
                    parent,
                    children,
                    ..
                } => {
                    debug_assert!(!removable.contains(parent));
                    debug_assert!(children.iter().all(|child| !removable.contains(child)));
                    debug_assert!(pairs.iter().all(|(left, right)| {
                        !removable.contains(left) && !removable.contains(right)
                    }));
                }
            }
            debug_assert!(edge.disequalities().iter().all(|(key, disequality)| {
                !valid_hash(disequality.hash, disequality.level, &self.predecessor_level)
                    || (!removable.contains(key)
                        && !removable.contains(&disequality.term)
                        && !removable.contains(&disequality.original_disequality.0)
                        && !removable.contains(&disequality.original_disequality.1))
            }));
        }
        for (id, slot) in self.terms.iter().enumerate() {
            if removable.contains(&(id as u32)) {
                continue;
            }
            if let TermSlot::Term(entry) = slot {
                debug_assert!(
                    entry
                        .children
                        .as_slice()
                        .iter()
                        .all(|child| !removable.contains(child)),
                    "live enode retained a collected child"
                );
            }
        }

        // Remove stale disequality references before IDs become reusable.
        for edge in &mut self.proof_forest {
            edge.disequalities_mut().retain(|key, disequality| {
                !removable.contains(key)
                    && !removable.contains(&disequality.term)
                    && !removable.contains(&disequality.original_disequality.0)
                    && !removable.contains(&disequality.original_disequality.1)
            });
        }

        for entries in self.function_maps.values_mut() {
            entries.retain(|(id, _)| !removable.contains(id));
        }
        self.function_maps.retain(|_, entries| !entries.is_empty());
        for entries in self.relevant_function_maps.values_mut() {
            entries.retain(|(id, _)| !removable.contains(id));
        }
        self.relevant_function_maps
            .retain(|_, entries| !entries.is_empty());

        for (id, entries) in self.predecessors.iter_mut().enumerate() {
            if removable.contains(&(id as u32)) {
                entries.clear();
            } else {
                entries.retain(|parent, predecessor| {
                    !removable.contains(parent)
                        && !removable.contains(&predecessor.inner_term)
                        && !removable.contains(&predecessor.predecessor)
                });
            }
        }
        self.predecessors_created_by_quantifiers
            .retain(|child, parents| {
                if removable.contains(child) {
                    return false;
                }
                parents.retain(|parent, _| !removable.contains(parent));
                !parents.is_empty()
            });
        self.union_to_eclass.retain(|id, _| !removable.contains(id));
        self.sig_table.retain(|(_, children), id| {
            !removable.contains(id)
                && !children
                    .as_slice()
                    .iter()
                    .any(|child| removable.contains(child))
        });
        self.arithmetic_merge_queue
            .retain(|(a, b)| !removable.contains(a) && !removable.contains(b));
        self.relevancy_merge_queue.retain(|event| {
            !removable.contains(&event.survivor) && !removable.contains(&event.demoted)
        });
        for trail in &mut self.e_matching_relevance_trail {
            trail.retain(|id| !removable.contains(id));
        }

        let mut retired_ids: Vec<u32> = removable.into_iter().collect();
        retired_ids.sort_unstable();
        for &id in &retired_ids {
            self.terms[id as usize] = TermSlot::Empty;
            self.proof_forest[id as usize] = ProofForestEdge::Root {
                size: 1000,
                child: 0,
                disequalities: DeterministicHashMap::new(),
                children: DeterministicHashSet::new(),
                arithmetic: false,
            };
            self.member_next[id as usize] = id;
            self.e_matching_relevance_levels[id as usize] = None;
            self.ever_e_matching_relevant[id as usize] = false;
            self.free_ids.push(id);
        }
        self.stats.retired_terms += retired_ids.len() as u64;
        report.predecessor_entries_after_retirement =
            self.predecessors.iter().map(|entries| entries.len()).sum();
        report.retired_ids = retired_ids;
        report
    }

    /// Extract the Op from a Term and its function name string.
    /// Ensure storage is allocated for the given term ID without fully registering it.
    /// Used for quantifier body subterms that are opaque to the egraph.
    fn ensure_capacity(&mut self, id: u32) {
        while self.terms.len() <= id as usize {
            self.terms.resize(self.terms.len() * 2, TermSlot::Empty);
            self.proof_forest.resize(
                self.proof_forest.len() * 2,
                ProofForestEdge::Root {
                    size: 1000,
                    child: 0,
                    disequalities: DeterministicHashMap::new(),
                    children: DeterministicHashSet::new(),
                    arithmetic: false,
                },
            );
            self.predecessors.resize(
                self.predecessors.len() * 2,
                FastDeterministicHashMap::default(),
            );
            self.member_next.resize(self.member_next.len() * 2, 0);
            self.e_matching_relevance_levels
                .resize(self.e_matching_relevance_levels.len() * 2, None);
            self.ever_e_matching_relevant
                .resize(self.ever_e_matching_relevant.len() * 2, false);
        }
    }

    fn mark_match_term_relevant(&mut self, term: u32, level: usize) {
        self.ensure_capacity(term);
        let idx = term as usize;
        if self.e_matching_relevance_levels[idx].is_some_and(|old| old <= level) {
            return;
        }

        if !self.ever_e_matching_relevant[idx] {
            if let TermSlot::Term(entry) = &self.terms[idx] {
                let func_key = entry.op.to_function_map_key();
                if !func_key.is_empty() {
                    self.relevant_function_maps
                        .entry(func_key)
                        .or_default()
                        .push((term, entry.children.as_slice().to_vec()));
                }
            }
            self.ever_e_matching_relevant[idx] = true;
        }

        self.e_matching_relevance_levels[idx] = Some(level);
        if level > 0 {
            if self.e_matching_relevance_trail.len() <= level {
                self.e_matching_relevance_trail
                    .resize_with(level + 1, Vec::new);
            }
            self.e_matching_relevance_trail[level].push(term);
        }
    }

    fn backtrack_match_relevance(&mut self, level: usize) {
        if level + 1 < self.e_matching_relevance_trail.len() {
            for mark_level in ((level + 1)..self.e_matching_relevance_trail.len()).rev() {
                let terms = std::mem::take(&mut self.e_matching_relevance_trail[mark_level]);
                for term in terms.into_iter().rev() {
                    let idx = term as usize;
                    if self.e_matching_relevance_levels[idx] == Some(mark_level) {
                        self.e_matching_relevance_levels[idx] = None;
                    }
                }
            }
            self.e_matching_relevance_trail.truncate(level + 1);
        }
    }

    /// Register an opaque term — allocates a full slot with a proof_forest Root
    /// but no op/children/function_maps/predecessors. Used for quantifier terms
    /// that participate in union-find (merged with true/false) but not congruence.
    fn register_opaque_term(&mut self) -> u32 {
        let id = self.allocate_id();
        self.ensure_capacity(id);
        self.terms[id as usize] = TermSlot::Opaque;
        self.proof_forest[id as usize] = ProofForestEdge::Root {
            size: 1,
            disequalities: DeterministicHashMap::new(),
            child: 0,
            children: DeterministicHashSet::new(),
            arithmetic: false,
        };
        self.member_next[id as usize] = id;
        id
    }

    fn is_constant(&self, id: u32) -> bool {
        matches!(
            &self.terms[id as usize],
            TermSlot::Term(TermEntry {
                op: Op::Constant(_),
                ..
            })
        )
    }

    fn find(&self, x: u32) -> u32 {
        let p: &ProofForestEdge = &self.proof_forest[x as usize];
        match p {
            ProofForestEdge::Root { .. } => x,
            ProofForestEdge::Congruence { parent: p, .. }
            | ProofForestEdge::Equality { parent: p, .. } => self.find(*p),
        }
    }

    fn member_range_for_root(&self, root: u32) -> EClassMemberRange<u32> {
        debug_assert_eq!(self.find(root), root);
        EClassMemberRange {
            first: self.member_next[root as usize],
            last: root,
        }
    }

    fn collect_member_range(&self, range: EClassMemberRange<u32>) -> Vec<u32> {
        let mut members = Vec::new();
        let mut current = range.first;
        loop {
            members.push(current);
            if current == range.last {
                break;
            }
            assert!(
                members.len() <= self.next_id as usize,
                "e-class member range did not reach its final member"
            );
            current = self.member_next[current as usize];
        }
        members
    }

    // FIND operation for union-find
    // lazy find, keep finding the representative until you get to something that is a representative of itself
    // design decision: I do not implement path compression. I could, but would make recovering proof much harder
    fn find_with_level(
        &self,
        x: u32,
        highest_level: usize,
        highest_hash: u32,
    ) -> (u32, usize, u32) {
        match &self.proof_forest[x as usize] {
            ProofForestEdge::Root { .. } => (x, highest_level, highest_hash),
            ProofForestEdge::Congruence {
                parent: p,
                level,
                hash,
                ..
            }
            | ProofForestEdge::Equality {
                parent: p,
                level,
                hash,
                ..
            } => {
                let (l, h) = if *level > highest_level {
                    (*level, *hash)
                } else {
                    (highest_level, highest_hash)
                };
                self.find_with_level(*p, l, h)
            }
        }
    }

    /// Adds a disequality between t1 and t2 to the egraph
    fn add_disequality(&mut self, t1: u32, t2: u32, diseq_lit: i32, level: usize, hash: u32) {
        let t1_root = self.find(t1);
        let t2_root = self.find(t2);
        let disequality1 = DisequalTerm {
            term: t2_root,
            diseq_lit,
            level,
            hash,
            original_disequality: (t1, t2),
        };
        let disequality2 = DisequalTerm {
            term: t1_root,
            diseq_lit,
            level,
            hash,
            original_disequality: (t1, t2),
        };
        debug_println!(
            12,
            0,
            "Adding a disequality between {} and {} at level {} and hash {}",
            self.display_term(t1),
            self.display_term(t2),
            level,
            hash
        );
        assert!(t2_root == disequality1.term);
        assert!(t1_root != disequality1.term);
        self.proof_forest[t1_root as usize].add_disequality(
            t2_root,
            disequality1.clone(),
            &self.predecessor_level,
        );
        assert!(t1_root == disequality2.term);
        assert!(t2_root != disequality2.term);
        self.proof_forest[t2_root as usize].add_disequality(
            t1_root,
            disequality2.clone(),
            &self.predecessor_level,
        );
    }

    /// Checks if term t is equal to itself
    fn check_self_disequality(&self, t: u32) -> Option<DisequalTerm> {
        assert!(t == self.find(t));
        debug_println!(
            19,
            1,
            "We are in check_self_disequality with t {}",
            self.display_term(t)
        );
        let t_disequalities = &self.proof_forest[t as usize].disequalities();
        debug_println!(19, 2, "We have t_disequalities {:?}", t_disequalities);

        let sorted_disequalities: Vec<_> = t_disequalities.iter().collect();

        for (key, disequality) in sorted_disequalities {
            if !valid_hash(disequality.hash, disequality.level, &self.predecessor_level) {
                debug_println!(
                    19,
                    0,
                    "We are skipping disequality with {}, disequality: {:?} because it is not at the same level does not have key {}",
                    self.display_term(disequality.term),
                    disequality,
                    self.predecessor_level[disequality.level]
                );
                continue;
            }
            assert!(*key == disequality.term);
            let root = self.find(*key);
            debug_println!(
                19,
                3,
                "We are in check_self_disequality with {} [{}] and root {} [{}] and original term {}",
                self.display_term(t),
                t,
                self.display_term(root),
                root,
                self.display_term(disequality.term)
            );
            if root == t {
                debug_println!(
                    19,
                    4,
                    "We have found a key {} [{}], disequality {:?} with root: {}, t: {}, disequality.term {} and original_disequality {} != {}",
                    self.display_term(*key),
                    key,
                    disequality,
                    self.display_term(root),
                    self.display_term(t),
                    self.display_term(disequality.term),
                    self.display_term(disequality.original_disequality.0),
                    self.display_term(disequality.original_disequality.1)
                );
                // we expect the two terms in the disequality to be equal to each other
                return Some(disequality.clone());
            }
        }
        None
    }

    /// Compute the signature key for a term: (op, [find(c1), ..., find(cn)]).
    /// Returns None for terms that don't participate in congruence (non-App/Eq/Ite ops, or opaque terms).
    fn compute_signature(&self, term_id: u32) -> Option<SigKey> {
        let entry = match &self.terms[term_id as usize] {
            TermSlot::Term(e) => e,
            _ => return None,
        };
        let op = match &entry.op {
            Op::App(s) => CanonicalOp::App(s.to_string()),
            Op::Eq => CanonicalOp::Eq,
            Op::Ite => CanonicalOp::Ite,
            _ => return None,
        };
        let canonical_children: Vec<u32> = entry
            .children
            .as_slice()
            .iter()
            .map(|&c| self.find(c))
            .collect();
        Some((op, Children::from_slice(&canonical_children)))
    }

    /// Insert a term into the sig_table, recording a trail entry for backtracking.
    fn sig_table_insert(&mut self, key: SigKey, term_id: u32, level: usize) {
        self.sig_table.insert(key.clone(), term_id);
        self.sig_trail.push((level, key, term_id, true));
    }

    /// Build a congruence proof edge and merge two terms that have the same signature.
    /// Returns the result of cc_union (which may contain a conflict).
    fn congruence_merge(&mut self, a: u32, b: u32, level: usize) -> EgraphResult<u32> {
        let a_children = match &self.terms[a as usize] {
            TermSlot::Term(e) => e.children.as_slice().to_vec(),
            _ => Vec::new(),
        };
        let b_children = match &self.terms[b as usize] {
            TermSlot::Term(e) => e.children.as_slice().to_vec(),
            _ => Vec::new(),
        };
        let pairs: Vec<(u32, u32)> = a_children.into_iter().zip(b_children).collect();
        let proof_parent = ProofForestEdge::Congruence {
            size: 0,
            pairs,
            parent: 0,
            child: 0,
            disequalities: DeterministicHashMap::new(),
            level,
            hash: self.predecessor_hash,
            children: DeterministicHashSet::new(),
        };
        self.cc_union(a, b, proof_parent, level)
    }

    /// Adds a predecessor to a term (for example f(x) to x)
    ///
    /// TODO: right now this is preferring the smallest level, but this might not always be
    /// correct depending on the invariants
    fn add_predecessor(&mut self, term: u32, new_pred_key: u32, new_pred: Predecessor) {
        debug_println!(
            5,
            0,
            "We are in add_predecessor with term {} and new_pred_key {} and new_pred {:?}",
            self.display_term(term),
            self.display_term(new_pred_key),
            new_pred
        );

        // Compute new_pred validity before entering the Entry so we don't
        // re-borrow self while holding an occupied slot.
        let new_valid = valid_hash(new_pred.hash, new_pred.level, &self.predecessor_level);
        let new_pred_level = new_pred.level;
        let new_pred_hash = new_pred.hash;
        let installed = new_pred.clone();
        let mut previous = None;
        let mut changed = false;

        use std::collections::hash_map::Entry;
        match self.predecessors[term as usize].entry(new_pred_key) {
            Entry::Vacant(slot) => {
                slot.insert(new_pred);
                changed = true;
                debug_println!(
                    11,
                    0,
                    "For term {}, we are adding the predecessor {} [level {}, hash {}]",
                    self.display_term(term),
                    self.display_term(new_pred_key),
                    new_pred_level,
                    new_pred_hash
                );
            }
            Entry::Occupied(mut slot) => {
                // Inline valid_hash for the original so we don't need &self inside
                // the occupied borrow. Matches valid_hash's body exactly (minus
                // its debug_println at level 5, which has no functional effect).
                let original = slot.get();
                let orig_valid = valid_hash(original.hash, original.level, &self.predecessor_level);
                // original.hash >= self.predecessor_level[original.level]
                //     || original.hash == 0
                //     || original.level == 0;
                let orig_level = original.level;
                let orig_hash = original.hash;
                let orig_predecessor = original.predecessor;
                let should_replace = (!orig_valid || new_pred_level <= orig_level) && new_valid;
                if should_replace {
                    previous = Some(original.clone());
                    slot.insert(new_pred);
                    changed = true;
                    debug_println!(
                        11,
                        0,
                        "For term {}, we are replacing the predecessor {} [level {}, hash {}] with predecessor {} [level {}, hash {}]",
                        self.display_term(term),
                        self.display_term(orig_predecessor),
                        orig_level,
                        orig_hash,
                        self.display_term(new_pred_key),
                        new_pred_level,
                        new_pred_hash
                    );
                }
                // Keep-old case: zero inserts, no debug output (matches original).
            }
        }
        if changed && new_pred_level != 0 {
            while new_pred_level >= self.predecessor_trail.len() {
                self.predecessor_trail.push(Vec::new());
            }
            self.predecessor_trail[new_pred_level].push(PredecessorTrailEntry {
                term,
                key: new_pred_key,
                previous,
                installed,
            });
        }
    }

    /// Explain why u ≡ v by walking the proof forest to their least common ancestor.
    /// Returns None if u and v are not in the same equivalence class.
    fn leastcommonancestor(&self, u: u32, v: u32) -> Option<Vec<(u32, u32)>> {
        debug_println!(
            11,
            1,
            "Finding least common ancestor for {} and {}",
            self.display_term(u),
            self.display_term(v)
        );
        self.leastcommonancestor_helper(u, v, 0)
    }

    fn leastcommonancestor_helper(&self, u: u32, v: u32, indent: usize) -> Option<Vec<(u32, u32)>> {
        debug_println!(
            20,
            indent,
            "checking the equality of {} and {}",
            self.display_term(u),
            self.display_term(v)
        );
        let mut visited = FastDeterministicHashSet::default();

        let mut path_from_u: Vec<u32> = vec![];
        let mut curr = u;

        let max_recursion_depth = 100;
        if indent > max_recursion_depth {
            debug_println!(11, 0, "We have the proof forest :{}", self);
            panic!("Should not have this many recursive calls to LCH");
        }
        loop {
            visited.insert(curr);
            if let ProofForestEdge::Root { .. } = self.proof_forest[curr as usize] {
                break;
            }
            path_from_u.push(curr);
            curr = self.proof_forest[curr as usize].get_parent();
        }

        let mut path_from_v: Vec<u32> = vec![];
        curr = v;
        loop {
            if visited.contains(&curr) {
                break;
            }
            if let ProofForestEdge::Root { .. } = self.proof_forest[curr as usize] {
                return None;
            }
            path_from_v.push(curr);
            curr = self.proof_forest[curr as usize].get_parent();
        }
        let lca = curr;

        assert!(visited.contains(&curr));

        let mut final_proof = vec![];
        let mut proof_congruences: Vec<&[(u32, u32)]> = vec![];

        let proof_nodes = path_from_u
            .iter()
            .take_while(|&&node| node != lca)
            .chain(path_from_v.iter());

        debug_println!(16, indent + 1, "We have the proof:");
        for &node in proof_nodes {
            match &self.proof_forest[node as usize] {
                ProofForestEdge::Root { .. } => {
                    eprintln!("ERROR: Root should not be processed");
                    std::process::exit(1);
                }
                ProofForestEdge::Congruence { pairs, .. } => {
                    if is_important(20) {
                        debug_println!(20, indent + 12, "Congruence ");
                        for &(t1, t2) in pairs.iter() {
                            debug_println!(
                                20,
                                indent + 12,
                                "{} [{}] ~ {} [{}] ",
                                self.display_term(t1),
                                t1,
                                self.display_term(t2),
                                t2
                            );
                        }
                    }
                    proof_congruences.push(pairs.as_slice());
                }
                ProofForestEdge::Equality { term, .. } => {
                    if let Some(&(t1, t2)) = term.as_ref() {
                        debug_println!(
                            20,
                            indent + 12,
                            "Equality {} [{}] = {} [{}]",
                            self.display_term(t1),
                            t1,
                            self.display_term(t2),
                            t2
                        );
                        final_proof.push((t1, t2));
                        debug_println!(
                            11,
                            1,
                            "We have the current final proof is: {:?}",
                            final_proof
                        )
                    }
                }
            }
        }

        for pairs in proof_congruences {
            for &(a, b) in pairs {
                if let Some(subproof) = self.leastcommonancestor_helper(a, b, indent + 1) {
                    final_proof.extend(subproof);
                }
            }
        }
        Some(final_proof)
    }

    /// Assert t1 = t2 at the current decision level.
    /// Performs congruence closure. Returns a conflict if a disequality is violated.
    fn assert_equal(&mut self, t1: u32, t2: u32) -> EgraphResult<u32> {
        let level = self.decision_level;
        let proof_parent = ProofForestEdge::Equality {
            size: 0,
            term: Some((t1, t2)),
            parent: 0,
            child: 0,
            disequalities: DeterministicHashMap::new(),
            level,
            hash: self.predecessor_hash,
            children: DeterministicHashSet::new(),
        };
        self.cc_union(t1, t2, proof_parent, level)
    }

    /// Assert t1 ≠ t2 at the current decision level.
    /// Returns a conflict if t1 and t2 are already in the same equivalence class.
    fn assert_disequal(&mut self, t1: u32, t2: u32, diseq_lit: i32) -> EgraphResult<u32> {
        let level = self.decision_level;
        if let Some(equalities) = self.leastcommonancestor(t1, t2) {
            // diseq_lit is None: the disequality being asserted is implicit in the
            // conflict (the caller reconstructs it from the assertion context).
            return EgraphResult::with_conflict(Conflict {
                equalities,
                disequality: (t1, t2),
                diseq_lit: None,
            });
        }
        let hash = self.predecessor_hash;
        self.add_disequality(t1, t2, diseq_lit, level, hash);
        EgraphResult::ok()
    }

    /// Assert all terms are pairwise distinct at the current decision level.
    fn assert_distinct(&mut self, terms: &[u32], diseq_lit: i32) -> EgraphResult<u32> {
        for i in 0..terms.len() {
            for j in i + 1..terms.len() {
                let result = self.assert_disequal(terms[i], terms[j], diseq_lit);
                if result.conflict.is_some() {
                    return result;
                }
            }
        }
        EgraphResult::ok()
    }

    /// Undo all egraph operations at levels strictly greater than `level`.
    fn backtrack_to(&mut self, level: usize) {
        self.backtrack_match_relevance(level);
        self.predecessor_hash += 1;

        for i in level + 1..self.decision_level + 1 {
            self.predecessor_level[i] = self.predecessor_hash;
        }

        self.decision_level = level;

        // Pop proof forest backtrack stack (restore UF first)
        while !self.proof_forest_backtrack_stack.is_empty() {
            let last_level = self.proof_forest_backtrack_stack.last().unwrap().0;
            if last_level <= level {
                break;
            }
            let (_, backtrack_equality, y, y_root, x_root, merged_y_root) =
                self.proof_forest_backtrack_stack.pop().unwrap();
            self.proof_forest_backtrack(backtrack_equality, y, y_root);
            // Swapping the same two links restores both pre-merge cycles.
            self.member_next
                .swap(x_root as usize, merged_y_root as usize);
        }

        // Replay sig_trail in reverse AFTER UF is restored.
        // Use the stored key directly — recomputing from find() would give the wrong key.
        while let Some((entry_level, _, _, _)) = self.sig_trail.last() {
            if *entry_level <= level {
                break;
            }
            let (_, key, term_id, was_inserted) = self.sig_trail.pop().unwrap();
            if was_inserted {
                if self.sig_table.get(&key) == Some(&term_id) {
                    self.sig_table.remove(&key);
                }
            } else {
                self.sig_table.insert(key, term_id);
            }
        }

        // Re-add predecessors created by quantifiers at their new roots.
        // Skip entries added at or below `level`: their predecessor stamps are
        // still valid (predecessor_level only got bumped for levels > `level`)
        // and their roots didn't shift because of any pop above `level`.
        for (term, parents) in &self.predecessors_created_by_quantifiers.clone() {
            let current_ancestor = self.find(*term);
            for (parent, added_at) in parents {
                if *added_at <= level {
                    continue;
                }
                let predecessor = Predecessor {
                    level,
                    hash: self.predecessor_hash,
                    predecessor: *parent,
                    inner_term: *term,
                };
                self.add_predecessor(current_ancestor, *parent, predecessor);
            }
        }

        // Any merges left in the arithmetic queue from before this backtrack
        // are stale — they refer to unions at levels we've just undone. Clear
        // them so that only re-fired congruence merges (added by the loop
        // below) survive.
        self.arithmetic_merge_queue.clear();
        self.relevancy_merge_queue.clear();

        // Re-do union_to_eclass via sig table probe. Entries added at or below
        // `level` were already reconciled with the sig_table at that level and
        // their signatures are stable under this backtrack.
        let union_to_eclass_info = self.union_to_eclass.clone();
        for (term, added_at) in union_to_eclass_info {
            if added_at <= level {
                continue;
            }
            if let Some(sig) = self.compute_signature(term) {
                if let Some(&existing) = self.sig_table.get(&sig) {
                    if self.find(existing) != self.find(term) {
                        self.congruence_merge(existing, term, self.decision_level);
                    }
                } else {
                    self.sig_table_insert(sig, term, self.decision_level);
                }
            }
        }

        // Clear at level 0
        if level == 0 {
            self.predecessors_created_by_quantifiers = DeterministicHashMap::new();
            self.union_to_eclass = DeterministicHashMap::new();
            self.proof_forest_backtrack_stack = vec![];
            self.sig_trail.clear();
        }
    }

    /// Undo a single union operation during backtracking.
    fn proof_forest_backtrack(
        &mut self,
        equality: ProofForestEdge,
        y: u32,
        y_parent: ProofForestEdge,
    ) {
        let child = &equality.get_child();
        let child_edge = self.proof_forest[*child as usize].clone();
        let parent = &equality.get_parent();
        let parent_edge = self.proof_forest[*parent as usize].clone();

        assert_eq!(self.find(*child), self.find(*parent));

        debug_println!(
            16,
            0,
            "Backtracking on {} with child {} and parent {} and y_term {}",
            equality,
            self.display_term(*child),
            self.display_term(*parent),
            self.display_term(y)
        );

        debug_println!(
            6,
            0,
            "We are in proof_forest_backtrack trying to get term for {:?}",
            child
        );

        debug_println!(
            6,
            0,
            "We have child_edge {:?}, parent_edge {:?} and equality {:?}",
            child_edge,
            parent_edge,
            equality
        );
        let (child, child_edge, _parent, _parent_edge) = if child_edge != equality {
            debug_println!(6, 0, "we are reversing the edge");
            debug_println!(10, 0, "{}", self);
            assert_eq!(parent_edge.get_parent(), equality.get_child());
            debug_println!(6, 0, "after first assert");
            assert_eq!(parent_edge.get_child(), equality.get_parent());
            (parent, parent_edge, child, child_edge)
        } else {
            (child, child_edge, parent, parent_edge)
        };

        debug_println!(
            6,
            0,
            "We are setting the predecessors of the child {} to {:?}",
            self.display_term(*child),
            self.predecessors[*child as usize]
        );

        let childs_child = child_edge.get_child();

        let mut new_disequalities = DeterministicHashMap::new();
        for (k, v) in child_edge.disequalities().iter() {
            if valid_hash(v.hash, v.level, &self.predecessor_level) {
                debug_println!(11, 0, "Keeping disequality {}: {} in {}", k, v, child);
                new_disequalities.insert(*k, v.clone());
            } else {
                debug_println!(
                    11,
                    0,
                    "Removing disequality {}: {} from {}",
                    k,
                    v,
                    child_edge
                );
            }
        }

        // Splitting an arithmetic class yields two arithmetic classes, so
        // both new roots inherit the flag from the still-merged class.
        let merged_root_arithmetic = matches!(
            &self.proof_forest[self.find(*child) as usize],
            ProofForestEdge::Root {
                arithmetic: true,
                ..
            }
        );

        let child_root = ProofForestEdge::Root {
            size: 0,
            child: childs_child,
            disequalities: new_disequalities,
            children: DeterministicHashSet::new(),
            arithmetic: merged_root_arithmetic,
        };

        self.proof_forest[*child as usize] = child_root;

        debug_println!(
            16,
            0,
            "Making {} the root on a backtrack",
            self.display_term(y)
        );
        self.make_root(y, y_parent);
    }

    /// Union two terms in the egraph, merging their equivalence classes
    /// and adding edge x -> y. Good for recovering proof at the end,
    /// but this could double/triple the max tree size at each iteration
    ///
    /// design decision: don't have eager updates for equivalence class and inverting tree
    fn cc_union(
        &mut self,
        x: u32,
        y: u32,
        proof_parent: ProofForestEdge,
        level: usize,
    ) -> EgraphResult<u32> {
        let x_root = self.find(x);
        let y_root = self.find(y);
        debug_println!(6, 1, "{}", self);
        debug_println!(6, 0, "before1");
        debug_println!(
            22,
            1,
            "Unioning vertices [{}] {}  and [{}] {}  (roots: {} [{}] and {} [{}]) at level {} with {}",
            x,
            self.display_term(x),
            y,
            self.display_term(y),
            x_root,
            self.display_term(x_root),
            y_root,
            self.display_term(y_root),
            level,
            proof_parent
        );

        if x_root == y_root {
            debug_println!(
                16,
                2,
                "{} and {} are already in the same equivalence class",
                self.display_term(x),
                self.display_term(y)
            );
            return EgraphResult::ok();
        }

        let x_root_is_const = self.is_constant(x_root);
        let y_root_is_const = self.is_constant(y_root);

        // Two distinct constants merged — immediate conflict since constant
        // disequality is implicit (no SAT literal needed).
        if x_root_is_const && y_root_is_const {
            debug_assert!(self.display_term(x_root) != self.display_term(y_root));
            let mut equalities = Vec::new();
            if x != x_root
                && let Some(path) = self.leastcommonancestor(x, x_root)
            {
                equalities.extend(path);
            }
            // Explain the current merge from the proof_parent edge
            match &proof_parent {
                ProofForestEdge::Equality {
                    term: Some((t1, t2)),
                    ..
                } => {
                    equalities.push((*t1, *t2));
                }
                ProofForestEdge::Congruence { pairs, .. } => {
                    for (a, b) in pairs {
                        if let Some(path) = self.leastcommonancestor(*a, *b) {
                            equalities.extend(path);
                        }
                    }
                }
                _ => {}
            }
            if y != y_root
                && let Some(path) = self.leastcommonancestor(y, y_root)
            {
                equalities.extend(path);
            }
            return EgraphResult::with_conflict(Conflict {
                equalities,
                disequality: (x_root, y_root),
                diseq_lit: None,
            });
        }

        self.stats.merges += 1;

        // Ensure the constant (if any) remains the root: make the constant
        // side "x" so that x_root stays as root after the union.
        let (x, y, x_root, y_root) = if y_root_is_const {
            (y, x, y_root, x_root)
        } else {
            (x, y, x_root, y_root)
        };

        if self.track_all_merges {
            self.relevancy_merge_queue.push(EgraphMergeEvent {
                survivor: x_root,
                demoted: y_root,
                survivor_members: self.member_range_for_root(x_root),
                demoted_members: self.member_range_for_root(y_root),
                level,
            });
        }

        // `mark_arithmetic` runs *after* `register_term` in
        // `insert_predecessor`, so a congruence merge here can precede tagging
        // on one side. If either root is tagged, queue the merge and upgrade
        // the surviving root's flag so it stays tagged going forward.
        let x_root_arith = matches!(
            &self.proof_forest[x_root as usize],
            ProofForestEdge::Root {
                arithmetic: true,
                ..
            }
        );
        let y_root_arith = matches!(
            &self.proof_forest[y_root as usize],
            ProofForestEdge::Root {
                arithmetic: true,
                ..
            }
        );
        if x_root_arith || y_root_arith {
            if self.incremental_arithmetic {
                self.arithmetic_merge_queue.push((x_root, y_root));
            }
            if !x_root_arith
                && let ProofForestEdge::Root { arithmetic, .. } =
                    &mut self.proof_forest[x_root as usize]
            {
                *arithmetic = true;
            }
        }

        // making x the parent of y ~> could also do this based on relative depth of x and y tree
        let proof_parent: ProofForestEdge =
            proof_parent.with_parent(x, y, level, self.predecessor_hash);

        let y_root_parent = &self.proof_forest[y_root as usize];

        if level > 0 {
            debug_println!(
                16,
                0,
                "BACKTTRACK STACK: adding equalitity between {} and {} with y_root: {} at level {}",
                self.display_term(x),
                self.display_term(y),
                self.display_term(y_root),
                level
            );
            self.proof_forest_backtrack_stack.push((
                level,
                proof_parent.clone(),
                y_root,
                y_root_parent.clone(),
                x_root,
                y_root,
            ));
        }

        // Splice the two circular member lists in O(1). This list is
        // independent of proof-tree orientation, so use the pre-merge roots.
        self.member_next.swap(x_root as usize, y_root as usize);

        // Perform the union first so we can check for disequality violations early.
        debug_println!(
            16,
            2,
            "Making {} the root of its equivalence class [previously was {}]",
            self.display_term(y),
            self.display_term(y_root)
        );
        self.make_root(y, proof_parent);

        // Early conflict check: x_root's existing disequalities may already be
        // violated now that y's class has been merged in.
        if let Some(disequality) = self.check_self_disequality(x_root) {
            if let Some(equalities) = self.leastcommonancestor(
                disequality.original_disequality.0,
                disequality.original_disequality.1,
            ) {
                return EgraphResult::with_conflict(Conflict {
                    equalities,
                    disequality: disequality.original_disequality,
                    diseq_lit: Some(disequality.diseq_lit),
                });
            } else {
                panic!(
                    "Should have found a equality between {} [root: {}] and {} [root: {}]",
                    self.display_term(disequality.original_disequality.0),
                    self.display_term(self.find(disequality.original_disequality.0)),
                    self.display_term(disequality.original_disequality.1),
                    self.display_term(self.find(disequality.original_disequality.1)),
                );
            }
        }

        // need to add the new disequalities into x_root
        // TODO: could also clean up some backtracking stuff here, probably want to factor this into its own function
        let (x_root_disequalities_edge, y_root_disequalities_edge) = if x_root > y_root {
            let split = self.proof_forest.split_at_mut(x_root as usize);
            (&mut split.1[0], &split.0[y_root as usize])
        } else {
            let split = self.proof_forest.split_at_mut(y_root as usize);
            (&mut split.0[x_root as usize], &split.1[0])
        };

        let y_root_disequalities = y_root_disequalities_edge.disequalities();
        let x_root_disequalities = x_root_disequalities_edge.disequalities_mut();

        // when we copy things over, make sure we only copy things over that are valid and that we are updating the hash/level -> this caused some very tricky bugs
        // TODO: write helper functions to make copying over hased things easier
        for (key, value) in y_root_disequalities {
            // make sure we update the disequality level
            if valid_hash(value.hash, value.level, &self.predecessor_level) {
                // we can have that we introduce a new equality via eclass option after a quantifier instantiation
                // this equality could be at level 0
                // but then it's possible that there are disequalities that get copied over such that one of the disequalities are at a level higher than 0
                let (diseq_level, diseq_hash) = if value.level > level {
                    (value.level, value.hash)
                } else {
                    (level, self.predecessor_level[level])
                };

                let new_value = DisequalTerm {
                    term: value.term,
                    diseq_lit: value.diseq_lit,
                    level: diseq_level,
                    hash: diseq_hash,
                    original_disequality: value.original_disequality,
                };
                // this assert is obviously not true as x_root_disequalities could contain key
                // but then why is it not a problem that we are overwriting it
                // assert!(!x_root_disequalities.contains_key(key));

                if let Some(x_disequality) = x_root_disequalities.get(key)
                    && (x_disequality.hash >= self.predecessor_level[x_disequality.level]
                        || x_disequality.hash == 0)
                {
                    debug_println!(
                        12,
                        0,
                        "Skipping disequality {} : {} to {} at level {}",
                        key,
                        new_value,
                        x_root,
                        level
                    );
                    continue;
                }

                debug_println!(
                    12,
                    0,
                    "Adding disequality {} : {} to {} at level {}",
                    key,
                    new_value,
                    x_root,
                    level
                );
                x_root_disequalities.insert(*key, new_value);
            }
        }

        // No explicit sig_table removal phase needed: old entries keyed on y_root
        // become stale (unreachable by compute_signature after the union) and are
        // naturally superseded by the fresh insertions below.
        // Reinsert y_root's predecessors into sig_table with new canonical forms
        // and immediately merge any congruent pairs found.
        // Also move predecessors from y_root to x_root.
        let predecessors_v = std::mem::take(&mut self.predecessors[y_root as usize]);
        let mut y_root_pred_keys: Vec<u32> = Vec::new();
        for (pred_key, pred_val) in &predecessors_v {
            let new_pred = Predecessor {
                level,
                hash: self.predecessor_hash,
                predecessor: *pred_key,
                inner_term: pred_val.inner_term,
            };
            self.add_predecessor(x_root, *pred_key, new_pred);
            if valid_hash(pred_val.hash, pred_val.level, &self.predecessor_level) {
                y_root_pred_keys.push(*pred_key);
            }
        }
        self.predecessors[y_root as usize] = predecessors_v;
        for &pred_id in &y_root_pred_keys {
            if let Some(new_sig) = self.compute_signature(pred_id) {
                if let Some(&existing) = self.sig_table.get(&new_sig) {
                    if self.find(existing) != self.find(pred_id) {
                        let sub_result = self.congruence_merge(existing, pred_id, level);
                        if sub_result.conflict.is_some() {
                            return sub_result;
                        }
                    }
                } else {
                    self.sig_table_insert(new_sig, pred_id, level);
                }
            }
        }

        debug_assert!(
            !x_root_is_const || self.find(x_root) == x_root,
            "constant root invariant violated for {}",
            self.display_term(x_root)
        );

        EgraphResult::ok()
    }

    /// Make vertex the root of its proof-forest tree.
    fn make_root(&mut self, vertex: u32, proof_parent: ProofForestEdge) {
        debug_println!(
            16,
            0,
            "Making {} the root with proof_parent {}",
            self.display_term(vertex),
            proof_parent
        );
        let old_parent = self.proof_forest[vertex as usize].clone();
        let disequalities = match old_parent {
            ProofForestEdge::Root { disequalities, .. } => disequalities,
            ProofForestEdge::Congruence {
                size: _,
                pairs,
                parent,
                child,
                disequalities,
                level,
                hash,
                children,
            } => {
                assert_eq!(child, vertex);
                self.make_root(
                    parent,
                    ProofForestEdge::Congruence {
                        size: 0,
                        pairs,
                        parent: vertex,
                        child: parent,
                        disequalities: DeterministicHashMap::new(),
                        level,
                        hash,
                        children,
                    },
                );
                disequalities
            }
            ProofForestEdge::Equality {
                term,
                parent,
                child,
                disequalities,
                level,
                hash,
                children,
                ..
            } => {
                assert_eq!(child, vertex);
                self.make_root(
                    parent,
                    ProofForestEdge::Equality {
                        size: 0,
                        term,
                        parent: vertex,
                        child: parent,
                        disequalities: DeterministicHashMap::new(),
                        level,
                        hash,
                        children,
                    },
                );
                disequalities
            }
        };
        let new_proof_parent = proof_parent.set_disequalities(disequalities);
        self.proof_forest[vertex as usize] = new_proof_parent;
    }

    /// E-matching: given a partial assignment and trigger-term pairs, find all
    /// satisfying substitutions. This is the core e-matching algorithm.
    /// E-matching: given a partial assignment and trigger-term pairs, find all
    /// satisfying substitutions. Returns variable name → matched term ID.
    /// Match a list of (pattern, ground_hint) pairs against the egraph.
    /// Returns all valid variable assignments.
    fn match_patterns(
        &self,
        assignment: &mut DeterministicHashMap<Local, u32>,
        pattern_term_pairs: &[(PatternId, Option<u32>)],
        relevant_only: bool,
    ) -> Vec<DeterministicHashMap<Local, u32>> {
        if pattern_term_pairs.is_empty() {
            return vec![assignment.clone()];
        }
        let (pattern_id, ground_hint) = pattern_term_pairs[0];
        let pattern = &self.compiled_patterns[pattern_id];
        self.match_pattern_recursive(
            assignment,
            pattern,
            ground_hint,
            &pattern_term_pairs[1..],
            relevant_only,
        )
    }

    /// Match a single pattern against an optional ground term, then continue with remaining pairs.
    fn match_pattern_recursive(
        &self,
        assignment: &mut DeterministicHashMap<Local, u32>,
        pattern: &Pattern,
        ground_hint: Option<u32>,
        remaining: &[(PatternId, Option<u32>)],
        relevant_only: bool,
    ) -> Vec<DeterministicHashMap<Local, u32>> {
        match pattern {
            Pattern::Var(name) => {
                let ground = ground_hint.expect("Pattern::Var requires a ground term to bind");
                match assignment.get(name) {
                    None => {
                        assignment.insert(name.clone(), ground);

                        self.match_patterns(assignment, remaining, relevant_only)
                    }
                    Some(v) if self.find(*v) == self.find(ground) => {
                        self.match_patterns(assignment, remaining, relevant_only)
                    }
                    Some(_) => vec![],
                }
            }
            Pattern::Ground(egraph_id) => match ground_hint {
                Some(ground) if self.find(*egraph_id) == self.find(ground) => {
                    self.match_patterns(assignment, remaining, relevant_only)
                }
                None => self.match_patterns(assignment, remaining, relevant_only),
                _ => vec![],
            },
            Pattern::App(op, sub_patterns) => {
                let func_name = op.to_function_map_key();
                self.find_assignments_on_pattern(
                    ground_hint,
                    &func_name,
                    sub_patterns,
                    remaining,
                    assignment,
                    relevant_only,
                )
            }
        }
    }

    /// Find all function applications matching the given op, then recurse into sub-patterns.
    fn find_assignments_on_pattern(
        &self,
        ground_hint: Option<u32>,
        func_name: &str,
        sub_patterns: &[Pattern],
        remaining: &[(PatternId, Option<u32>)],
        assignment: &mut DeterministicHashMap<Local, u32>,
        relevant_only: bool,
    ) -> Vec<DeterministicHashMap<Local, u32>> {
        let ground_root = ground_hint.map(|t| self.find(t));
        let function_map = if relevant_only && ground_root.is_none() {
            &self.relevant_function_maps
        } else {
            &self.function_maps
        };
        let function_terms = match function_map.get(func_name) {
            Some(terms) => terms,
            None => return vec![],
        };

        let mut list_assignments = Vec::new();
        let mut considered_function_terms = DeterministicHashSet::default();

        for (i, subterms) in function_terms {
            self.e_match_candidates_scanned
                .set(self.e_match_candidates_scanned.get() + 1);
            if relevant_only && ground_root.is_none() {
                self.e_match_relevant_candidates_scanned
                    .set(self.e_match_relevant_candidates_scanned.get() + 1);
            }
            if subterms.len() != sub_patterns.len() {
                continue;
            }

            if relevant_only
                && ground_root.is_none()
                && self.e_matching_relevance_levels[*i as usize].is_none()
            {
                continue;
            }
            let i_root = self.find(*i);
            if relevancy_trace_enabled() && relevant_only && ground_root.is_none() {
                eprintln!(
                    "[relevancy] e-match indexed candidate func={} term_id={} class={} children={:?}",
                    func_name, i, i_root, subterms
                );
            }
            if ground_root.is_none() || ground_root.unwrap() == i_root {
                // With relevancy filtering, distinct relevant enodes in the
                // same e-class can become visible at different times and can
                // carry different syntactic substitutions (notably for
                // Boolean terms whose SAT value is not represented as an
                // egraph merge). Preserve those enodes here and let the
                // quantifier-level substitution set remove true duplicates.
                // Without filtering, retain the existing canonical e-class
                // deduplication behavior.
                let dedup_subterms: Vec<u32> = if relevant_only {
                    subterms.clone()
                } else {
                    subterms.iter().map(|s| self.find(*s)).collect()
                };

                if considered_function_terms.contains(&dedup_subterms) {
                    continue;
                }
                considered_function_terms.insert(dedup_subterms);

                let new_assignments = self.match_subpatterns(
                    &mut assignment.clone(),
                    sub_patterns,
                    subterms,
                    remaining,
                    relevant_only,
                );
                list_assignments.extend(new_assignments);
            }
        }
        list_assignments
    }

    /// Match sub-patterns against ground subterms, then continue with remaining pattern pairs.
    fn match_subpatterns(
        &self,
        assignment: &mut DeterministicHashMap<Local, u32>,
        sub_patterns: &[Pattern],
        ground_subterms: &[u32],
        remaining: &[(PatternId, Option<u32>)],
        relevant_only: bool,
    ) -> Vec<DeterministicHashMap<Local, u32>> {
        if sub_patterns.is_empty() {
            return self.match_patterns(assignment, remaining, relevant_only);
        }
        let pattern = &sub_patterns[0];
        let ground = ground_subterms[0];
        let rest_patterns = &sub_patterns[1..];
        let rest_grounds = &ground_subterms[1..];

        match pattern {
            Pattern::Var(name) => match assignment.get(name) {
                None => {
                    assignment.insert(name.clone(), ground);
                    self.match_subpatterns(
                        assignment,
                        rest_patterns,
                        rest_grounds,
                        remaining,
                        relevant_only,
                    )
                }
                Some(v) if self.find(*v) == self.find(ground) => self.match_subpatterns(
                    assignment,
                    rest_patterns,
                    rest_grounds,
                    remaining,
                    relevant_only,
                ),
                Some(_) => vec![],
            },
            Pattern::Ground(egraph_id) => {
                if self.find(*egraph_id) == self.find(ground) {
                    self.match_subpatterns(
                        assignment,
                        rest_patterns,
                        rest_grounds,
                        remaining,
                        relevant_only,
                    )
                } else {
                    vec![]
                }
            }
            Pattern::App(op, children) => {
                let func_name = op.to_function_map_key();
                let function_terms = match self.function_maps.get(&func_name) {
                    Some(terms) => terms,
                    None => return vec![],
                };

                let mut list_assignments = Vec::new();
                let ground_root = self.find(ground);
                let mut considered = DeterministicHashSet::default();

                for (i, subterms) in function_terms {
                    self.e_match_candidates_scanned
                        .set(self.e_match_candidates_scanned.get() + 1);
                    if subterms.len() != children.len() {
                        continue;
                    }
                    let i_root = self.find(*i);
                    // Here ground_root is pinned by the parent match, so
                    // any candidate with a matching class root is a valid
                    // sub-match — no need for the class_filter guard.
                    if ground_root == i_root {
                        let subterms_canonical: Vec<u32> =
                            subterms.iter().map(|s| self.find(*s)).collect();
                        if considered.contains(&subterms_canonical) {
                            continue;
                        }
                        considered.insert(subterms_canonical);

                        let mut sub_assignment = assignment.clone();
                        let sub_results = self.match_subpatterns(
                            &mut sub_assignment,
                            children,
                            subterms,
                            &[],
                            relevant_only,
                        );
                        for mut sub in sub_results {
                            let more = self.match_subpatterns(
                                &mut sub,
                                rest_patterns,
                                rest_grounds,
                                remaining,
                                relevant_only,
                            );
                            list_assignments.extend(more);
                        }
                    }
                }
                list_assignments
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Egraph;
    use crate::egraphs::EgraphTrait;
    use crate::egraphs::repr::{Op, Pattern};
    use crate::utils::DeterministicHashSet;

    fn class_members(egraph: &Egraph, start: u32) -> Vec<u32> {
        let mut members = vec![start];
        let mut current = egraph.member_next[start as usize];
        while current != start {
            assert!(
                members.len() <= egraph.next_id as usize,
                "e-class member cycle did not return to its start"
            );
            members.push(current);
            current = egraph.member_next[current as usize];
        }
        members
    }

    #[test]
    fn member_lists_splice_and_backtrack_with_unions() {
        let mut egraph = Egraph::new();
        let a = egraph.register_opaque();
        let b = egraph.register_opaque();
        let c = egraph.register_opaque();
        egraph.set_track_all_merges(true);

        assert_eq!(class_members(&egraph, a), vec![a]);
        assert_eq!(class_members(&egraph, b), vec![b]);
        assert_eq!(class_members(&egraph, c), vec![c]);

        egraph.notify_new_decision_level();
        assert!(egraph.assert_equal(a, b).conflict.is_none());
        assert_eq!(class_members(&egraph, a), vec![a, b]);

        assert!(egraph.assert_equal(a, c).conflict.is_none());
        assert_eq!(class_members(&egraph, a), vec![a, c, b]);

        let events = egraph.drain_all_merges();
        assert_eq!(events.len(), 2);
        assert_eq!(
            egraph.collect_member_range(events[0].survivor_members),
            vec![a]
        );
        assert_eq!(
            egraph.collect_member_range(events[0].demoted_members),
            vec![b]
        );
        assert_eq!(
            egraph.collect_member_range(events[1].survivor_members),
            vec![b, a]
        );
        assert_eq!(
            egraph.collect_member_range(events[1].demoted_members),
            vec![c]
        );
        assert_eq!(events[0].level, 1);
        assert_eq!(events[1].level, 1);

        egraph.backtrack_to(0);
        assert_eq!(class_members(&egraph, a), vec![a]);
        assert_eq!(class_members(&egraph, b), vec![b]);
        assert_eq!(class_members(&egraph, c), vec![c]);

        egraph.notify_new_decision_level();
        assert!(egraph.assert_equal(a, b).conflict.is_none());
        egraph.backtrack_to(0);
        assert!(egraph.drain_all_merges().is_empty());
    }

    #[test]
    fn relevant_match_candidates_are_incremental_and_backtrackable() {
        let mut egraph = Egraph::new();
        let a = egraph.register_constant(Op::Constant("a".to_owned()));
        let b = egraph.register_constant(Op::Constant("b".to_owned()));
        let fa = egraph.register_term(Op::App("f".to_owned()), &[a], false);
        let fb = egraph.register_term(Op::App("f".to_owned()), &[b], false);
        let fa_pattern = egraph.compile_pattern(Pattern::App(
            Op::App("f".to_owned()),
            vec![Pattern::Ground(a)],
        ));
        let fb_pattern = egraph.compile_pattern(Pattern::App(
            Op::App("f".to_owned()),
            vec![Pattern::Ground(b)],
        ));

        egraph.notify_new_decision_level();
        egraph.mark_e_matching_term_relevant(fa, 1);

        assert_eq!(egraph.match_triggers(&[(fa_pattern, None)], true).len(), 1);
        assert!(
            egraph
                .match_triggers(&[(fb_pattern, None)], true)
                .is_empty()
        );
        assert_eq!(egraph.match_triggers(&[(fb_pattern, None)], false).len(), 1);

        egraph.mark_e_matching_term_relevant(fb, 1);
        assert_eq!(egraph.match_triggers(&[(fb_pattern, None)], true).len(), 1);

        egraph.backtrack_to(0);
        assert!(
            egraph
                .match_triggers(&[(fa_pattern, None)], true)
                .is_empty()
        );
        assert!(
            egraph
                .match_triggers(&[(fb_pattern, None)], true)
                .is_empty()
        );

        egraph.notify_new_decision_level();
        egraph.mark_e_matching_term_relevant(fb, 1);
        egraph.mark_e_matching_term_relevant(fb, 0);
        egraph.backtrack_to(0);
        assert_eq!(egraph.match_triggers(&[(fb_pattern, None)], true).len(), 1);
    }

    #[test]
    fn retirement_removes_complete_dead_subgraphs_and_reuses_ids() {
        let mut egraph = Egraph::new();
        let a = egraph.register_constant(Op::Constant("a".to_owned()));
        let fa = egraph.register_term(Op::App("f".to_owned()), &[a], false);
        let gfa = egraph.register_term(Op::App("g".to_owned()), &[fa], false);
        egraph.backtrack_to(0);

        let report = egraph.retire_terms(&DeterministicHashSet::from_iter([fa]));
        assert!(report.retired_ids.is_empty());
        assert_eq!(report.blocked_live_parent_terms, 1);

        let report = egraph.retire_terms(&DeterministicHashSet::from_iter([fa, gfa]));
        assert_eq!(report.retired_ids, vec![fa, gfa]);
        assert_eq!(egraph.gc_profile().registered_terms, 1);
        assert_eq!(egraph.gc_profile().function_entries, 1);
        assert_eq!(egraph.gc_profile().reusable_ids, 2);

        let ha = egraph.register_term(Op::App("h".to_owned()), &[a], false);
        assert_eq!(ha, gfa);
        assert_eq!(egraph.gc_profile().reusable_ids, 1);
    }

    #[test]
    fn retirement_removes_complete_merged_classes_atomically() {
        let mut egraph = Egraph::new();
        let a = egraph.register_term(Op::App("a".to_owned()), &[], false);
        let b = egraph.register_term(Op::App("b".to_owned()), &[], false);
        assert!(egraph.assert_equal(a, b).conflict.is_none());
        assert_eq!(egraph.find(a), egraph.find(b));
        egraph.backtrack_to(0);

        let report = egraph.retire_terms(&DeterministicHashSet::from_iter([a, b]));
        assert_eq!(report.candidate_classes, 1);
        assert_eq!(report.fully_candidate_classes, 1);
        assert_eq!(report.retired_classes, 1);
        assert_eq!(report.retired_ids, vec![a, b]);
        assert_eq!(egraph.gc_profile().registered_terms, 0);
    }

    #[test]
    fn retirement_prunes_dead_leaf_from_a_live_merged_class() {
        let mut egraph = Egraph::new();
        let a = egraph.register_term(Op::App("a".to_owned()), &[], false);
        let b = egraph.register_term(Op::App("b".to_owned()), &[], false);
        assert!(egraph.assert_equal(a, b).conflict.is_none());
        egraph.backtrack_to(0);

        let root = egraph.find(a);
        let leaf = if root == a { b } else { a };
        let report = egraph.retire_terms(&DeterministicHashSet::from_iter([root]));
        assert!(report.retired_ids.is_empty());
        assert_eq!(report.candidate_classes, 1);
        assert_eq!(report.fully_candidate_classes, 0);
        assert_eq!(report.blocked_mixed_class_roots, 1);
        assert_eq!(egraph.gc_profile().registered_terms, 2);

        let report = egraph.retire_terms(&DeterministicHashSet::from_iter([leaf]));
        assert_eq!(report.retired_ids, vec![leaf]);
        assert_eq!(report.pruned_mixed_classes, 1);
        assert_eq!(report.pruned_mixed_class_terms, 1);
        assert_eq!(egraph.class_members(root), vec![root]);
        assert_eq!(egraph.gc_profile().registered_terms, 1);
    }

    #[test]
    fn retirement_propagates_parent_closure_across_merged_classes() {
        let mut egraph = Egraph::new();
        let a = egraph.register_term(Op::App("a".to_owned()), &[], false);
        let b = egraph.register_term(Op::App("b".to_owned()), &[], false);
        let fa = egraph.register_term(Op::App("f".to_owned()), &[a], false);
        let fb = egraph.register_term(Op::App("g".to_owned()), &[b], false);
        assert!(egraph.assert_equal(a, b).conflict.is_none());
        assert!(egraph.assert_equal(fa, fb).conflict.is_none());
        egraph.backtrack_to(0);

        let report = egraph.retire_terms(&DeterministicHashSet::from_iter([a, b]));
        assert!(report.retired_ids.is_empty());
        assert_eq!(report.blocked_live_parent_terms, 2);

        let report = egraph.retire_terms(&DeterministicHashSet::from_iter([a, b, fa, fb]));
        assert_eq!(report.retired_classes, 2);
        assert_eq!(report.retired_ids, vec![a, b, fa, fb]);
    }

    #[test]
    fn retirement_compacts_backtracked_predecessor_copies() {
        let mut egraph = Egraph::new();
        let x = egraph.register_term(Op::App("x".to_owned()), &[], false);
        let y = egraph.register_term(Op::App("y".to_owned()), &[], false);
        let fx = egraph.register_term(Op::App("f".to_owned()), &[x], false);
        let fy = egraph.register_term(Op::App("f".to_owned()), &[y], false);
        let baseline = egraph.gc_profile().predecessor_entries;
        assert_eq!(baseline, 2);

        egraph.notify_new_decision_level();
        assert!(egraph.assert_equal(x, y).conflict.is_none());
        assert_eq!(egraph.find(fx), egraph.find(fy));
        egraph.backtrack_to(0);
        assert_ne!(egraph.find(fx), egraph.find(fy));

        let grown = egraph.gc_profile().predecessor_entries;
        assert!(grown > baseline);
        let report = egraph.retire_terms(&DeterministicHashSet::default());
        assert_eq!(report.predecessor_entries_before, grown);
        assert_eq!(report.predecessor_entries_after_compaction, baseline);
        assert_eq!(report.predecessor_entries_after_retirement, baseline);

        // Reconstructed root edges must still trigger congruence on the next
        // branch; compaction changes storage, not equality behavior.
        egraph.notify_new_decision_level();
        assert!(egraph.assert_equal(x, y).conflict.is_none());
        assert_eq!(egraph.find(fx), egraph.find(fy));
    }

    #[test]
    fn incremental_predecessor_gc_reclaims_backtracked_copies() {
        let mut egraph = Egraph::new();
        let x = egraph.register_term(Op::App("x".to_owned()), &[], false);
        let y = egraph.register_term(Op::App("y".to_owned()), &[], false);
        let fx = egraph.register_term(Op::App("f".to_owned()), &[x], false);
        let fy = egraph.register_term(Op::App("f".to_owned()), &[y], false);
        let baseline = egraph.gc_profile().predecessor_entries;

        egraph.notify_new_decision_level();
        assert!(egraph.assert_equal(x, y).conflict.is_none());
        assert_eq!(egraph.find(fx), egraph.find(fy));
        egraph.backtrack_to(0);
        assert!(egraph.gc_profile().predecessor_entries > baseline);

        let report = egraph.collect_backtracked_predecessors();
        assert!(report.examined_mutations > 0);
        assert!(report.removed_entries + report.restored_entries > 0);
        assert_eq!(egraph.gc_profile().predecessor_entries, baseline);

        egraph.notify_new_decision_level();
        assert!(egraph.assert_equal(x, y).conflict.is_none());
        assert_eq!(egraph.find(fx), egraph.find(fy));
    }

    #[test]
    fn retirement_keeps_terms_referenced_by_compiled_patterns() {
        let mut egraph = Egraph::new();
        let a = egraph.register_constant(Op::Constant("a".to_owned()));
        let _ = egraph.compile_pattern(Pattern::Ground(a));

        let report = egraph.retire_terms(&DeterministicHashSet::from_iter([a]));
        assert!(report.retired_ids.is_empty());
        assert_eq!(report.blocked_pattern_terms, 1);
    }

    #[test]
    fn retirement_keeps_terms_with_compiled_trigger_heads() {
        let mut egraph = Egraph::new();
        let fa = egraph.register_term(Op::App("f".to_owned()), &[], false);
        let _ = egraph.compile_pattern(Pattern::App(Op::App("f".to_owned()), vec![]));
        egraph.backtrack_to(0);

        let report = egraph.retire_terms(&DeterministicHashSet::from_iter([fa]));
        assert!(report.retired_ids.is_empty());
        assert_eq!(report.blocked_trigger_head_terms, 1);
        assert_eq!(egraph.gc_profile().registered_terms, 1);
    }
}

/// Checks if the hash is still valid at the given level
fn valid_hash(hash: u32, level: usize, predecessor_level: &[u32]) -> bool {
    debug_println!(
        5,
        0,
        "We are in valid_hash with hash {} and level {}",
        hash,
        level
    );
    hash >= predecessor_level[level] || level == 0
}

impl EgraphTrait for Egraph {
    type Op = Op;
    type TermId = u32;

    fn register_term(
        &mut self,
        op: Self::Op,
        children: &[Self::TermId],
        dynamic: bool,
    ) -> Self::TermId {
        let id = self.allocate_id();
        self.register_term_internal(id, op, children, dynamic);
        id
    }

    fn register_constant(&mut self, op: Self::Op) -> Self::TermId {
        // TODO: currently relies on Op::Constant variant to distinguish constants
        // from other 0-arity terms. If Op is unified in the future, this method
        // should mark the term as a constant via a separate mechanism.
        let id = self.allocate_id();
        self.register_term_internal(id, op, &[], false);
        id
    }

    fn register_opaque(&mut self) -> Self::TermId {
        self.register_opaque_term()
    }

    fn compile_pattern(&mut self, pattern: Pattern) -> PatternId {
        let id = self.compiled_patterns.len();
        self.compiled_patterns.push(pattern);
        id
    }

    fn register_eq(&mut self, _t1: Self::TermId, _t2: Self::TermId, _lit: Lit) {
        // TODO: watch-based equality propagation (future optimization)
    }

    fn register_boolean_term(
        &mut self,
        op: Self::Op,
        children: &[Self::TermId],
        _lit: Lit,
    ) -> Self::TermId {
        self.register_term(op, children, false)
    }

    fn mark_arithmetic(&mut self, term: Self::TermId) {
        let root = self.find(term);
        match &mut self.proof_forest[root as usize] {
            ProofForestEdge::Root { arithmetic, .. } => {
                *arithmetic = true;
            }
            _ => panic!(
                "mark_arithmetic: find({}) returned a non-root node",
                self.display_term(term)
            ),
        }
    }

    fn incremental_arithmetic(&mut self, enabled: bool) {
        self.incremental_arithmetic = enabled;
        if !enabled {
            self.arithmetic_merge_queue.clear();
        }
    }

    fn drain_arithmetic_equalities(&mut self) -> Vec<(Self::TermId, Self::TermId)> {
        std::mem::take(&mut self.arithmetic_merge_queue)
    }

    fn set_track_all_merges(&mut self, enabled: bool) {
        self.track_all_merges = enabled;
        if !enabled {
            self.relevancy_merge_queue.clear();
        }
    }

    fn drain_all_merges(&mut self) -> Vec<EgraphMergeEvent<Self::TermId>> {
        std::mem::take(&mut self.relevancy_merge_queue)
    }

    fn notify_new_decision_level(&mut self) {
        assert!(
            self.arithmetic_merge_queue.is_empty(),
            "arithmetic queue must be drained before advancing decision level"
        );
        self.decision_level += 1;
        while self.decision_level >= self.predecessor_level.len() {
            self.predecessor_level
                .resize(self.predecessor_level.len() * 2, 0);
        }
        while self.decision_level >= self.predecessor_trail.len() {
            self.predecessor_trail.push(Vec::new());
        }
        self.predecessor_level[self.decision_level] = self.predecessor_hash;
    }

    fn assert_equal(&mut self, t1: Self::TermId, t2: Self::TermId) -> EgraphResult<Self::TermId> {
        self.assert_equal(t1, t2)
    }

    fn assert_disequal(
        &mut self,
        t1: Self::TermId,
        t2: Self::TermId,
        lit: Lit,
    ) -> EgraphResult<Self::TermId> {
        self.assert_disequal(t1, t2, lit)
    }

    fn assert_distinct(&mut self, terms: &[Self::TermId], lit: Lit) -> EgraphResult<Self::TermId> {
        self.assert_distinct(terms, lit)
    }

    fn find(&self, term: Self::TermId) -> Self::TermId {
        self.find(term)
    }

    fn are_equal(&self, t1: Self::TermId, t2: Self::TermId) -> bool {
        self.find(t1) == self.find(t2)
    }

    fn class_member_range(&self, term: Self::TermId) -> EClassMemberRange<Self::TermId> {
        self.member_range_for_root(self.find(term))
    }

    fn next_class_member(&self, term: Self::TermId) -> Self::TermId {
        self.member_next[term as usize]
    }

    fn mark_e_matching_term_relevant(&mut self, term: Self::TermId, level: usize) {
        self.mark_match_term_relevant(term, level);
    }

    fn match_triggers(
        &self,
        trigger_term_pairs: &[(PatternId, Option<Self::TermId>)],
        relevant_only: bool,
    ) -> Vec<DeterministicHashMap<Local, u32>> {
        self.e_match_calls.set(self.e_match_calls.get() + 1);
        let mut assignment = DeterministicHashMap::default();
        let results = self.match_patterns(&mut assignment, trigger_term_pairs, relevant_only);
        self.e_match_results
            .set(self.e_match_results.get() + results.len() as u64);
        results
    }

    fn backtrack_to(&mut self, level: usize) {
        self.backtrack_to(level)
    }

    fn make_decision(&self, _assignments: &[i32]) -> i32 {
        0
    }

    fn make_decision_lit(&self, _lit: Lit, _assignments: &[i32]) -> Lit {
        0
    }

    fn explain_equality(
        &self,
        t1: Self::TermId,
        t2: Self::TermId,
    ) -> Option<Vec<(Self::TermId, Self::TermId)>> {
        self.leastcommonancestor(t1, t2)
    }
}
