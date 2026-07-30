// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use super::datastructures::{CanonicalOp, DisequalTerm, Predecessor};
use super::proofforest::*;
use super::repr::{Children, Op, Pattern, PatternId, TermEntry, TermSlot};
use crate::debug_println;
use crate::egraphs::traits::{Conflict, EgraphResult, EgraphTrait, Lit};
use crate::log::is_important;
use crate::utils::{
    DeterministicHashMap, DeterministicHashSet, FastDeterministicHashMap, FastDeterministicHashSet,
};
use std::default::Default;
use std::fmt;
use yaspar_ir::ast::Local;

/// Key for the signature table: (operator, canonical children).
type SigKey = (CanonicalOp, Children);

/// A complete repair pass is worthwhile only when incremental work is dense.
const FULL_REBUILD_MIN_TERMS: usize = 1024;

/// A Boolean value attached to an e-class and its SAT witness. Constants use zero.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct BoolClassAssignment<T> {
    term: T,
    lit: Lit,
    value: bool,
    bool_constant: T,
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
    /// Internal term representation per term ID
    terms: Vec<TermSlot>,
    /// Compiled patterns for e-matching (indexed by PatternId)
    compiled_patterns: Vec<Pattern>,
    /// map from vertices (u32) -> ProofForestEdge
    proof_forest: Vec<ProofForestEdge>,
    /// keeps track of a stack of "edges" to backtrack on
    proof_forest_backtrack_stack: Vec<(usize, ProofForestEdge, u32, ProofForestEdge)>,
    /// this is a map from terms (u32) -> (term in the same egraph, predecessor of term in same egraph)
    predecessors: Vec<FastDeterministicHashMap<u32, Predecessor>>,
    /// number to keep track of the current hash
    predecessor_hash: u32,
    /// mapping from levels -> corresponding hash
    predecessor_level: Vec<u32>,
    /// map from functions (String) -> terms of this function
    function_maps: DeterministicHashMap<String, Vec<(u32, Vec<u32>)>>,
    /// the current decision level of the SAT solver, useful to keep track for backtracking
    decision_level: usize,
    /// keeps track of terms created by quantifier instantiation and their predecessors.
    /// Inner map: parent term id -> decision level at which the (child, parent) pair
    /// was registered. Used by `backtrack_to` to skip re-registering entries that
    /// were added at or below the target level (their predecessors are already
    /// valid at that level and don't need refreshing).
    predecessors_created_by_quantifiers:
        DeterministicHashMap<u32, DeterministicHashMap<u32, usize>>,
    /// Signature table for the last completed rebuild.
    sig_table: FastDeterministicHashMap<SigKey, u32>,
    /// Backtrack trail for signature-table mutations.
    sig_table_trail: Vec<(usize, SigKey, Option<u32>)>,
    /// Last rebuilt signature for each term.
    term_signatures: Vec<Option<SigKey>>,
    /// All terms that participate in congruence, in registration order.
    congruence_terms: Vec<u32>,
    /// Backtrack trail for per-term signature-cache mutations.
    term_signature_trail: Vec<(usize, u32, Option<SigKey>)>,
    /// Terms whose canonical signatures may have changed.
    pending_congruence: Vec<u32>,
    /// Dense membership flags for `pending_congruence`.
    pending_congruence_flags: Vec<bool>,
    /// Whether `pending_congruence` was expanded into a complete repair pass.
    full_congruence_rebuild_active: bool,
    /// Congruence-capable terms registered above level zero. Terms persist
    /// after SAT backtracking, so their cache entries must be rebuilt at the
    /// restored level.
    congruence_registrations: Vec<(usize, u32)>,
    /// Whether to collect arithmetic-relevant merges for an incremental
    /// arithmetic backend.
    incremental_arithmetic: bool,
    /// Pre-merge (surviving_root, demoted_root) pairs from direct or
    /// congruence-derived unions where either root was arithmetic-tagged.
    /// The incremental backend drains this to propagate equalities to Z3.
    arithmetic_merge_queue: Vec<(u32, u32)>,
    /// Whether each term should be merged with true/false on SAT assignment.
    merge_tf: Vec<bool>,
    /// A marked-term witness for each root whose class contains a `merge_tf` term.
    merge_tf_class: Vec<Option<u32>>,
    /// Root-class updates introduced by backtrackable unions.
    merge_tf_class_trail: Vec<(usize, u32, Option<u32>)>,
    /// Nonzero-level upgrades that persist and need relocation after backtrack.
    merge_tf_upgrades: Vec<(usize, u32)>,
    /// Deferred `(term, bool_constant)` merges from APIs that return only a
    /// term ID. Keyed on the pair so re-queuing the same merge dedups for free;
    /// the value is the decision level at which it was queued (for backtracking).
    pending_merges: DeterministicHashMap<(u32, u32), usize>,
    /// Boolean value and its SAT witness, stored only on e-class roots.
    bool_assignments: Vec<Option<BoolClassAssignment<u32>>>,
    /// Root-assignment changes to undo on SAT backtracking.
    bool_assignment_trail: Vec<(usize, u32)>,
    /// Accumulated egraph statistics.
    pub(crate) stats: EgraphStats,
}

/// Statistics accumulated by the egraph.
#[derive(Debug, Default, Clone)]
pub(crate) struct EgraphStats {
    /// Number of successful equality merges (where roots differed).
    pub(crate) merges: u64,
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
            terms: vec![TermSlot::Empty],
            compiled_patterns: Vec::new(),
            proof_forest: vec![ProofForestEdge::Root {
                size: 1000,
                child: 0,
                disequalities: DeterministicHashMap::new(),
                children: DeterministicHashSet::new(),
                arithmetic: false,
            }],
            proof_forest_backtrack_stack: Vec::new(),
            predecessors: vec![FastDeterministicHashMap::default()],
            predecessor_hash: 1,
            predecessor_level: vec![1, 1],
            function_maps: DeterministicHashMap::default(),
            decision_level: 0,
            predecessors_created_by_quantifiers: DeterministicHashMap::new(),
            sig_table: FastDeterministicHashMap::default(),
            sig_table_trail: Vec::new(),
            term_signatures: vec![None],
            congruence_terms: Vec::new(),
            term_signature_trail: Vec::new(),
            pending_congruence: Vec::new(),
            pending_congruence_flags: vec![false],
            full_congruence_rebuild_active: false,
            congruence_registrations: Vec::new(),
            incremental_arithmetic: false,
            arithmetic_merge_queue: Vec::new(),
            merge_tf: vec![false],
            merge_tf_class: vec![None],
            merge_tf_class_trail: Vec::new(),
            merge_tf_upgrades: Vec::new(),
            pending_merges: DeterministicHashMap::new(),
            bool_assignments: vec![None],
            bool_assignment_trail: Vec::new(),
            stats: EgraphStats::default(),
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
    /// Congruence is deferred until `rebuild`.
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

                self.predecessors[root as usize]
                    .entry(id)
                    .or_insert(root_predecessor);
            }
        }

        if matches!(op, Op::App(_) | Op::Eq | Op::Ite) {
            self.congruence_terms.push(id);
            if self.decision_level > 0 {
                self.congruence_registrations
                    .push((self.decision_level, id));
            }
            self.enqueue_congruence(id);
        }

        false
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
            self.merge_tf.resize(self.merge_tf.len() * 2, false);
            self.merge_tf_class
                .resize(self.merge_tf_class.len() * 2, None);
            self.bool_assignments
                .resize(self.bool_assignments.len() * 2, None);
            self.term_signatures
                .resize(self.term_signatures.len() * 2, None);
            self.pending_congruence_flags
                .resize(self.pending_congruence_flags.len() * 2, false);
        }
    }

    /// Register an opaque term — allocates a full slot with a proof_forest Root
    /// but no op/children/function_maps/predecessors. Used for quantifier terms
    /// that participate in union-find (merged with true/false) but not congruence.
    fn register_opaque_term(&mut self) -> u32 {
        let id = self.next_id;
        self.next_id += 1;
        self.ensure_capacity(id);
        self.terms[id as usize] = TermSlot::Opaque;
        self.proof_forest[id as usize] = ProofForestEdge::Root {
            size: 1,
            disequalities: DeterministicHashMap::new(),
            child: 0,
            children: DeterministicHashSet::new(),
            arithmetic: false,
        };
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

    fn enqueue_congruence(&mut self, term: u32) {
        let participates = matches!(
            &self.terms[term as usize],
            TermSlot::Term(TermEntry {
                op: Op::App(_) | Op::Eq | Op::Ite,
                ..
            })
        );
        if participates && !self.pending_congruence_flags[term as usize] {
            self.pending_congruence_flags[term as usize] = true;
            self.pending_congruence.push(term);
        }
    }

    fn clear_pending_congruence(&mut self) {
        for term in self.pending_congruence.drain(..) {
            self.pending_congruence_flags[term as usize] = false;
        }
        self.full_congruence_rebuild_active = false;
    }

    fn maybe_schedule_full_congruence_rebuild(&mut self) {
        let total = self.congruence_terms.len();
        if self.full_congruence_rebuild_active
            || total < FULL_REBUILD_MIN_TERMS
            || self.pending_congruence.len().saturating_mul(2) < total
        {
            return;
        }
        if self.pending_congruence.len() == total {
            self.full_congruence_rebuild_active = true;
            return;
        }

        self.clear_pending_congruence();
        for &term in &self.congruence_terms {
            self.pending_congruence_flags[term as usize] = true;
            self.pending_congruence.push(term);
        }
        self.full_congruence_rebuild_active = true;
    }

    fn set_sig_table_entry(&mut self, key: SigKey, value: Option<u32>) {
        let previous = self.sig_table.get(&key).copied();
        if previous == value {
            return;
        }
        if self.decision_level > 0 {
            self.sig_table_trail
                .push((self.decision_level, key.clone(), previous));
        }
        if let Some(term) = value {
            self.sig_table.insert(key, term);
        } else {
            self.sig_table.remove(&key);
        }
    }

    fn set_term_signature(&mut self, term: u32, signature: Option<SigKey>) {
        if self.term_signatures[term as usize] == signature {
            return;
        }
        if self.decision_level > 0 {
            self.term_signature_trail.push((
                self.decision_level,
                term,
                self.term_signatures[term as usize].clone(),
            ));
        }
        self.term_signatures[term as usize] = signature;
    }

    /// Repair one canonical signature and merge a collision, if any.
    fn rebuild_congruence(&mut self, term: u32) -> EgraphResult<u32> {
        let Some(signature) = self.compute_signature(term) else {
            self.set_term_signature(term, None);
            return EgraphResult::ok();
        };

        if self.term_signatures[term as usize].as_ref() == Some(&signature)
            && self.sig_table.get(&signature) == Some(&term)
        {
            return EgraphResult::ok();
        }

        if let Some(old_signature) = self.term_signatures[term as usize].clone()
            && self.sig_table.get(&old_signature) == Some(&term)
        {
            self.set_sig_table_entry(old_signature, None);
        }
        self.set_term_signature(term, None);

        loop {
            let Some(existing) = self.sig_table.get(&signature).copied() else {
                self.set_sig_table_entry(signature.clone(), Some(term));
                self.set_term_signature(term, Some(signature));
                return EgraphResult::ok();
            };

            if existing == term {
                self.set_term_signature(term, Some(signature));
                return EgraphResult::ok();
            }

            if self.compute_signature(existing).as_ref() != Some(&signature) {
                self.set_sig_table_entry(signature.clone(), None);
                self.enqueue_congruence(existing);
                continue;
            }

            self.set_term_signature(existing, Some(signature.clone()));
            self.set_term_signature(term, Some(signature));
            if self.find(existing) == self.find(term) {
                return EgraphResult::ok();
            }
            return self.congruence_merge(existing, term, self.decision_level);
        }
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

        use std::collections::hash_map::Entry;
        match self.predecessors[term as usize].entry(new_pred_key) {
            Entry::Vacant(slot) => {
                slot.insert(new_pred);
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
                    slot.insert(new_pred);
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
        let mut expanded_pairs = FastDeterministicHashSet::default();
        let mut seen_equalities = FastDeterministicHashSet::default();
        let mut equalities = Vec::new();
        self.leastcommonancestor_helper(
            u,
            v,
            0,
            &mut expanded_pairs,
            &mut seen_equalities,
            &mut equalities,
        )?;
        Some(equalities)
    }

    fn leastcommonancestor_helper(
        &self,
        u: u32,
        v: u32,
        indent: usize,
        expanded_pairs: &mut FastDeterministicHashSet<(u32, u32)>,
        seen_equalities: &mut FastDeterministicHashSet<(u32, u32)>,
        final_proof: &mut Vec<(u32, u32)>,
    ) -> Option<()> {
        debug_println!(
            20,
            indent,
            "checking the equality of {} and {}",
            self.display_term(u),
            self.display_term(v)
        );
        if u == v {
            return Some(());
        }
        let pair = if u < v { (u, v) } else { (v, u) };
        if !expanded_pairs.insert(pair) {
            return Some(());
        }

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
                expanded_pairs.remove(&pair);
                return None;
            }
            path_from_v.push(curr);
            curr = self.proof_forest[curr as usize].get_parent();
        }
        let lca = curr;

        assert!(visited.contains(&curr));

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
                        let equality = if t1 < t2 { (t1, t2) } else { (t2, t1) };
                        if seen_equalities.insert(equality) {
                            final_proof.push((t1, t2));
                        }
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
                let _ = self.leastcommonancestor_helper(
                    a,
                    b,
                    indent + 1,
                    expanded_pairs,
                    seen_equalities,
                    final_proof,
                );
            }
        }
        Some(())
    }

    /// Assert t1 = t2 at the current decision level.
    /// Congruence consequences are deferred until `rebuild`.
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
                bool_lits: None,
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

    fn assign_bool_value(
        &mut self,
        term: u32,
        lit: Lit,
        value: bool,
        bool_constant: u32,
    ) -> EgraphResult<u32> {
        let root = self.find(term);
        let assignment = BoolClassAssignment {
            term,
            lit,
            value,
            bool_constant,
        };
        let result = match self.bool_assignments[root as usize] {
            None => {
                self.bool_assignment_trail.push((self.decision_level, root));
                self.bool_assignments[root as usize] = Some(assignment);
                EgraphResult::ok()
            }
            Some(existing) if existing.value != value => {
                let equalities = self
                    .leastcommonancestor(existing.term, term)
                    .expect("Boolean assignment witnesses must share an e-class");
                EgraphResult::with_conflict(Conflict {
                    equalities,
                    disequality: (existing.term, term),
                    diseq_lit: None,
                    bool_lits: Some([existing.lit, assignment.lit]),
                })
            }
            Some(_) => EgraphResult::ok(),
        };
        if result.conflict.is_none() {
            self.queue_merge_tf_assignment(root, self.decision_level);
        }
        result
    }

    fn queue_merge_tf_assignment(&mut self, root: u32, level: usize) {
        if self.merge_tf_class[root as usize].is_none() || self.is_constant(root) {
            return;
        }
        let Some(assignment) = self.bool_assignments[root as usize] else {
            return;
        };
        if assignment.lit == 0 {
            return;
        }
        // Keying on the pair dedups re-queues of the same merge automatically.
        self.pending_merges
            .entry((assignment.term, assignment.bool_constant))
            .or_insert(level);
    }

    fn set_merge_tf_class_witness(&mut self, root: u32, witness: u32, level: usize) {
        if self.merge_tf_class[root as usize].is_some() {
            return;
        }
        if level > 0 {
            self.merge_tf_class_trail
                .push((level, root, self.merge_tf_class[root as usize]));
        }
        self.merge_tf_class[root as usize] = Some(witness);
    }

    fn should_merge_tf(&self, term: u32) -> bool {
        self.merge_tf_class[self.find(term) as usize].is_some()
    }

    /// Transfer the demoted root's Boolean value to the surviving root. Both
    /// roots have already been checked for an opposite-value conflict.
    fn merge_bool_assignments(&mut self, surviving_root: u32, demoted_root: u32, level: usize) {
        let surviving = self.bool_assignments[surviving_root as usize];
        let demoted = self.bool_assignments[demoted_root as usize];
        match (surviving, demoted) {
            (None, Some(assignment)) => {
                self.bool_assignment_trail.push((level, surviving_root));
                self.bool_assignments[surviving_root as usize] = Some(assignment);
            }
            (Some(first), Some(second)) => {
                debug_assert_eq!(first.value, second.value);
                debug_assert_eq!(first.bool_constant, second.bool_constant);
            }
            _ => {}
        }
        self.queue_merge_tf_assignment(surviving_root, level);
    }

    /// Explain the equality that would be introduced by a pending union,
    /// without mutating the proof forest.
    fn explain_pending_union(
        &self,
        left_witness: u32,
        x: u32,
        right_witness: u32,
        y: u32,
        proof_parent: &ProofForestEdge,
    ) -> Vec<(u32, u32)> {
        let mut equalities = Vec::new();
        if left_witness != x {
            equalities.extend(
                self.leastcommonancestor(left_witness, x)
                    .expect("left witness must be in x's class"),
            );
        }
        match proof_parent {
            ProofForestEdge::Equality {
                term: Some((t1, t2)),
                ..
            } => equalities.push((*t1, *t2)),
            ProofForestEdge::Congruence { pairs, .. } => {
                for &(a, b) in pairs {
                    equalities.extend(
                        self.leastcommonancestor(a, b)
                            .expect("congruence children must already be equal"),
                    );
                }
            }
            _ => {}
        }
        if right_witness != y {
            equalities.extend(
                self.leastcommonancestor(right_witness, y)
                    .expect("right witness must be in y's class"),
            );
        }
        equalities
    }

    /// Undo all egraph operations at levels strictly greater than `level`.
    fn backtrack_to(&mut self, level: usize) {
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
            let (_, backtrack_equality, y, y_root) =
                self.proof_forest_backtrack_stack.pop().unwrap();
            self.proof_forest_backtrack(backtrack_equality, y, y_root);
        }

        while let Some((entry_level, _, _)) = self.merge_tf_class_trail.last() {
            if *entry_level <= level {
                break;
            }
            let (_, root, previous) = self.merge_tf_class_trail.pop().unwrap();
            self.merge_tf_class[root as usize] = previous;
        }

        while let Some((entry_level, _)) = self.bool_assignment_trail.last() {
            if *entry_level <= level {
                break;
            }
            let (_, root) = self.bool_assignment_trail.pop().unwrap();
            self.bool_assignments[root as usize] = None;
        }
        self.pending_merges
            .retain(|_, entry_level| *entry_level <= level);
        let mut relocated_upgrades = Vec::new();
        for (upgrade_level, term) in &mut self.merge_tf_upgrades {
            if *upgrade_level > level {
                *upgrade_level = level;
                relocated_upgrades.push(*term);
            }
        }
        let mut relocated_roots = FastDeterministicHashSet::default();
        for term in relocated_upgrades {
            let root = self.find(term);
            self.set_merge_tf_class_witness(root, term, level);
            relocated_roots.insert(root);
        }
        for root in relocated_roots {
            self.queue_merge_tf_assignment(root, level);
        }

        if level == 0 {
            self.merge_tf_class_trail.clear();
            self.merge_tf_upgrades.clear();
        }

        while let Some((entry_level, _, _)) = self.sig_table_trail.last() {
            if *entry_level <= level {
                break;
            }
            let (_, key, previous) = self.sig_table_trail.pop().unwrap();
            if let Some(term) = previous {
                self.sig_table.insert(key, term);
            } else {
                self.sig_table.remove(&key);
            }
        }

        while let Some((entry_level, _, _)) = self.term_signature_trail.last() {
            if *entry_level <= level {
                break;
            }
            let (_, term, previous) = self.term_signature_trail.pop().unwrap();
            self.term_signatures[term as usize] = previous;
        }

        // Pending work belongs to the abandoned suffix of the SAT trail. The
        // target level was fully rebuilt before the solver advanced past it.
        self.clear_pending_congruence();

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
                self.predecessors[current_ancestor as usize].insert(*parent, predecessor);
            }
        }

        let mut relocated_registrations = Vec::new();
        for (registered_at, term) in &mut self.congruence_registrations {
            if *registered_at > level {
                *registered_at = level;
                relocated_registrations.push(*term);
            }
        }
        for term in relocated_registrations {
            self.enqueue_congruence(term);
        }

        // Merges queued for arithmetic above the target level are stale.
        self.arithmetic_merge_queue.clear();

        // Clear at level 0
        if level == 0 {
            self.predecessors_created_by_quantifiers = DeterministicHashMap::new();
            self.proof_forest_backtrack_stack = vec![];
            self.bool_assignment_trail.clear();
            self.sig_table_trail.clear();
            self.term_signature_trail.clear();
            self.congruence_registrations.clear();
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
            match &proof_parent {
                ProofForestEdge::Equality {
                    term: Some((t1, t2)),
                    ..
                } => equalities.push((*t1, *t2)),
                ProofForestEdge::Congruence { pairs, .. } => {
                    for &(a, b) in pairs {
                        if let Some(path) = self.leastcommonancestor(a, b) {
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
                bool_lits: None,
            });
        }

        if let (Some(first), Some(second)) = (
            self.bool_assignments[x_root as usize],
            self.bool_assignments[y_root as usize],
        ) && first.value != second.value
        {
            let equalities =
                self.explain_pending_union(first.term, x, second.term, y, &proof_parent);
            return EgraphResult::with_conflict(Conflict {
                equalities,
                disequality: (first.term, second.term),
                diseq_lit: None,
                bool_lits: Some([first.lit, second.lit]),
            });
        }

        self.stats.merges += 1;

        // Ensure the constant (if any) remains the root: make the constant
        // side "x" so that x_root stays as root after the union.
        let (x, y, x_root, y_root, surviving_root_is_const) = if y_root_is_const {
            (y, x, y_root, x_root, true)
        } else {
            (x, y, x_root, y_root, x_root_is_const)
        };

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

        if let Some(witness) = self.merge_tf_class[y_root as usize] {
            self.set_merge_tf_class_witness(x_root, witness, level);
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
            ));
        }

        // Perform the union first so we can check for disequality violations early.
        debug_println!(
            16,
            2,
            "Making {} the root of its equivalence class [previously was {}]",
            self.display_term(y),
            self.display_term(y_root)
        );
        self.make_root(y, proof_parent);
        self.merge_bool_assignments(x_root, y_root, level);

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
                    bool_lits: None,
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

        // Move predecessors from the demoted root to the surviving root and
        // defer all induced congruence reasoning until rebuild.
        let predecessors_v = std::mem::take(&mut self.predecessors[y_root as usize]);
        for (pred_key, pred_val) in &predecessors_v {
            let new_pred = Predecessor {
                level,
                hash: self.predecessor_hash,
                predecessor: *pred_key,
                inner_term: pred_val.inner_term,
            };
            self.add_predecessor(x_root, *pred_key, new_pred);
            if valid_hash(pred_val.hash, pred_val.level, &self.predecessor_level) {
                self.enqueue_congruence(*pred_key);
            }
        }
        self.predecessors[y_root as usize] = predecessors_v;

        debug_assert!(
            !surviving_root_is_const || self.find(x_root) == x_root,
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
        &mut self,
        assignment: &mut DeterministicHashMap<Local, u32>,
        pattern_term_pairs: &[(PatternId, Option<u32>)],
    ) -> Vec<DeterministicHashMap<Local, u32>> {
        if pattern_term_pairs.is_empty() {
            return vec![assignment.clone()];
        }
        let (pattern_id, ground_hint) = pattern_term_pairs[0];
        let pattern = self.compiled_patterns[pattern_id].clone();
        self.match_pattern_recursive(
            assignment,
            &pattern,
            ground_hint,
            &pattern_term_pairs[1..].to_vec(),
        )
    }

    /// Match a single pattern against an optional ground term, then continue with remaining pairs.
    fn match_pattern_recursive(
        &mut self,
        assignment: &mut DeterministicHashMap<Local, u32>,
        pattern: &Pattern,
        ground_hint: Option<u32>,
        remaining: &Vec<(PatternId, Option<u32>)>,
    ) -> Vec<DeterministicHashMap<Local, u32>> {
        match pattern {
            Pattern::Var(name) => {
                let ground = ground_hint.expect("Pattern::Var requires a ground term to bind");
                match assignment.get(name) {
                    None => {
                        assignment.insert(name.clone(), ground);

                        self.match_patterns(assignment, remaining)
                    }
                    Some(v) if self.find(*v) == self.find(ground) => {
                        self.match_patterns(assignment, remaining)
                    }
                    Some(_) => vec![],
                }
            }
            Pattern::Ground(egraph_id) => match ground_hint {
                Some(ground) if self.find(*egraph_id) == self.find(ground) => {
                    self.match_patterns(assignment, remaining)
                }
                None => self.match_patterns(assignment, remaining),
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
                )
            }
        }
    }

    /// Find all function applications matching the given op, then recurse into sub-patterns.
    fn find_assignments_on_pattern(
        &mut self,
        ground_hint: Option<u32>,
        func_name: &str,
        sub_patterns: &[Pattern],
        remaining: &Vec<(PatternId, Option<u32>)>,
        assignment: &mut DeterministicHashMap<Local, u32>,
    ) -> Vec<DeterministicHashMap<Local, u32>> {
        let function_terms = match self.function_maps.get(func_name) {
            Some(terms) => terms.clone(),
            None => return vec![],
        };

        let mut list_assignments = Vec::new();
        let mut considered_function_terms = DeterministicHashSet::default();
        let ground_root = ground_hint.map(|t| self.find(t));

        for (i, subterms) in function_terms {
            if subterms.len() != sub_patterns.len() {
                continue;
            }

            let i_root = self.find(i);
            if ground_root.is_none() || ground_root.unwrap() == i_root {
                let subterms_canonical: Vec<u32> = subterms.iter().map(|s| self.find(*s)).collect();

                if considered_function_terms.contains(&subterms_canonical) {
                    continue;
                }
                considered_function_terms.insert(subterms_canonical);

                let new_assignments = self.match_subpatterns(
                    &mut assignment.clone(),
                    sub_patterns,
                    &subterms,
                    remaining,
                );
                list_assignments.extend(new_assignments);
            }
        }
        list_assignments
    }

    /// Match sub-patterns against ground subterms, then continue with remaining pattern pairs.
    fn match_subpatterns(
        &mut self,
        assignment: &mut DeterministicHashMap<Local, u32>,
        sub_patterns: &[Pattern],
        ground_subterms: &[u32],
        remaining: &Vec<(PatternId, Option<u32>)>,
    ) -> Vec<DeterministicHashMap<Local, u32>> {
        if sub_patterns.is_empty() {
            return self.match_patterns(assignment, remaining);
        }
        let pattern = &sub_patterns[0];
        let ground = ground_subterms[0];
        let rest_patterns = &sub_patterns[1..];
        let rest_grounds = &ground_subterms[1..];

        match pattern {
            Pattern::Var(name) => match assignment.get(name) {
                None => {
                    assignment.insert(name.clone(), ground);
                    self.match_subpatterns(assignment, rest_patterns, rest_grounds, remaining)
                }
                Some(v) if self.find(*v) == self.find(ground) => {
                    self.match_subpatterns(assignment, rest_patterns, rest_grounds, remaining)
                }
                Some(_) => vec![],
            },
            Pattern::Ground(egraph_id) => {
                if self.find(*egraph_id) == self.find(ground) {
                    self.match_subpatterns(assignment, rest_patterns, rest_grounds, remaining)
                } else {
                    vec![]
                }
            }
            Pattern::App(op, children) => {
                let func_name = op.to_function_map_key();
                let function_terms = match self.function_maps.get(&func_name) {
                    Some(terms) => terms.clone(),
                    None => return vec![],
                };

                let mut list_assignments = Vec::new();
                let ground_root = self.find(ground);
                let mut considered = DeterministicHashSet::default();

                for (i, subterms) in function_terms {
                    if subterms.len() != children.len() {
                        continue;
                    }
                    let i_root = self.find(i);
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
                            &subterms,
                            &vec![],
                        );
                        for mut sub in sub_results {
                            let more = self.match_subpatterns(
                                &mut sub,
                                rest_patterns,
                                rest_grounds,
                                remaining,
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
        let id = self.next_id;
        self.next_id += 1;
        self.register_term_internal(id, op, children, dynamic);
        id
    }

    fn register_constant(&mut self, op: Self::Op) -> Self::TermId {
        // TODO: currently relies on Op::Constant variant to distinguish constants
        // from other 0-arity terms. If Op is unified in the future, this method
        // should mark the term as a constant via a separate mechanism.
        let id = self.next_id;
        self.next_id += 1;
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

    fn notify_new_decision_level(&mut self) {
        assert!(
            self.arithmetic_merge_queue.is_empty(),
            "arithmetic queue must be drained before advancing decision level"
        );
        assert!(
            self.pending_congruence.is_empty() && self.pending_merges.is_empty(),
            "egraph must be rebuilt before advancing decision level"
        );
        self.decision_level += 1;
        while self.decision_level >= self.predecessor_level.len() {
            self.predecessor_level
                .resize(self.predecessor_level.len() * 2, 0);
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

    fn set_merge_tf(&mut self, term: Self::TermId) {
        if !self.merge_tf[term as usize] {
            self.merge_tf[term as usize] = true;
            if self.decision_level > 0 {
                self.merge_tf_upgrades.push((self.decision_level, term));
            }
            let root = self.find(term);
            self.set_merge_tf_class_witness(root, term, self.decision_level);
            self.queue_merge_tf_assignment(root, self.decision_level);
        }
    }

    fn assign_bool(
        &mut self,
        term: Self::TermId,
        lit: Lit,
        value: bool,
        bool_constant: Self::TermId,
    ) -> EgraphResult<Self::TermId> {
        if self.should_merge_tf(term) {
            self.assert_equal(term, bool_constant)
        } else {
            self.assign_bool_value(term, lit, value, bool_constant)
        }
    }

    fn rebuild(&mut self) -> EgraphResult<Self::TermId> {
        let mut result = EgraphResult::ok();
        loop {
            if let Some(((term, bool_constant), _)) = self.pending_merges.pop_first() {
                let merge_result = self.assert_equal(term, bool_constant);
                result.propagations.extend(merge_result.propagations);
                if let Some(conflict) = merge_result.conflict {
                    result.conflict = Some(conflict);
                    return result;
                }
                continue;
            }

            self.maybe_schedule_full_congruence_rebuild();
            let Some(term) = self.pending_congruence.pop() else {
                self.full_congruence_rebuild_active = false;
                return result;
            };
            debug_assert!(self.pending_congruence_flags[term as usize]);
            self.pending_congruence_flags[term as usize] = false;
            let congruence_result = self.rebuild_congruence(term);
            result.propagations.extend(congruence_result.propagations);
            if let Some(conflict) = congruence_result.conflict {
                result.conflict = Some(conflict);
                return result;
            }
        }
    }

    fn are_equal(&self, t1: Self::TermId, t2: Self::TermId) -> bool {
        self.find(t1) == self.find(t2)
    }

    fn match_triggers(
        &mut self,
        trigger_term_pairs: Vec<(PatternId, Option<Self::TermId>)>,
    ) -> Vec<DeterministicHashMap<Local, u32>> {
        let mut assignment = DeterministicHashMap::default();
        self.match_patterns(&mut assignment, &trigger_term_pairs)
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
