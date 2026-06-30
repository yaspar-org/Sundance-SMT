// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use super::datastructures::{CanonicalOp, DisequalTerm, Predecessor};
use super::proofforest::*;
use super::repr::{Children, Op, Pattern, PatternId, TermEntry, TermSlot};
use super::unionfind::ProofTracker;
use crate::debug_println;
use crate::egraphs::traits::{Conflict, EgraphResult, EgraphTrait, Lit};
use crate::log::is_important;
use crate::utils::{DeterministicHashMap, DeterministicHashSet, FastDeterministicHashMap};
use std::default::Default;
use std::fmt;

/// Key for the signature table: (operator, canonical children).
type SigKey = (CanonicalOp, Children);

/// Trail entry for undoing sig_table modifications on backtrack.
/// Stores the actual key used, so undo doesn't depend on UF state.
/// (level, key, term_id, was_inserted)
type SigTrailEntry = (usize, SigKey, u32, bool);

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
                    } => {
                        // we use get_term_safe here for child, because it could be that there actually is no child
                        writeln!(
                            f,
                            "  {} -> root [Root (size: {}, child: {:?}, disequalities: {:?}, children: {:?}])",
                            self.display_term(term_id as u32),
                            size,
                            self.display_term(*child),
                            disequalities,
                            children
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
    /// keeps track of terms created by quantifier instantiation and their predecessors
    predecessors_created_by_quantifiers: DeterministicHashMap<u32, DeterministicHashSet<u32>>,
    /// if a quantifier instantiates (f t) and t = s, then we want to add (f.uid(), "f", [t.uid()])
    union_to_eclass: DeterministicHashSet<u32>,
    /// Signature table: maps (op, [find(c1),...,find(cn)]) → term_id.
    /// Maintained in parallel with the existing congruence detection for now.
    sig_table: FastDeterministicHashMap<SigKey, u32>,
    /// Trail for backtracking the sig_table.
    sig_trail: Vec<SigTrailEntry>,
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
            }],
            proof_forest_backtrack_stack: Vec::new(),
            predecessors: vec![FastDeterministicHashMap::default()],
            predecessor_hash: 1,
            predecessor_level: vec![1, 1],
            function_maps: DeterministicHashMap::default(),
            decision_level: 0,
            predecessors_created_by_quantifiers: DeterministicHashMap::new(),
            union_to_eclass: DeterministicHashSet::new(),
            sig_table: FastDeterministicHashMap::default(),
            sig_trail: Vec::new(),
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

                match self.predecessors_created_by_quantifiers.get_mut(&child_uid) {
                    Some(parents) => {
                        parents.insert(id);
                    }
                    None => {
                        let mut parents = DeterministicHashSet::new();
                        parents.insert(id);
                        self.predecessors_created_by_quantifiers
                            .insert(child_uid, parents);
                    }
                };

                self.predecessors[root as usize]
                    .entry(id)
                    .or_insert(root_predecessor);
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
            self.union_to_eclass.insert(id);
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
                },
            );
            self.predecessors.resize(
                self.predecessors.len() * 2,
                FastDeterministicHashMap::default(),
            );
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
        };
        id
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
        let p = self.proof_forest[x as usize].clone();
        match p {
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
                let (l, h) = if level > highest_level {
                    (level, hash)
                } else {
                    (highest_level, highest_hash)
                };
                self.find_with_level(p, l, h)
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

    /// Remove a term from the sig_table (if it maps to expected_id), recording a trail entry.
    fn sig_table_remove(&mut self, key: &SigKey, expected_id: u32, level: usize) {
        if self.sig_table.get(key) == Some(&expected_id) {
            self.sig_table.remove(key);
            self.sig_trail
                .push((level, key.clone(), expected_id, false));
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
    fn leastcommonancestor(
        &self,
        u: u32,
        v: u32,
        tracker: &mut ProofTracker,
    ) -> Option<Vec<(u32, u32)>> {
        debug_println!(
            11,
            1,
            "Finding least common ancestor for {} and {}",
            self.display_term(u),
            self.display_term(v)
        );
        self.leastcommonancestor_helper(u, v, tracker, 0)
    }

    fn leastcommonancestor_helper(
        &self,
        u: u32,
        v: u32,
        tracker: &mut ProofTracker,
        indent: usize,
    ) -> Option<Vec<(u32, u32)>> {
        debug_println!(
            20,
            indent,
            "checking the equality of {} and {}",
            self.display_term(u),
            self.display_term(v)
        );
        let mut visited = DeterministicHashSet::default();

        let mut path_from_u = vec![];
        let mut curr = u;

        let max_recursion_depth = 100;
        if indent > max_recursion_depth {
            debug_println!(11, 0, "We have the proof forest :{}", self);
            panic!("Should not have this many recusive calls to LCH");
        }
        loop {
            let parent = self.proof_forest[curr as usize].clone();
            visited.insert(curr);
            if let ProofForestEdge::Root {
                size: _,
                child: _,
                disequalities: _,
                children: _,
            } = parent
            {
                visited.insert(curr);
                break;
            }
            curr = parent.get_parent();
            path_from_u.push(parent);
        }

        let mut path_from_v = vec![];
        curr = v;
        let mut parent: ProofForestEdge;
        loop {
            parent = self.proof_forest[curr as usize].clone();
            if visited.contains(&curr) {
                break;
            }
            if let ProofForestEdge::Root {
                size: _,
                child: _,
                disequalities: _,
                children: _,
            } = parent
            {
                return None;
            }
            curr = parent.get_parent();
            path_from_v.push(parent);
        }

        let mut proof: Vec<ProofForestEdge> = Vec::new();
        proof.extend(
            path_from_u
                .iter()
                .take_while(|x| **x != parent)
                .cloned()
                .collect::<Vec<ProofForestEdge>>(),
        );
        proof.extend(path_from_v);

        assert!(visited.contains(&curr));

        let mut final_proof = vec![];
        let mut proof_congruences = vec![];

        debug_println!(11, indent + 1, "We get the unprocessed proof {:?}", proof);
        debug_println!(16, indent + 1, "We have the proof:");
        for proof_term in proof {
            match proof_term {
                ProofForestEdge::Root {
                    size: _,
                    child: _,
                    disequalities: _,
                    children: _,
                } => {
                    eprintln!("ERROR: Root should not be processed");
                    std::process::exit(1);
                }
                ProofForestEdge::Congruence { pairs, .. } => {
                    if is_important(20) {
                        debug_println!(20, indent + 12, "Congruence ");
                        for (t1, t2) in pairs.clone() {
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
                    proof_congruences.push(pairs);
                }
                ProofForestEdge::Equality { term, .. } => {
                    if let Some((t1, t2)) = term {
                        debug_println!(
                            20,
                            indent + 12,
                            "Equality {} [{}] = {} [{}]",
                            self.display_term(t1),
                            t1,
                            self.display_term(t2),
                            t2
                        );
                        if tracker.union(t1, t2) {
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
            for pair in pairs {
                if let Some(subproof) =
                    self.leastcommonancestor_helper(pair.0, pair.1, tracker, indent + 1)
                {
                    final_proof.extend(subproof);
                }
            }
        }
        Some(final_proof)
    }

    /// Ensure internal bookkeeping is ready for operations at the given level.
    fn advance_to_level(&mut self, level: usize) {
        while level >= self.predecessor_level.len() {
            self.predecessor_level
                .resize(self.predecessor_level.len() * 2, 0);
        }
        if level > self.decision_level {
            self.decision_level = level;
            self.predecessor_level[level] = self.predecessor_hash;
        }
    }

    /// Assert t1 = t2 at the given decision level.
    /// Performs congruence closure. Returns a conflict if a disequality is violated.
    fn assert_equal(&mut self, t1: u32, t2: u32, level: usize) -> EgraphResult<u32> {
        self.advance_to_level(level);
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
    fn assert_disequal(
        &mut self,
        t1: u32,
        t2: u32,
        diseq_lit: i32,
        level: usize,
    ) -> EgraphResult<u32> {
        self.advance_to_level(level);
        let mut tracker = ProofTracker::new();
        if let Some(equalities) = self.leastcommonancestor(t1, t2, &mut tracker) {
            return EgraphResult::with_conflict(Conflict {
                equalities,
                disequality: (t1, t2),
                diseq_lit,
            });
        }
        let hash = self.predecessor_hash;
        self.add_disequality(t1, t2, diseq_lit, level, hash);
        EgraphResult::ok()
    }

    /// Assert all terms are pairwise distinct at the current decision level.
    fn assert_distinct(
        &mut self,
        terms: &[u32],
        diseq_lit: i32,
        level: usize,
    ) -> EgraphResult<u32> {
        for i in 0..terms.len() {
            for j in i + 1..terms.len() {
                let result = self.assert_disequal(terms[i], terms[j], diseq_lit, level);
                if result.conflict.is_some() {
                    return result;
                }
            }
        }
        EgraphResult::ok()
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

        // Re-add predecessors created by quantifiers at their new roots
        for (term, parents) in &self.predecessors_created_by_quantifiers.clone() {
            let current_ancestor = self.find(*term);
            for parent in parents {
                let predecessor = Predecessor {
                    level,
                    hash: self.predecessor_hash,
                    predecessor: *parent,
                    inner_term: *term,
                };
                self.predecessors[current_ancestor as usize].insert(*parent, predecessor);
            }
        }

        // Re-do union_to_eclass via sig table probe
        let union_to_eclass_info = self.union_to_eclass.clone();
        for term in union_to_eclass_info {
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
            self.union_to_eclass = DeterministicHashSet::new();
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

        let child_root = ProofForestEdge::Root {
            size: 0,
            child: childs_child,
            disequalities: new_disequalities,
            children: DeterministicHashSet::new(),
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
        debug_println!(11, 0, "{}", self);
        // assert_eq!(
        //     self.display_term(x).get_sort(self),
        //     self.display_term(y).get_sort(self),
        //     "We are comparing terms {} and {}",
        //     self.display_term(x),
        //     self.display_term(y)
        // );

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

        // keep track of original proof_parent
        let _proof_parent_original = proof_parent.clone();

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

        // Phase 1: Remove sig_table entries for y_root's predecessors BEFORE updating the UF.
        // Their signatures currently use y_root as a child representative; after the UF
        // update they'll need new entries with x_root instead.
        // Only process valid (non-stale) predecessors.
        let y_root_pred_keys: Vec<u32> = self.predecessors[y_root as usize]
            .iter()
            .filter(|(_, p)| valid_hash(p.hash, p.level, &self.predecessor_level))
            .map(|(k, _)| *k)
            .collect();
        for pred_id in &y_root_pred_keys {
            if let Some(old_sig) = self.compute_signature(*pred_id) {
                self.sig_table_remove(&old_sig, *pred_id, level);
            }
        }

        // Phase 2: Perform the union and propagate disequalities from y_root to x_root.
        debug_println!(
            16,
            2,
            "Making {} the root of its equivalence class [previously was {}]",
            self.display_term(y),
            self.display_term(y_root)
        );
        self.make_root(y, proof_parent);

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

        // basically checking if the current equality that we just added violated any earlier disequalities and if it did, we learn a conflict clause
        // TODO: now I am actually not sure if disequality checking is really necessary
        // kind've a weird way to do it since we have already unioned, we are just checking if two things are unequal to themselves
        debug_println!(
            5,
            0,
            "A. Checking the equality {} = {} with disequalities {:?}",
            self.display_term(x),
            self.display_term(y),
            self.proof_forest[x as usize].disequalities()
        );
        if let Some(disequality) = self.check_self_disequality(x_root).clone() {
            debug_println!(
                11,
                0,
                "B. Checking the equality {} = {} with disequality {} != {}",
                self.display_term(x),
                self.display_term(y),
                self.display_term(disequality.original_disequality.0),
                self.display_term(disequality.original_disequality.1)
            );
            let mut tracker = ProofTracker::new();
            if let Some(equalities) = self.leastcommonancestor(
                disequality.original_disequality.0,
                disequality.original_disequality.1,
                &mut tracker,
            ) {
                return EgraphResult::with_conflict(Conflict {
                    equalities,
                    disequality: disequality.original_disequality,
                    diseq_lit: disequality.diseq_lit,
                });
            } else {
                debug_println!(16, 0, "{}", self);
                panic!(
                    "Should have found a equality between {} [root: {}] and {} [root: {}]",
                    self.display_term(disequality.original_disequality.0),
                    self.display_term(self.find(disequality.original_disequality.0)),
                    self.display_term(disequality.original_disequality.1),
                    self.display_term(self.find(disequality.original_disequality.1)),
                );
            }
        }

        // Phase 3: Reinsert y_root's predecessors into sig_table with new canonical forms
        // and immediately merge any congruent pairs found.
        // Also move predecessors from y_root to x_root.
        let predecessors_v = std::mem::take(&mut self.predecessors[y_root as usize]);
        for (pred_key, pred_val) in &predecessors_v {
            let new_pred = Predecessor {
                level,
                hash: self.predecessor_hash,
                predecessor: *pred_key,
                inner_term: pred_val.inner_term,
            };
            self.add_predecessor(x_root, *pred_key, new_pred);
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
        assignment: &mut DeterministicHashMap<String, u32>,
        pattern_term_pairs: &[(PatternId, Option<u32>)],
    ) -> Vec<DeterministicHashMap<String, u32>> {
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
        assignment: &mut DeterministicHashMap<String, u32>,
        pattern: &Pattern,
        ground_hint: Option<u32>,
        remaining: &Vec<(PatternId, Option<u32>)>,
    ) -> Vec<DeterministicHashMap<String, u32>> {
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
        assignment: &mut DeterministicHashMap<String, u32>,
    ) -> Vec<DeterministicHashMap<String, u32>> {
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
        assignment: &mut DeterministicHashMap<String, u32>,
        sub_patterns: &[Pattern],
        ground_subterms: &[u32],
        remaining: &Vec<(PatternId, Option<u32>)>,
    ) -> Vec<DeterministicHashMap<String, u32>> {
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
    hash >= predecessor_level[level] || level == 0 // todo: I added this level ==0 ~> I think this is correct but need to double check to be sure
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

    fn assert_equal(
        &mut self,
        t1: Self::TermId,
        t2: Self::TermId,
        level: usize,
    ) -> EgraphResult<Self::TermId> {
        self.assert_equal(t1, t2, level)
    }

    fn assert_disequal(
        &mut self,
        t1: Self::TermId,
        t2: Self::TermId,
        lit: Lit,
        level: usize,
    ) -> EgraphResult<Self::TermId> {
        self.assert_disequal(t1, t2, lit, level)
    }

    fn assert_distinct(
        &mut self,
        terms: &[Self::TermId],
        lit: Lit,
        level: usize,
    ) -> EgraphResult<Self::TermId> {
        self.assert_distinct(terms, lit, level)
    }

    fn find(&self, term: Self::TermId) -> Self::TermId {
        self.find(term)
    }

    fn are_equal(&self, t1: Self::TermId, t2: Self::TermId) -> bool {
        self.find(t1) == self.find(t2)
    }

    fn match_triggers(
        &mut self,
        trigger_term_pairs: Vec<(PatternId, Option<Self::TermId>)>,
    ) -> Vec<DeterministicHashMap<String, u32>> {
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
        let mut tracker = ProofTracker::new();
        self.leastcommonancestor(t1, t2, &mut tracker)
    }
}
