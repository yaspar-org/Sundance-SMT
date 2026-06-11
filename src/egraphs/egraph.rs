// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::debug_println;
use crate::egraphs::congruence_closure::{add_parent, get_child, get_parent};
use crate::egraphs::repr::{Children, Op, TermEntry, TermSlot};
use crate::egraphs::traits::{Conflict, EgraphResult, EgraphTrait, Lit};
use crate::egraphs::unionfind::ProofTracker;
use crate::log::is_important;
use crate::egraphs::datastructures::{
    CanonicalForm, CanonicalOp, DisequalTerm, Predecessor,
};
use crate::egraphs::proofforest::*;
use crate::utils::{DeterministicHashMap, DeterministicHashSet, FastDeterministicHashMap};
use std::default::Default;
use std::fmt;

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
                            self.display_term(term_id as u64),
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
                            self.display_term(term_id as u64),
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
                            self.display_term(term_id as u64),
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
                            self.display_term(term_id as u64),
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
                    self.display_term(term as u64),
                    preds.len()
                )?;
                for pred in preds.values() {
                    writeln!(
                        f,
                        "    -> {} (level: {}, hash: {})",
                        self.display_term(pred.predecessor), pred.level, pred.hash
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
    next_id: u64,
    /// Internal term representation per term ID
    pub terms: Vec<TermSlot>,
    /// Pattern terms (for e-matching only, separate from ground terms)
    pub patterns: DeterministicHashMap<u64, TermEntry>,
    /// map from vertices (u64) -> ProofForestEdge
    pub proof_forest: Vec<ProofForestEdge>,
    /// keeps track of a stack of "edges" to backtrack on
    pub proof_forest_backtrack_stack: Vec<(usize, ProofForestEdge, u64, ProofForestEdge)>,
    /// this is a map from terms (u64) -> (term in the same egraph, predecessor of term in same egraph)
    pub predecessors: Vec<FastDeterministicHashMap<u64, Predecessor>>,
    /// number to keep track of the current hash
    pub predecessor_hash: u64,
    /// mapping from levels -> corresponding hash
    pub predecessor_level: Vec<u64>,
    /// map from functions (String) -> terms of this function
    pub function_maps: DeterministicHashMap<String, Vec<(u64, Vec<u64>)>>,
    /// uid for true
    pub true_term: u64,
    /// uid for false
    pub false_term: u64,
    /// the current decision level of the SAT solver, useful to keep track for backtracking
    pub decision_level: usize,
    /// keeps track of terms created by quantifier instantiation and their predecessors
    pub predecessors_created_by_quantifiers: DeterministicHashMap<u64, DeterministicHashSet<u64>>,
    /// if a quantifier instantiates (f t) and t = s, then we want to add (f.uid(), "f", [t.uid()])
    pub union_to_eclass: DeterministicHashSet<(u64, String, Vec<u64>)>,
}

impl Egraph {
    pub fn new() -> Self {

        Egraph {
            next_id: 0,
            terms: vec![TermSlot::Empty],
            patterns: DeterministicHashMap::new(),
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
            true_term: 0,
            false_term: 0,
            decision_level: 0,
            predecessors_created_by_quantifiers: DeterministicHashMap::new(),
            union_to_eclass: DeterministicHashSet::new(),
        }
    }

    /// Register an equality watch: when t1 ≡ t2, propagate lit.

    /// Returns the u64 corresponding to a given lit with the correct polarity
    /// Display a term recursively using the internal representation.
    pub fn display_term(&self, id: u64) -> String {
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
                    let children_str: Vec<String> = entry.children.as_slice()
                        .iter()
                        .map(|c| self.display_term(*c))
                        .collect();
                    format!("({} {})", entry.op.to_function_map_key(), children_str.join(" "))
                }
            }
        }
    }

    /// Register a single term in the egraph (non-recursive).
    /// Sets up terms_list, proof_forest, predecessors, function_maps for this term.
    /// Register a single term (non-recursive). Children must already be registered.
    /// Sets up terms_list, proof_forest, function_maps, and adds this term as a
    /// predecessor of each of its children.
    /// If `dynamic` is true, calls find_and_union_to_eclass to merge with any
    /// existing congruent term (needed for quantifier instantiation and datatype axioms).
    /// Returns true if the term was already registered.
    /// Register a single term (non-recursive). Children must already be registered.
    /// Takes raw IDs — no dependency on Term representation.
    pub fn register_term_internal(&mut self, id: u64, op: Op, children: &[u64], dynamic: bool) -> bool {
        // Resize storage if needed
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

        // If dynamic, find and merge with existing congruent terms
        if dynamic && !children.is_empty() {
            self.find_and_union_to_eclass(id, func_key.clone(), children.to_vec());
            self.union_to_eclass
                .insert((id, func_key, children.to_vec()));
        }

        false
    }

    /// Extract the Op from a Term and its function name string.
    /// Ensure storage is allocated for the given term ID without fully registering it.
    /// Used for quantifier body subterms that are opaque to the egraph.
    pub fn ensure_capacity(&mut self, id: u64) {
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

    /// Store a pattern term's structure (for match_term to inspect) without
    /// adding to function_maps, proof_forest, or predecessors. Pattern terms
    /// are only used for e-matching, never as ground terms.
    /// Stored in a separate map so they don't interfere with ground term registration.
    pub fn register_pattern_entry(&mut self, id: u64, op: Op, children: &[u64]) {
        self.patterns.insert(id, TermEntry {
            op,
            children: Children::from_slice(children),
        });
    }

    /// Register an opaque term — allocates a full slot with a proof_forest Root
    /// but no op/children/function_maps/predecessors. Used for quantifier terms
    /// that participate in union-find (merged with true/false) but not congruence.
    pub fn register_opaque_term(&mut self) -> u64 {
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

    /// If any predecessors of the first subterm are congruent to term_num
    /// (same function, all subterms equal), union them.
    pub fn find_and_union_to_eclass(&mut self, term_num: u64, func: String, subterms: Vec<u64>) {
        let subterm_num = subterms[0];
        let subterm_root = self.find(subterm_num);

        let subterm_root_predecessor = &self.predecessors[subterm_root as usize].clone();

        for (pred_key, pred) in subterm_root_predecessor {
            if !valid_hash(pred.hash, pred.level, &self.predecessor_level) {
                self.predecessors[subterm_root as usize].remove(pred_key);
                continue;
            }
            let pred_entry = match &self.terms[*pred_key as usize] { TermSlot::Term(e) => e, _ => continue };
            let pred_func = pred_entry.op.to_function_map_key();
            let pred_children = pred_entry.children.as_slice();
            if func == pred_func && pred_children.len() == subterms.len() {
                let mut equal = true;
                let mut congruence_pairs = vec![];
                for (pred_subterm_uid, subterm) in pred_children.iter().zip(subterms.iter()) {
                    let (pred_subterm_uid, subterm_uid) = (*pred_subterm_uid, *subterm);
                    let (subterm_equal, _, _) = self.check_equal(pred_subterm_uid, subterm_uid);
                    if !subterm_equal {
                        equal = false;
                        break;
                    }
                    congruence_pairs.push((pred_subterm_uid, subterm_uid));
                }
                if equal {
                    let equality = ProofForestEdge::Congruence {
                        pairs: congruence_pairs,
                        size: 0,
                        parent: term_num,
                        child: *pred_key,
                        disequalities: DeterministicHashMap::new(),
                        level: self.decision_level,
                        hash: self.predecessor_hash,
                        children: DeterministicHashSet::new(),
                    };
                    self.cc_union(
                        term_num,
                        *pred_key,
                        equality,
                        self.decision_level,
                        false,
                        true,
                    );
                }
            }
        }
    }

    pub fn find(&self, x: u64) -> u64 {
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
    pub fn find_with_level(
        &self,
        x: u64,
        highest_level: usize,
        highest_hash: u64,
    ) -> (u64, usize, u64) {
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

    // checks if x and y are equal in union find datastructure
    // if they are equal, returns the largest level in both their paths to a
    // common ancestor and the corresponding hash
    pub fn check_equal(&self, x: u64, y: u64) -> (bool, usize, u64) {
        let mut x_parent = x;
        let (mut highest_level_x, mut highest_hash_x) = (0, 0);
        let mut x_stack = vec![x];
        while x_parent != y {
            match self.proof_forest[x_parent as usize] {
                ProofForestEdge::Root { .. } => break,
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
                    if level > highest_level_x {
                        (highest_level_x, highest_hash_x) = (level, hash);
                    }
                    x_parent = p;
                    x_stack.push(x_parent)
                }
            }
        }

        if x_parent == y {
            return (true, highest_level_x, highest_hash_x);
        };

        let mut y_parent = y;
        let (mut highest_level_y, mut highest_hash_y) = (0, 0);
        let mut y_stack = vec![y];
        while y_parent != x {
            match self.proof_forest[y_parent as usize] {
                ProofForestEdge::Root { .. } => break,
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
                    if level > highest_level_y {
                        (highest_level_y, highest_hash_y) = (level, hash);
                    }
                    y_parent = p;
                    y_stack.push(y_parent)
                }
            }
        }

        if y_parent == x {
            return (true, highest_level_y, highest_hash_y);
        };

        // if they are in the same tree need to recompute the root
        // this is super gnarly -> make better
        if y_parent == x_parent {
            while x_stack.len() > 1
                && y_stack.len() > 1
                && x_stack[x_stack.len() - 2] == y_stack[y_stack.len() - 2]
            {
                assert!(x_stack[x_stack.len() - 1] == y_stack[y_stack.len() - 1]);
                x_stack.pop();
                y_stack.pop();
            }

            assert!(x_stack[x_stack.len() - 1] == y_stack[y_stack.len() - 1]);

            let common_root = x_stack[x_stack.len() - 1];
            let (mut highest_level, mut highest_hash) = (0, 0);

            let mut x_parent = x;
            while x_parent != common_root {
                match self.proof_forest[x_parent as usize] {
                    ProofForestEdge::Root { .. } => {
                        panic!()
                    }
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
                        if level > highest_level {
                            (highest_level, highest_hash) = (level, hash);
                        }
                        x_parent = p;
                    }
                }
            }

            let mut y_parent = y;
            while y_parent != common_root {
                match self.proof_forest[y_parent as usize] {
                    ProofForestEdge::Root { .. } => {
                        panic!()
                    }
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
                        if level > highest_level {
                            (highest_level, highest_hash) = (level, hash);
                        }
                        y_parent = p;
                    }
                }
            }

            return (true, highest_level, highest_hash);
        }

        (false, 0, 0)
    }

    /// Adds a disequality between t1 and t2 to the egraph
    pub fn add_disequality(&mut self, t1: u64, t2: u64, diseq_lit: i32, level: usize, hash: u64) {
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
    pub fn check_self_disequality(&self, t: u64) -> Option<DisequalTerm> {
        assert!(t == self.find(t));
        debug_println!(
            19,
            1,
            "We are in check_self_disequality with t {}",
            self.display_term(t)
        );
        let t_disequalities = &self.proof_forest[t as usize].disequalities();
        debug_println!(19, 2, "We have t_disequalities {:?}", t_disequalities);

        // TODO: should not need to sort disequalities here if we are using a deterministic hashmap
        let sorted_disequalities: Vec<_> = t_disequalities.iter().collect();
        // sorted_disequalities.sort_by_key(|(key, _)| **key);

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
                // assert! ((smaller_term == self.find(disequality.original_disequality.0) && larger_term == self.find(disequality.original_disequality.1)) || (smaller_term == self.find(disequality.original_disequality.1) && larger_term == self.find(disequality.original_disequality.0)));
                return Some(disequality.clone());
            }
        }
        None
    }

    /// Set the terms corresponding to x and y equal in egraph
    // TODO: make_eq moved to SolverState (uses cnf_cache, context)

    /// Get the canonical form for some term
    /// For example the canoncial form for f(x, y) is (f, root(x), root(y))  
    /// TODO: I don't support canonical forms for non-app, non-eq terms, non-ite terms, but will have to do that eventually
    pub fn get_canonical_form(&self, term_num: u64, _level: usize) -> Option<CanonicalForm> {
        let entry = match &self.terms[term_num as usize] {
            TermSlot::Term(e) => e,
            _ => return None,
        };

        let original_subterms = entry.children.as_slice().to_vec();
        let op = match &entry.op {
            Op::App(s) => CanonicalOp::App(s.to_string()),
            Op::Eq => CanonicalOp::Eq,
            Op::Ite => CanonicalOp::Ite,
            _ => return None,
        };

        let canonical_subterms: Vec<u64> =
            original_subterms.iter().map(|&t| self.find(t)).collect();
        Some(CanonicalForm {
            original_subterms,
            op,
            canonical_subterms,
        })
    }

    /// Adds a predecessor to a term (for example f(x) to x)
    ///
    /// TODO: right now this is preferring the smallest level, but this might not always be
    /// correct depending on the invariants
    pub fn add_predecessor(&mut self, term: u64, new_pred_key: u64, new_pred: Predecessor) {
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

    // TODO: check_for_recursive_datatypes moved to SolverState

    /// Explain why u ≡ v by walking the proof forest to their least common ancestor.
    /// Returns None if u and v are not in the same equivalence class.
    pub(crate) fn leastcommonancestor(
        &self,
        u: u64,
        v: u64,
        tracker: &mut ProofTracker,
    ) -> Option<Vec<(u64, u64)>> {
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
        u: u64,
        v: u64,
        tracker: &mut ProofTracker,
        indent: usize,
    ) -> Option<Vec<(u64, u64)>> {
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
            curr = get_parent(&parent);
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
            curr = get_parent(&parent);
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

    /// Assert t1 = t2 at the current decision level.
    /// Performs congruence closure. Returns a conflict if a disequality is violated.
    pub fn assert_equal(&mut self, t1: u64, t2: u64, level: usize) -> EgraphResult<u64> {
        let fixed = level == 0;
        let from_quantifier = level > 0;
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
        self.cc_union(t1, t2, proof_parent, level, fixed, from_quantifier)
    }

    /// Assert t1 ≠ t2 at the current decision level.
    /// Returns a conflict if t1 and t2 are already in the same equivalence class.
    pub fn assert_disequal(&mut self, t1: u64, t2: u64, diseq_lit: i32, level: usize) -> EgraphResult<u64> {
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
    pub fn assert_distinct(&mut self, terms: &[u64], diseq_lit: i32, level: usize) -> EgraphResult<u64> {
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
    pub fn backtrack_to(&mut self, level: usize) {
        self.predecessor_hash += 1;

        for i in level + 1..self.decision_level + 1 {
            self.predecessor_level[i] = self.predecessor_hash;
        }

        self.decision_level = level;

        // Pop proof forest backtrack stack
        while !self.proof_forest_backtrack_stack.is_empty() {
            let last_level = self.proof_forest_backtrack_stack.last().unwrap().0;
            if last_level <= level {
                break;
            }
            let (_, backtrack_equality, y, y_root) =
                self.proof_forest_backtrack_stack.pop().unwrap();
            self.proof_forest_backtrack(backtrack_equality, y, y_root);
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

        // Re-do union_to_eclass
        let union_to_eclass_info = self.union_to_eclass.clone();
        for (term, func, subterms) in union_to_eclass_info {
            self.find_and_union_to_eclass(term, func, subterms);
        }

        // Clear at level 0
        if level == 0 {
            self.predecessors_created_by_quantifiers = DeterministicHashMap::new();
            self.union_to_eclass = DeterministicHashSet::new();
            self.proof_forest_backtrack_stack = vec![];
        }
    }

    /// Undo a single union operation during backtracking.
    pub(crate) fn proof_forest_backtrack(
        &mut self,
        equality: ProofForestEdge,
        y: u64,
        y_parent: ProofForestEdge,
    ) {
        let child = &get_child(&equality);
        let child_edge = self.proof_forest[*child as usize].clone();
        let parent = &get_parent(&equality);
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
            assert_eq!(get_parent(&parent_edge), get_child(&equality));
            debug_println!(6, 0, "after first assert");
            assert_eq!(get_child(&parent_edge), get_parent(&equality));
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

        let childs_child = get_child(&child_edge);

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
    pub(crate) fn cc_union(
        &mut self,
        x: u64,
        y: u64,
        proof_parent: ProofForestEdge,
        level: usize,
        fixed: bool,
        from_quantifier: bool,
    ) -> EgraphResult<u64> {
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
            add_parent(proof_parent, x, y, level, self.predecessor_hash);

        let y_root_parent = &self.proof_forest[y_root as usize];

        if !fixed {
            // not adding fixed levels to backtracking based on what Armin said
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
            if value.hash >= self.predecessor_level[value.level]
                || value.hash == 0
                || value.level == 0
            {
                // added value.level == 0 since I think all hashes should be valid at level 0
                // TODO: borrowing issue so I can't use valid_hash function

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

        self.union_predecessors(x_root, y_root, level, fixed, from_quantifier)
    }

    /// Given u and v (roots of u_original and v_original), check the predecessors of
    /// each of these and union them if they have become equal
    ///
    /// TODO: I probably actually don't want this to delete all of the predecessors of u because it will screw up backtracking
    /// you only have to do it for predecessor terms that are roots of a congruent class
    /// once you merge two predecessor states, then you don't need to look at it until you backtrack
    ///
    /// TODO: need to implement a backtracking where I change the predecessor hash
    pub(crate) fn union_predecessors(
        &mut self,
        u: u64,
        v: u64,
        level: usize,
        fixed: bool,
        from_quantifier: bool,
    ) -> EgraphResult<u64> {
        debug_println!(
            11,
            1,
            "Unioning predecessors of {} [{}, Predecessors: {}] and {} [{}, Predecessors: {}]",
            self.display_term(u),
            u,
            format!("{:?}",
                self.predecessors[u as usize]
                    .keys()
                    .map(|x| self.display_term(*x))
                    .collect::<Vec<_>>()
            ),
            self.display_term(v),
            v,
            format!("{:?}",
                self.predecessors[v as usize]
                    .keys()
                    .map(|x| self.display_term(*x))
                    .collect::<Vec<_>>()
            )
        );

        debug_assert!(u != v);
        debug_assert!(self.find(u) == u);

        let result = EgraphResult::ok();

        // Move u's and v's predecessor maps out of the egraph so we can iterate
        // without cloning. Both slots are restored before any re-entrant call
        // (add_predecessor / union_process_assignment) can observe them.
        let mut predecessors_u = std::mem::take(&mut self.predecessors[u as usize]);
        let predecessors_v = std::mem::take(&mut self.predecessors[v as usize]);

        let mut canonical_forms_u: FastDeterministicHashMap<_, Vec<(Vec<u64>, u64)>> =
            FastDeterministicHashMap::default();

        // Stale entries are dropped in-place via retain before iterating.
        predecessors_u.retain(|_, p| {
            let keep = valid_hash(p.hash, p.level, &self.predecessor_level);
            if !keep {
                debug_println!(
                    11,
                    2,
                    "CANONICAL_FORMS_U: Skipping predecessor {} of {} [original: {}] as it has hash {} at level {} and correct hash is {}",
                    self.display_term(p.predecessor),
                    self.display_term(u),
                    self.display_term(p.inner_term),
                    p.hash,
                    p.level,
                    self.predecessor_level[p.level]
                );
            }
            keep
        });

        for (_pred_u_key, predecessor_u) in predecessors_u.iter() {
            debug_println!(
                11,
                2,
                "1.We are in union_predecessors trying to get term for {}",
                self.display_term(predecessor_u.predecessor)
            );

            // checking if the ite leads to a contradiction
            // if let Some(negated_model) =
            //     union_process_ite(&egraph.get_term(predecessor_u.predecessor), egraph, level, from_quantifier)
            // {
            //      debug_println!(
            //         4,
            //         3,
            //         "M. Contradiction found in union_predecessors, we have the following negated_model: {:?}",
            //         negated_model
            //     );
            //     return Some(negated_model);
            // }

            if let Some(CanonicalForm {
                original_subterms,
                op,
                canonical_subterms,
            }) = self.get_canonical_form(predecessor_u.predecessor, level)
            {
                let canonical_form = (op, canonical_subterms);
                debug_println!(
                    11,
                    4,
                    "We are adding in the canonical_form {:?}",
                    canonical_form
                );
                if let Some(forms) = canonical_forms_u.get_mut(&canonical_form) {
                    forms.push((original_subterms, predecessor_u.predecessor))
                } else {
                    canonical_forms_u.insert(
                        canonical_form,
                        vec![(original_subterms, predecessor_u.predecessor)],
                    );
                }
            }
        }

        debug_println!(
            11,
            4,
            "2.We have the canonical_forms_u {:?}",
            canonical_forms_u
        );

        // Restore u's slot before calling add_predecessor below, which writes to it.
        self.predecessors[u as usize] = predecessors_u;

        // basically the issue was that in `union_predecessors` when you create a `canonical_term_u`,
        // you fix it, but then you compare to a for loop iterating through all terms in v and iteratively
        // computing the canonical_term_v, but this could change as you are iterating through the loop
        // so we want to precompute the canonical terms of v.
        //
        // Precompute: store (key, predecessor_id, canonical_form) per entry.
        // No Predecessor clone — just the scalar `predecessor` field needed downstream.
        let mut predecessor_v_canonical_forms: Vec<(u64, u64, Option<CanonicalForm>)> =
            Vec::with_capacity(predecessors_v.len());
        for (pred_v_key, predecessor_v) in predecessors_v.iter() {
            let canonical_form = self.get_canonical_form(predecessor_v.predecessor, level);
            predecessor_v_canonical_forms.push((
                *pred_v_key,
                predecessor_v.predecessor,
                canonical_form,
            ));
        }

        // moving predecessors from v to u
        for (pred_key, pred_val) in predecessors_v.iter() {
            debug_println!(
                11,
                0,
                "We are are adding predecessor {} (of  {}) to {} [level: {}, hash: {}]",
                self.display_term(*pred_key),
                self.display_term(pred_val.inner_term),
                self.display_term(u),
                level,
                self.predecessor_hash
            );
            let new_pred = Predecessor {
                level,
                hash: self.predecessor_hash,
                predecessor: *pred_key,
                inner_term: pred_val.inner_term,
            };
            self.add_predecessor(u, *pred_key, new_pred);
        }

        // Restore v before the consuming loop — union_process_assignment can
        // re-enter and read/write self.predecessors[v].
        self.predecessors[v as usize] = predecessors_v;

        for (pred_v_key, pred_predecessor, canonical_form_v) in predecessor_v_canonical_forms {
            // Look up the predecessor's validity from the restored v slot.
            // Extract only scalar fields — no Predecessor clone.
            let (pred_hash, pred_level, pred_inner_term) =
                match self.predecessors[v as usize].get(&pred_v_key) {
                    Some(p) => (p.hash, p.level, p.inner_term),
                    None => continue, // removed by a prior iteration
                };
            if !valid_hash(pred_hash, pred_level, &self.predecessor_level) {
                debug_println!(
                    11,
                    5,
                    "Skipping predecessor {} of {} [original: {}] as it has hash {} at level {} and correct hash is {}",
                    self.display_term(pred_predecessor),
                    self.display_term(v),
                    self.display_term(pred_inner_term),
                    pred_hash,
                    pred_level,
                    self.predecessor_level[pred_level]
                );
                debug_println!(
                    11,
                    5,
                    "The current level is {} and hash is {}",
                    level,
                    self.predecessor_hash
                );
                self.predecessors[v as usize].remove(&pred_v_key);
                continue;
            }
            debug_println!(
                11,
                3,
                "L. We are in union_predecessors trying to get term for {}",
                self.display_term(pred_predecessor)
            );

            if let Some(CanonicalForm {
                original_subterms,
                op,
                canonical_subterms,
            }) = canonical_form_v
            {
                let canonical_form = (op, canonical_subterms);
                debug_println!(
                    11,
                    6,
                    "3. We are in union_predecessors for v and have canonical form {:?} for {}",
                    canonical_form,
                    self.display_term(pred_predecessor)
                );
                if let Some(u_forms) = canonical_forms_u.get(&canonical_form) {
                    debug_println!(5, 0, "We have the following u_forms {:?}", u_forms);
                    for (u_original_subterms, canonical_form_u) in u_forms {
                        debug_println!(
                            16,
                            0,
                            "We are actually merging the two predecessors {} and {}",
                            self.display_term(*canonical_form_u),
                            self.display_term(pred_predecessor)
                        );
                        if is_important(16) {
                            debug_println!(16, 0, "We have u_original_subterms: ");
                            for term in u_original_subterms {
                                debug_println!(16, 4, "{}", self.display_term(*term));
                            }
                            debug_println!(16, 0, "We have original_subterms: ");
                            for term in original_subterms.clone() {
                                debug_println!(16, 4, "{}", self.display_term(term));
                            }
                        }

                        let terms_pairwise = u_original_subterms
                            .clone()
                            .into_iter()
                            .zip(original_subterms.clone())
                            .collect::<Vec<(u64, u64)>>();
                        let proof_parent = ProofForestEdge::Congruence {
                            size: 0,
                            pairs: terms_pairwise,
                            parent: 0,
                            child: 0,
                            disequalities: DeterministicHashMap::new(),
                            level,
                            hash: self.predecessor_hash,
                            children: DeterministicHashSet::new(),
                        }; // TODO: I can't have a child of -1 anymore, but I think doing it like this is correct

                        let sub_result = self.cc_union(
                            *canonical_form_u,
                            pred_predecessor,
                            proof_parent,
                            level,
                            fixed,
                            from_quantifier,
                        );
                        if sub_result.conflict.is_some() {
                            return sub_result;
                        }
                    }
                }
            }
        }
        debug_println!(
            11,
            0,
            "[exiting union_pred] of {} and {} with None",
            self.display_term(u),
            self.display_term(v)
        );
        result
    }


    /// Make vertex the root of its proof-forest tree.
    pub(crate) fn make_root(&mut self, vertex: u64, proof_parent: ProofForestEdge) {
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
    pub fn match_term(
        &mut self,
        assignment: &mut DeterministicHashMap<String, u64>,
        trigger_term_pairs: Vec<(u64, Option<u64>)>,
    ) -> Vec<DeterministicHashMap<String, u64>> {
        if trigger_term_pairs.is_empty() {
            return vec![assignment.clone()];
        }
        let (trigger, term) = trigger_term_pairs[0];
        let trigger_entry = self.patterns.get(&trigger)
            .unwrap_or_else(|| panic!("match_term: trigger {} is not a registered pattern", trigger))
            .clone();

        match &trigger_entry.op {
            Op::Constant(_) => {
                if term.is_none() || self.find(trigger) == self.find(term.unwrap()) {
                    self.match_term(assignment, trigger_term_pairs[1..].to_vec())
                } else {
                    vec![]
                }
            }
            Op::Local(name) => {
                match assignment.get(name) {
                    None => {
                        assignment.insert(name.clone(), term.unwrap());
                        let new_assignments =
                            self.match_term(assignment, trigger_term_pairs[1..].to_vec());
                        new_assignments
                    }
                    Some(v) if self.find(*v) == self.find(term.unwrap()) => {
                        self.match_term(assignment, trigger_term_pairs[1..].to_vec())
                    }
                    Some(_) => {
                        vec![]
                    }
                }
            }
            op if !trigger_entry.children.is_empty() => {
                let func_name = op.to_function_map_key();
                let children: Vec<u64> = trigger_entry.children.as_slice().to_vec();
                self.find_assignments_on_term(
                    term,
                    &func_name,
                    children,
                    trigger_term_pairs,
                    assignment,
                )
            }
            _ => panic!(
                "Trigger term {} is not an App or variable",
                self.display_term(trigger)
            ),
        }
    }

    /// Given a function name and arguments, find all matching applications in the egraph.
    /// Given a function name and trigger children (as IDs), find all matching applications.
    fn find_assignments_on_term(
        &mut self,
        term: Option<u64>,
        func_name: &str,
        trigger_children: Vec<u64>,
        trigger_term_pairs: Vec<(u64, Option<u64>)>,
        assignment: &mut DeterministicHashMap<String, u64>,
    ) -> Vec<DeterministicHashMap<String, u64>> {
        let mut list_assignments = Vec::new();

        let function_terms = self.function_maps.get(func_name);
        if function_terms.is_none() {
            return vec![];
        }

        let function_terms = function_terms.unwrap().clone();
        let mut considered_function_terms = DeterministicHashSet::default();

        let term_root = term.map(|t| self.find(t));
        for (i, subterms) in function_terms {
            assert!(subterms.len() == trigger_children.len());

            let i_root = self.find(i);
            if term_root.is_none() || term_root.unwrap() == i_root {
                let subterms_canonical = subterms.iter().map(|s| self.find(*s)).collect::<Vec<_>>();

                if considered_function_terms.contains(&subterms_canonical) {
                    continue;
                }
                considered_function_terms.insert(subterms_canonical);

                let mut new_pairs: Vec<(u64, Option<u64>)> = trigger_children
                    .iter()
                    .zip(subterms.iter())
                    .map(|(a, s)| (*a, Some(*s)))
                    .collect();
                new_pairs.extend(trigger_term_pairs[1..].to_vec());
                let new_assignments = self.match_term(&mut assignment.clone(), new_pairs);

                list_assignments.extend(new_assignments);
            }
        }
        list_assignments
    }
}

// HasArena for Egraph removed — use HasArena for SolverState instead (in solver_state.rs)

// CNFConversion<Egraph> removed — use CNFConversion<SolverState> instead (in solver_state.rs)

/// Checks if the hash is still valid at the given level
pub fn valid_hash(hash: u64, level: usize, predecessor_level: &[u64]) -> bool {
    debug_println!(
        5,
        0,
        "We are in valid_hash with hash {} and level {}",
        hash,
        level
    );
    hash >= predecessor_level[level] || hash == 0 || level == 0 // todo: I added this level ==0 ~> I think this is correct but need to double check to be sure
}

impl EgraphTrait for Egraph {
    type Op = Op;
    type TermId = u64;

    fn register_true(&mut self) -> Self::TermId {
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
        self.true_term = id;
        id
    }

    fn register_false(&mut self) -> Self::TermId {
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
        self.false_term = id;
        id
    }

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
        trigger_term_pairs: Vec<(Self::TermId, Option<Self::TermId>)>,
    ) -> Vec<DeterministicHashMap<String, u64>> {
        let mut assignment = DeterministicHashMap::default();
        self.match_term(&mut assignment, trigger_term_pairs)
    }

    fn backtrack_to(&mut self, level: usize) {
        self.backtrack_to(level)
    }

    fn make_decision(&self, _assignments: &[i32]) -> i32 {
        0
    }

    fn make_decision_lit(&self, lit: Lit, _assignments: &[i32]) -> Lit {
        lit
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
