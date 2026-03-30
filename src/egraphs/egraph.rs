// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::cnf::{CNFCache, CNFConversion, CNFEnv};
use crate::datatypes::process::DatatypeInfo;
use crate::debug_println;
use crate::egraphs::congruence_closure::union;
use crate::egraphs::datastructures::{
    Assertion, ConstructorType, DisequalTerm, Polarity::*, Predecessor, Quantifier, TermOption,
};
use crate::egraphs::proofforest::*;
use crate::egraphs::utils::get_subterms;
use crate::quantifiers::datalogmatch::{self, FlatAtom};
use crate::utils::{DeterministicHashMap, DeterministicHashSet};
use sat_interface::Formula;
use std::collections::{HashMap, HashSet};
use std::default::Default;
use std::fmt;
use yaspar_ir::ast::{ATerm::*, Arena, Context, FetchSort, HasArena, ObjectAllocatorExt, Str};
use yaspar_ir::ast::{Attribute, Repr, Term, TermAllocator};

impl fmt::Display for Egraph {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "=== Egraph Summary ===")?;

        // Basic statistics
        writeln!(f, "Proof forest entries: {}", self.proof_forest.len())?;
        writeln!(f, "Predecessor relationships: {}", self.predecessors.len())?;
        writeln!(f, "Assertions: {}", self.assertions.len())?;
        writeln!(f, "Quantifiers: {}", self.quantifiers.len())?;
        writeln!(f, "Function entries: {}", self.function_entries.len())?;

        // Proof forest structure
        if !self.proof_forest.is_empty() {
            writeln!(f, "\n=== Proof Forest ===")?;
            for (term_id, edge) in self.proof_forest.iter().enumerate() {
                if self.terms_list[term_id].is_none() {
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
                            self.get_term(term_id as u64),
                            size,
                            self.get_term_safe(*child),
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
                            self.get_term(term_id as u64),
                            self.get_term(*parent),
                            self.get_term(*t1),
                            self.get_term(*t2),
                            size,
                            self.get_term(*parent),
                            self.get_term(*child),
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
                            self.get_term(term_id as u64),
                            self.get_term(*parent),
                            size,
                            self.get_term(*parent),
                            self.get_term(*child),
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
                            self.get_term(term_id as u64),
                            self.get_term(*parent),
                            pairs
                                .iter()
                                .map(|(t1, t2)| (self.get_term(*t1), self.get_term(*t2)))
                                .collect::<Vec<_>>(),
                            size,
                            self.get_term(*parent),
                            self.get_term(*child),
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
                    self.terms_list[term],
                    preds.len()
                )?;
                for pred in preds.values() {
                    writeln!(
                        f,
                        "    -> {} (level: {}, hash: {})",
                        self.terms_list[pred.predecessor as usize], pred.level, pred.hash
                    )?; // TODO: it is bad form to use self.false_term as the fallback here
                }
            }
        }

        // Function entries (raw log)
        if !self.function_entries.is_empty() {
            writeln!(f, "\n=== Function Applications ===")?;
            for (func_name, applications) in self.function_entries.iter() {
                writeln!(f, "  {}: {} applications", func_name, applications.len())?;
                for (term_id, subterms) in applications {
                    write!(f, "    {} (", self.get_term(*term_id))?;
                    for subterm in subterms {
                        write!(f, " {}, ", self.get_term(*subterm))?;
                    }
                    writeln!(f, ")")?;
                }
            }
        }

        // Assertions
        if !self.assertions.is_empty() {
            writeln!(f, "\n=== Assertions ===")?;
            for assertion in &self.assertions {
                writeln!(f, "  {:?}", assertion)?;
            }
        }

        // Quantifiers
        if !self.quantifiers.is_empty() {
            writeln!(f, "\n=== Quantifiers ===")?;
            for quantifier in &self.quantifiers {
                writeln!(f, "  {:?}", quantifier)?;
            }
        }

        writeln!(f, "=== End Egraph Summary ===")?;
        Ok(())
    }
}

// ============================================================
// Timestamped index data structures for semi-naive evaluation
// ============================================================

/// Entries under a single e-class key, grouped by the matching round (timestamp)
/// in which they became current. Stored as an OrdMap so we can efficiently
/// query only entries from recent rounds via `range(matching_round..)`.
#[derive(Clone, Debug)]
pub struct TimestampedEntries {
    pub entries: im::OrdMap<usize, Vec<u64>>,
}

impl TimestampedEntries {
    pub fn new() -> Self {
        TimestampedEntries {
            entries: im::OrdMap::new(),
        }
    }

    /// Insert an fnode UID at the given timestamp.
    pub fn insert(&mut self, timestamp: usize, fnode_uid: u64) {
        self.entries.entry(timestamp).or_insert_with(Vec::new).push(fnode_uid);
    }

    /// Get all fnode UIDs across all timestamps.
    pub fn all(&self) -> impl Iterator<Item = u64> + '_ {
        self.entries.values().flat_map(|v| v.iter().copied())
    }

    /// Get only delta fnode UIDs (timestamp >= matching_round).
    /// Uses range query to skip old entries entirely.
    pub fn delta(&self, matching_round: usize) -> impl Iterator<Item = u64> + '_ {
        self.entries.range(matching_round..).flat_map(|(_, v)| v.iter().copied())
    }

    /// Check if there are any delta entries (timestamp >= matching_round).
    pub fn has_delta(&self, matching_round: usize) -> bool {
        self.entries.range(matching_round..).next().is_some()
    }

    /// Merge all entries from another TimestampedEntries, re-stamping them
    /// at the given timestamp (their canonical form changed due to a merge).
    pub fn merge_from(&mut self, other: &TimestampedEntries, timestamp: usize) {
        let all_fnodes: Vec<u64> = other.all().collect();
        if !all_fnodes.is_empty() {
            self.entries.entry(timestamp).or_insert_with(Vec::new).extend(all_fnodes);
        }
    }
}

/// Index from e-class root to timestamped fnode entries.
/// Tracks a max timestamp for O(1) "has any delta?" checks.
#[derive(Clone, Debug)]
pub struct EClassIndex {
    /// Maximum timestamp across all entries in this index.
    pub max_stamp: usize,
    /// Maps e-class root -> timestamped entries under that e-class.
    pub index: im::OrdMap<u64, TimestampedEntries>,
}

impl EClassIndex {
    pub fn new() -> Self {
        EClassIndex {
            max_stamp: 0,
            index: im::OrdMap::new(),
        }
    }

    /// Insert an fnode UID under the given e-class at the given timestamp.
    pub fn insert(&mut self, eclass: u64, timestamp: usize, fnode_uid: u64) {
        self.index
            .entry(eclass)
            .or_insert_with(TimestampedEntries::new)
            .insert(timestamp, fnode_uid);
        if timestamp > self.max_stamp {
            self.max_stamp = timestamp;
        }
    }

    /// Get all fnode UIDs under the given e-class (all timestamps).
    pub fn get_all(&self, eclass: u64) -> Vec<u64> {
        self.index
            .get(&eclass)
            .map(|ts| ts.all().collect())
            .unwrap_or_default()
    }

    /// Get only delta fnode UIDs under the given e-class.
    pub fn get_delta(&self, eclass: u64, matching_round: usize) -> Vec<u64> {
        let result: Vec<u64> = self
            .index
            .get(&eclass)
            .map(|ts| ts.delta(matching_round).collect())
            .unwrap_or_default();
        if result.is_empty() {
            if let Some(ts) = self.index.get(&eclass) {
                let all: Vec<u64> = ts.all().collect();
                let stamps: Vec<&usize> = ts.entries.keys().collect();
                if !all.is_empty() {
                    debug_println!(
                        26, 0,
                        "      get_delta: eclass={} matching_round={} -> 0 delta but {} total entries, stamps={:?}",
                        eclass, matching_round, all.len(), stamps
                    );
                }
            }
        }
        result
    }

    /// Check if this index has any delta entries at all (O(1)).
    pub fn has_delta(&self, matching_round: usize) -> bool {
        self.max_stamp >= matching_round
    }

    /// Merge entries from old_root into new_root at the given timestamp.
    /// Returns true if any entries were actually moved.
    pub fn merge_roots(&mut self, old_root: u64, new_root: u64, timestamp: usize) -> bool {
        if let Some(old_entries) = self.index.remove(&old_root) {
            let count: usize = old_entries.entries.values().map(|v| v.len()).sum();
            debug_println!(26, 0, "      EClassIndex::merge_roots: moving {} entries from {} to {} at stamp={}", count, old_root, new_root, timestamp);
            self.index
                .entry(new_root)
                .or_insert_with(TimestampedEntries::new)
                .merge_from(&old_entries, timestamp);
            if timestamp > self.max_stamp {
                self.max_stamp = timestamp;
            }
            true
        } else {
            false
        }
    }
}

/// Per-function output index: maps output e-class to fnode UIDs.
#[derive(Clone, Debug)]
pub struct FunctionOutputIndex {
    pub output: EClassIndex,
}

impl FunctionOutputIndex {
    pub fn new() -> Self {
        FunctionOutputIndex {
            output: EClassIndex::new(),
        }
    }
}

/// Per-function argument index: one EClassIndex per argument position.
#[derive(Clone, Debug)]
pub struct FunctionArgIndex {
    pub args: Vec<EClassIndex>,
}

impl FunctionArgIndex {
    pub fn new(arity: usize) -> Self {
        FunctionArgIndex {
            args: (0..arity).map(|_| EClassIndex::new()).collect(),
        }
    }
}

/// The egraph datastructure that keeps track of terms, equalities and parents
pub struct Egraph {
    pub context: Context,
    /// map from u64 to Terms (default: all terms are None, two passes go from Uninitialized to Some, todo (amar): clean this up)
    pub terms_list: Vec<TermOption>,
    /// map from vertices (u64) -> ProofForestEdge
    pub proof_forest: Vec<ProofForestEdge>, // u64 -> ProofForestEdge [t <- ]
    /// keeps track of a stack of "edges" to backtrack on
    pub proof_forest_backtrack_stack: Vec<(usize, ProofForestEdge, u64, ProofForestEdge)>,
    /// this is a map from terms (u64) -> (term in the same egraph, predecesssor of term in same egraph)
    pub predecessors: Vec<DeterministicHashMap<u64, Predecessor>>, // u64 -> Vec<Predecessor> TODO: there might be a better way to do this
    /// number to keep track of the current hash
    pub predecessor_hash: u64,
    /// mapping from levels -> corresponding hash
    pub predecessor_level: Vec<u64>, // u64 -> hash (u64)
    /// shortcut to prevent recomputing assertions from literals
    pub assertions: Vec<Assertion>,
    /// this is a list of quantifiers
    pub quantifiers: Vec<Quantifier>,
    /// Append-only raw log of function applications: F -> Vec<(term_uid, arg_uids)>.
    /// Never modified after insertion; used by the traditional (non-datalog) matcher.
    pub function_entries: DeterministicHashMap<String, DeterministicHashMap<u64, Vec<u64>>>,
    /// Canonical output index: F -> FunctionOutputIndex (timestamped for semi-naive).
    pub function_maps: im::OrdMap<String, FunctionOutputIndex>,
    /// Canonical arg index: F -> FunctionArgIndex (timestamped for semi-naive).
    pub function_indices: im::OrdMap<String, FunctionArgIndex>,
    /// Snapshot stack: saved at each decision level for O(1) backtracking.
    /// Snapshot stack for backtracking canonical indices.
    pub function_index_snapshots: Vec<(
        usize,
        im::OrdMap<String, FunctionOutputIndex>,
        im::OrdMap<String, FunctionArgIndex>,
        usize, // matching_round at snapshot time
    )>,
    /// Current matching round for semi-naive evaluation. Incremented after each matching round.
    /// Entries with timestamp >= matching_round are "delta" (new since last round).
    pub matching_round: usize,
    /// Terms created by quantifier instantiations that need to be re-added to canonical indices
    /// after backtracking. Each entry is (func_name, term_uid, arg_uids).
    /// Cleared at level 0 since all terms are permanent at that point.
    pub terms_added_by_quantifiers: Vec<(String, u64, Vec<u64>)>,
    /// uid for true
    pub true_term: u64,
    /// uid for false
    pub false_term: u64,
    /// a list of quantifier instantiations indexed by the uid of the original quantifier (todo: why do we store a mapping from variable names to terms)
    pub added_instantiations: HashMap<u64, HashSet<DeterministicHashMap<String, Term>>>,
    /// this is a list of skolemized terms
    pub added_skolemizations: DeterministicHashSet<u64>,
    /// keeps track of terms created by quantifier instantiation and their predecessors
    pub predecessors_created_by_quantifiers: DeterministicHashMap<u64, DeterministicHashSet<u64>>,
    /// keeps track of info about datatypes
    pub datatype_info: DatatypeInfo,
    /// keeps track of all constructors (from dt preprocessing pass)
    pub term_constructors: DeterministicHashMap<u64, ConstructorType>, // maps all terms to the correct constructor (using Hashmap because I don't anticipate a lot of datatype terms relative to total # of terms)
    /// if a quantifier instantiates (f t) and t = s, then we want to add  (f.uid(), "f", [t.uid()])
    pub union_to_eclass: DeterministicHashSet<(u64, String, Vec<u64>)>, // todo: use identifier instead of String
    /// remember pairs of terms for which we have learnt  x = y \/ x > y \/ x < y
    pub nelson_oppen_ineq_literals: HashSet<(u64, u64)>,
    /// remember terms for which we have learnt datatype axioms
    pub datatype_axioms_applied: HashSet<u64>,
    /// user flag for whether to instantiate some datatype axioms lazily
    pub lazy_dt: bool,
    /// keeping track of arithmetic terms for theory combination (todo: might be easier just to keep track of arithmetic roots, but thats way more complicated)
    pub arithmetic_terms: Vec<u64>,
    /// user flag for whether certain optimizations for ddsmt are turned on (WARNING: this is buggy and should not be used for real queries)
    pub ddsmt: bool,
    /// user flag for whether we should skolemize eagerly
    pub eager_skolem: bool,
    /// user flag for whether to enable egglog-style relational (datalog) pattern matching
    pub datalog: bool,
    /// all flattened relational atoms from quantifier patterns (only populated when datalog is enabled)
    pub flat_atoms: DeterministicHashSet<FlatAtom>,
    /// for each quantifier (by uid), for each multipattern (disjunctive), the flattened atoms (conjunctive)
    pub flat_patterns: DeterministicHashMap<u64, Vec<Vec<FlatAtom>>>,
    /// index from function name to all flat atoms referencing that function (across all quantifiers)
    pub flat_atom_function_index: DeterministicHashMap<String, Vec<FlatAtom>>,
    /// counter for generating fresh variable IDs during pattern flattening
    pub fresh_var_counter: usize,
    /// store CNF cache
    pub cnf_cache: CNFCache,
    /// the current decision level of the SAT solver, useful to keep track for backtracking
    pub decision_level: usize,
}

impl Egraph {
    pub fn new(
        mut context: Context,
        lazy_dt: bool,
        ddsmt: bool,
        eager_skolem: bool,
        datalog: bool,
    ) -> Self {
        let tru = context.get_true();
        let fal = context.get_false();
        let datatype_info = DatatypeInfo::from_context(&context);

        Egraph {
            context,
            terms_list: vec![TermOption::None],
            proof_forest: vec![ProofForestEdge::Root {
                size: 1000,
                child: 0,
                disequalities: DeterministicHashMap::new(),
                children: DeterministicHashSet::new(),
            }], // think about whether using a vector or hashmap is better here
            // note: this is an option because if you are a subterm of a quantifier, you are not in the proof forest. TODO: maybe there is a better way to think about this
            proof_forest_backtrack_stack: Vec::new(),
            predecessors: vec![DeterministicHashMap::new()],
            predecessor_hash: 1,
            predecessor_level: vec![1, 1],
            assertions: vec![],
            quantifiers: vec![],
            function_entries: DeterministicHashMap::default(),
            function_maps: im::OrdMap::new(),
            function_indices: im::OrdMap::new(),
            function_index_snapshots: Vec::new(),
            matching_round: 0,
            terms_added_by_quantifiers: Vec::new(),
            true_term: tru.uid(),
            false_term: fal.uid(),
            added_instantiations: HashMap::default(),
            added_skolemizations: DeterministicHashSet::default(),
            predecessors_created_by_quantifiers: DeterministicHashMap::new(),
            datatype_info,
            term_constructors: DeterministicHashMap::new(),
            union_to_eclass: DeterministicHashSet::new(),
            nelson_oppen_ineq_literals: HashSet::new(),
            datatype_axioms_applied: HashSet::new(),
            lazy_dt,
            arithmetic_terms: vec![],
            ddsmt,
            eager_skolem,
            datalog,
            flat_atoms: DeterministicHashSet::new(),
            flat_patterns: DeterministicHashMap::new(),
            flat_atom_function_index: DeterministicHashMap::new(),
            fresh_var_counter: 0,
            cnf_cache: Default::default(),
            decision_level: 0,
        }
    }

    fn cnf_env(&mut self) -> CNFEnv<'_> {
        CNFEnv {
            context: &mut self.context,
            cache: &mut self.cnf_cache,
        }
    }

    /// Returns the u64 corresponding to a given lit with the correct polarity
    pub fn get_u64_from_lit_with_polarity(&self, lit: i32) -> (u64, bool) {
        if let Some(num) = self.cnf_cache.var_map_reverse.get(&lit) {
            (*num, true)
        } else if let Some(num) = self.cnf_cache.var_map_reverse.get(&-lit) {
            (*num, false)
        } else {
            panic!(
                "Term {} not found in terms_list {:?}\n We also have proof_forest {:?}",
                lit, self.terms_list, self.proof_forest
            );
        }
    }

    pub fn get_lit_from_u64(&self, num: u64) -> i32 {
        debug_println!(
            6,
            0,
            "We are in get_lit_from_u64 with num {} and var_map {:?}",
            num,
            self.cnf_cache.var_map
        );
        debug_println!(5, 0, "We have the term {}", self.get_term(num));
        *self.cnf_cache.var_map.get(&num).unwrap()
    }

    pub fn get_lit_from_u64_safe(&self, num: u64) -> Option<i32> {
        self.cnf_cache.var_map.get(&num).cloned()
    }

    pub fn get_term(&self, num: u64) -> Term {
        debug_println!(6, 0, "here3 with {}", num);
        self.terms_list[num as usize].clone().unwrap()
    }

    pub fn get_term_safe(&self, num: u64) -> TermOption {
        if self.terms_list.len() <= num as usize {
            TermOption::None
        } else {
            self.terms_list[num as usize].clone()
        }
    }

    pub fn get_term_from_lit(&mut self, lit: i32) -> Term {
        debug_println!(
            5,
            0,
            "We are in get_term_from_lit with lit {} and var_map_reverse {:?}",
            lit,
            self.cnf_cache.var_map_reverse
        );
        if let Some(num) = self.cnf_cache.var_map_reverse.get(&lit) {
            debug_println!(6, 0, "before5");
            self.get_term(*num)
        } else {
            let num = self.cnf_cache.var_map_reverse.get(&-lit).unwrap();
            debug_println!(6, 0, "before6");
            self.context.not(self.get_term(*num))
        }
    }

    pub fn get_term_from_lit_safe(&mut self, lit: i32) -> Option<Term> {
        debug_println!(
            7,
            0,
            "We are in get_term_from_lit with lit {} and var_map_reverse {:?}",
            lit,
            self.cnf_cache.var_map_reverse
        );
        if let Some(num) = self.cnf_cache.var_map_reverse.get(&lit) {
            debug_println!(6, 0, "before7");
            Some(self.get_term(*num))
        } else if let Some(num) = self.cnf_cache.var_map_reverse.get(&-lit) {
            debug_println!(6, 0, "before8");
            Some(self.context.not(self.get_term(*num)))
        } else {
            None
        }
    }

    pub fn get_lit_from_term(&self, term: &Term) -> i32 {
        let num = term.uid();
        debug_println!(
            11,
            0,
            "We are in get_lit_from_term with term {} and num {}",
            term,
            num
        );
        debug_println!(11, 0, "We have the var_map {:?}", self.cnf_cache.var_map);
        *self.cnf_cache.var_map.get(&num).unwrap()
    }

    /// Adds basic information about term to egraph
    fn get_or_insert(
        &mut self,
        term: &Term,
        guard: Option<u64>,
        disequalities: Option<DeterministicHashMap<u64, DisequalTerm>>,
    ) -> bool {
        // returns a vector of literals which do not occur in the propositional skeleton
        debug_println!(
            11,
            0,
            "We are in get_or_insert with term {} adn term id {}",
            term,
            term.uid()
        );
        let num = term.uid();

        // resize terms_list
        while self.terms_list.len() <= num as usize {
            self.terms_list
                .resize(self.terms_list.len() * 2, TermOption::None);
            self.proof_forest.resize(
                self.proof_forest.len() * 2,
                ProofForestEdge::Root {
                    size: 1000,
                    child: 0,
                    disequalities: DeterministicHashMap::new(),
                    children: DeterministicHashSet::new(),
                },
            );
            self.predecessors
                .resize(self.predecessors.len() * 2, DeterministicHashMap::new());
        }

        // if this has already been inserted, then we don't need to do anything
        // TODO: need to add this for non-pattern based stuff
        if let TermOption::Some(i) = &self.terms_list[num as usize] {
            debug_println!(
                22,
                0,
                "We are in get_or_insert with term {} and num {} and the term is already in the terms list {}",
                term,
                num,
                i
            );
            return true;
        }

        // otherwise, we can add the term
        debug_println!(22, 0, "Adding {} into with num {} terms list", term, num);
        self.terms_list[num as usize] = TermOption::Some(term.clone());

        // if the term is an ITE where the boolean is true or false, then we need to merge immediately
        // todo: I don't know if this is actually necessary (also these )
        // if let Ite(b, _, _) = term.repr() {
        //     if b.uid() == self.true_term {
        //          debug_println!(
        //             5,
        //             0,
        //             "We are in ITE get_or_insert with term {} and num {} and b true",
        //             term,
        //             num
        //         );
        //         let proof_parent = ProofForestEdge::Equality {
        //             size: 0,
        //             term: None,
        //             parent: 0,
        //             child: 0,
        //             disequalities: DeterministicHashMap::new(),
        //             level: 0,
        //             hash: 0,
        //             children: DeterministicHashSet::new()
        //         }; // the parent is None, since this is justified by b = True
        //         union(num, self.true_term, self, proof_parent, 0, true, false);
        //     } else if b.uid() == self.false_term {
        //          debug_println!(
        //             5,
        //             0,
        //             "We are in ITE get_or_insert with term {} and num {} and b false",
        //             term,
        //             num
        //         );
        //         let proof_parent = ProofForestEdge::Equality {
        //             size: 0,
        //             term: None,
        //             parent: 0,
        //             child: 0,
        //             disequalities: DeterministicHashMap::new(),
        //             level: 0,
        //             hash: 0,
        //             children: DeterministicHashSet::new()
        //         }; // the parent is None, since this is justified by b = False
        //         union(num, self.false_term, self, proof_parent, 0, true, false);
        //     }
        // };

        let new_disequalities = disequalities.unwrap_or_default();

        self.proof_forest[num as usize] = ProofForestEdge::Root {
            size: 1,
            disequalities: new_disequalities,
            child: 0,
            children: DeterministicHashSet::new(),
        };
        // }

        // inserting the term into the list of functions
        if let App(func, subterms, ..) = term.repr() {
            debug_println!(
                22,
                0,
                "We are adding the function {} with subterms {:?}",
                func,
                subterms
            );
            let subterms_u64 = subterms.iter().map(|t| t.uid()).collect::<Vec<_>>();
            let func_str = func.to_string();
            // Append to raw log (used by traditional matcher)
            self.function_entries
                .entry(func_str.clone())
                .or_default()
                .insert(num, subterms_u64.clone());
            if self.datalog {
                self.insert_into_canonical_indices(func_str, num, &subterms_u64);
            }
        };

        // inserting the ite term into the list of functions
        if let Ite(b, t1, t2) = term.repr() {
            let subterms = vec![b, t1, t2];
            debug_println!(5, 0, "We are adding the ite subterms {:?}", subterms);
            let subterms_u64 = subterms.iter().map(|t| t.uid()).collect::<Vec<_>>();
            self.function_entries
                .entry("ite".to_string())
                .or_default()
                .insert(num, subterms_u64.clone());
            if self.datalog {
                self.insert_into_canonical_indices("ite".to_string(), num, &subterms_u64);
            }
        };

        if let Constant(name, _) = term.repr() && self.datalog {
            debug_println!(24, 0, "Indexing Constant '{}' uid={} into canonical indices", name, num);
            self.function_entries
                .entry(name.to_string())
                .or_default()
                .insert(num, vec![]);
            self.insert_into_canonical_indices(name.to_string(), num, &vec![]);
            // Track for re-insertion after backtrack (zero-arg, so empty arg list)
            self.terms_added_by_quantifiers.push((name.to_string(), num, vec![]));
        }

        if let Global(name, _) = term.repr() && self.datalog {
            debug_println!(24, 0, "Indexing Global '{}' uid={} into canonical indices", name, num);
            self.function_entries
                .entry(name.to_string())
                .or_default()
                .insert(num, vec![]);
            self.insert_into_canonical_indices(name.to_string(), num, &vec![]);
            // Track for re-insertion after backtrack (zero-arg, so empty arg list)
            self.terms_added_by_quantifiers.push((name.to_string(), num, vec![]));
        }

        // TODO: inserting the term if it is a quantifier
        // TODO: there is a weird issue where quantifiers dont get added normally
        if let Exists(sorted_vars, middle_term) | Forall(sorted_vars, middle_term) = term.repr() {
            if let Some(g) = guard {
                debug_println!(
                    6,
                    0,
                    "We are adding the guard {} for quantifier {}",
                    self.get_term(g),
                    term
                );
            }
            if let Annotated(inner_term, attrs) = middle_term.repr() {
                // assert! (attrs.len() == 1); // TODO: we don't support triggers with > 1 multipattern yet
                let mut triggers = vec![];
                let mut trigger_ids = vec![];

                for attr in attrs.iter() {
                    if let Attribute::Pattern(s_exprs) = attr {
                        // assert!(s_exprs.len()==1, "{} has a multi-pattern", term);
                        trigger_ids.push(s_exprs.iter().map(|p| p.uid()).collect());
                        triggers.push(s_exprs);
                    }
                }

                // requires that every variable occurs in every pattern
                let variables: Vec<String> = sorted_vars.iter().map(|x| x.0.to_string()).collect();
                check_quantifier_validity(&triggers, &variables, term);

                let polarity = if let Forall(..) = term.repr() {
                    Universal
                } else {
                    Existential
                };

                self.quantifiers.push(Quantifier {
                    triggers: trigger_ids,
                    variables: variables.clone(),
                    body: inner_term.uid(),
                    id: term.uid(),
                    guard,
                    polarity,
                    skolemized: false,
                    needs_full_pass: true,
                });

                if self.datalog {
                    let trigger_refs: Vec<Vec<&Term>> =
                        triggers.iter().map(|mp| mp.iter().collect()).collect();
                    let compiled = datalogmatch::compile_multipatterns(
                        &trigger_refs,
                        &variables,
                        &mut self.fresh_var_counter,
                    );
                    for multipattern_atoms in &compiled {
                        for atom in multipattern_atoms {
                            self.flat_atoms.insert(atom.clone());
                            self.flat_atom_function_index
                                .entry(atom.func.clone())
                                .or_default()
                                .push(atom.clone());
                        }
                    }
                    self.flat_patterns.insert(term.uid(), compiled);
                    // New quantifier registered — in naive mode all entries are always
                    // examined, so no watermark reset needed.
                }
            } else {
                panic!("We have a quantifier {} without an annotation", term)
            }
        }
        false
    }

    /// For forall terms, adds the subterms to the terms_list but not to any of the other data structures
    fn add_to_terms_list(&mut self, term: &Term) {
        let num = term.uid();

        // resize terms_list
        while self.terms_list.len() <= num as usize {
            self.terms_list
                .resize(self.terms_list.len() * 2, TermOption::None);
            self.proof_forest.resize(
                self.proof_forest.len() * 2,
                ProofForestEdge::Root {
                    size: 1000,
                    child: 0,
                    disequalities: DeterministicHashMap::new(),
                    children: DeterministicHashSet::new(),
                },
            );
            self.predecessors
                .resize(self.predecessors.len() * 2, DeterministicHashMap::new());
        }

        // if this has already been inserted, then we don't need to do anything
        match self.terms_list[num as usize] {
            TermOption::Some(_) => return,
            TermOption::Uninitialized(_) => return,
            _ => {}
        }

        // otherwise, we can add the term as uninitialized. Thus, if the quantifier gets instantiated, we will add it to the terms list
        self.terms_list[num as usize] = TermOption::Uninitialized(term.clone());

        // adding in the subterms
        let (_, subterms) = get_subterms(term);
        for subterm in &subterms {
            self.add_to_terms_list(subterm);
        }
    }

    /// This function takes in a term_num, func, subterms
    /// term_num corresponds to the term with
    /// func applied to subterms
    /// if any of the predecessors of first element in subterms are equivalent (i.e. has the same function
    /// and all of its subterms are equal to the subterms of term_num), then
    /// we union term_num with that predecessors
    /// Used when a term is learned at level > 0 because of quantifier instantiation or datatype axiom
    pub fn find_and_union_to_eclass(&mut self, term_num: u64, func: String, subterms: Vec<u64>) {
        let subterm_num = subterms[0];
        let subterm_root = self.find(subterm_num);
        debug_println!(
            16,
            0,
            "TRYING ECLASS: with term_num {}, term {}, function {}, subterm {}, subterm_root {}",
            term_num,
            self.get_term(term_num),
            func,
            self.get_term(subterm_num),
            self.get_term(subterm_root)
        );

        let subterm_root_predecessor = &self.predecessors[subterm_root as usize].clone(); // need to clone here because I mutably borrow later

        debug_println!(
            16,
            0,
            "We have the predecessors of the subterm root {} with term {} as",
            subterm_root,
            self.get_term(subterm_root),
        );
        for pred_key in subterm_root_predecessor.keys() {
            debug_println!(16, 4, "{}", self.get_term(*pred_key),);
        }

        // enumerate through all of the predecessors of the root of the first subterm, and see if any of them are equivalent to term_num, and if so, union them
        for (pred_key, pred) in subterm_root_predecessor {
            debug_println!(6, 0, "before9");
            // if the predecessor is not valid, then we can remove it from the predecessors list (this can happen because of backtracking) and continue
            if !self.valid_hash(pred.hash, pred.level) {
                self.predecessors[subterm_root as usize].remove(pred_key);
                debug_println!(
                    16,
                    1,
                    "We removed predecessor {} with inner term {} because of invalid hash {} at level {}",
                    self.get_term(*pred_key),
                    self.get_term(pred.inner_term),
                    pred.hash,
                    pred.level
                );
                continue;
            }
            debug_println!(
                16,
                0,
                "We have subterm_root_predecessor {} with inner_term {}",
                self.get_term(*pred_key),
                self.get_term(pred.inner_term)
            );
            let pred_term = self.get_term(*pred_key);
            let (pred_func, pred_subterms) = get_subterms(&pred_term);
            // we can see if the predecessors has the same function name and the same number of subterms
            // if it does we can check if all of the subterms are equal.
            if func == pred_func && pred_subterms.len() == subterms.len() {
                let mut equal = true;
                let mut congruence_pairs = vec![];
                // check if all of the subterms are equal. If they are, then we can union term_num with the predecessor
                for (pred_subterm, subterm) in pred_subterms.iter().zip(subterms.iter()) {
                    let (pred_subterm_uid, subterm_uid) = (pred_subterm.uid(), *subterm);
                    let (subterm_equal, subterm_level, subterm_hash) =
                        self.check_equal(pred_subterm_uid, subterm_uid);
                    debug_println!(
                        16,
                        4,
                        "We are checking the equality of {} and {}, we get equal {} at level {} and hash {}",
                        self.get_term(pred_subterm_uid),
                        self.get_term(subterm_uid),
                        subterm_equal,
                        subterm_level,
                        subterm_hash
                    );
                    if !subterm_equal {
                        equal = false;
                        break;
                    }

                    congruence_pairs.push((pred_subterm_uid, subterm_uid));
                }
                if equal {
                    let equality = ProofForestEdge::Congruence {
                        pairs: congruence_pairs.clone(),
                        size: 0,
                        parent: term_num,
                        child: *pred_key,
                        disequalities: DeterministicHashMap::new(),
                        level: self.decision_level,
                        hash: self.predecessor_hash,
                        children: DeterministicHashSet::new(),
                    };
                    debug_println!(
                        16,
                        0,
                        "In eclass: We are unioning {} and {} with equality {:?}",
                        self.get_term(term_num),
                        self.get_term(*pred_key),
                        equality
                    );
                    union(
                        term_num,
                        *pred_key,
                        self,
                        equality,
                        self.decision_level,
                        false,
                        true,
                    );
                }
            }
        }
    }

    // Inserts the predecessor into egraph (for instance f(x) for x)
    // TODO: I handle the => subcase (to add guards) and the forall subcase (to avoid adding predecessors) separately, so that I don't need to
    pub fn insert_predecessor(
        &mut self,
        term: &Term,
        parent: Option<u64>,
        guard: Option<u64>,
        from_quantifier: bool,
        disequalities: Option<DeterministicHashMap<u64, DisequalTerm>>,
    ) {
        debug_println!(
            27,
            0,
            "We are in insert_predecessor with {} [{}] and from_quantifier {}",
            term,
            term.uid(),
            from_quantifier
        );
        let num = term.uid();

        if let Some(parent_num) = parent {
            let predecessor = Predecessor {
                level: 0,
                hash: 0,
                predecessor: parent_num,
                inner_term: num,
            };

            // this will not insert if something already exists. it should not matter for correctness, but should be slighlty more efficient
            self.predecessors[num as usize]
                .entry(parent_num)
                .or_insert(predecessor);

            if from_quantifier {
                // todo: if a quantifier adds (f t), we need to add (f t) as predecessor for root(t) (todo: need the right backtracking heuristic)
                // todo: also think about whether adding it as a predecessor for root(t) is enough or need to add it as a predecessor multiple places
                // i.e. look at how we do backtracking
                // todo: see if I need subterm_equal here
                let (root, level, hash) = self.find_with_level(num, 0, 0);
                let root_predecessor = Predecessor {
                    level,
                    hash,
                    predecessor: parent_num,
                    inner_term: num,
                };

                match self.predecessors_created_by_quantifiers.get_mut(&num) {
                    Some(parents) => {
                        parents.insert(parent_num);
                    }
                    None => {
                        let mut parents = DeterministicHashSet::new();
                        parents.insert(parent_num);
                        self.predecessors_created_by_quantifiers
                            .insert(num, parents);
                    }
                };

                self.predecessors[root as usize]
                    .entry(parent_num)
                    .or_insert(root_predecessor);
            }
        };

        let previously_inserted = self.get_or_insert(term, guard, disequalities);
        // todo: if previously inserted, then maybe exit here?
        // todo is this valid??
        if previously_inserted {
            return;
        }

        if term.get_sort(&mut self.context).to_string() == "Int" {
            self.arithmetic_terms.push(term.uid())
        }

        // Recursively insert predecessors for all subterms
        let (func, subterms) = get_subterms(term);

        // Track function applications created by quantifier instantiations for re-insertion
        // after backtracking (only when datalog is on).
        if from_quantifier && self.datalog && !subterms.is_empty() {
            let subterms_u64: Vec<u64> = subterms.iter().map(|t| t.uid()).collect();
            self.terms_added_by_quantifiers
                .push((func.to_string(), num, subterms_u64));
        }

        // for forall  and Exists terms, we need to add the subterms to the terms_list but not to any of the other data structures
        if let Exists(_, _) | Forall(_, _) = term.repr() {
            for subterm in subterms {
                debug_println!(
                    22,
                    0,
                    "We are adding the subterm of a forall/exists term {} to the terms list",
                    subterm
                );
                self.add_to_terms_list(subterm);
            }
            // println!("returning");
            return;
        } else {
            debug_println!(22, 0, "not a forall/exists term {}", term);
        }

        // // if a Datatype, we store its constructor
        // // todo: using context here but thats not correct
        // let sort = term.get_sort(self.cnfenv.context); // todo: not sure why this even finds anything hmm
        // let s = sort.to_string();

        // if self.datatype_info.sorts.contains_key(&s) && !self.term_constructors.contains_key(&num) {
        //     if let App(f, _, _) = term.repr() && self.datatype_info.constructors.contains_key(f.id_str().as_str()) {
        //         // println!("happens1 for term {}", term);
        //         let ctor_symbol =  self.cnfenv.context.allocate_string(f.to_string());// egraph.cnfenv.context.get_symbol_str(&ctor_name)
        //         let is_symbol = self.cnfenv.context.allocate_str("is"); // todo: maybe this should have allocate_symbol instead??
        //         let tester_identifier = Identifier {
        //             symbol: is_symbol,
        //             indices: vec![Index::Symbol(ctor_symbol)],
        //         };
        //         let tester_qid : QualifiedIdentifier = yaspar_ir::ast::alg::QualifiedIdentifier(tester_identifier, None); // todo: not sure if I actually need a type here
        //         // Create the tester application: ((_ is ConstructorName) term)
        //         let bool_sort = self.cnfenv.context.bool_sort();
        //         let tester_term = self.cnfenv.context.app(tester_qid, vec![term.clone()], Some(bool_sort));
        //         self.term_constructors.insert(num, ConstructorType::Constructor { name: f.to_string(), tester_term, hash: 0, level: 0 });
        //     } else {
        //         // println!("happens2 for term {}", term);
        //         self.term_constructors.insert(num, ConstructorType::Uninitialized);
        //     }
        // } else {
        //     // println!("doesnt happen for term {} with sort {}", term, sort);
        //     // println!("We have the sorts {:?}", self.datatype_info.sorts.keys());
        // }

        // kindve hacky way to handle the cause with (=> A (forall (x) B)). We want to keep A as a guard for the quantifier, so that if we instantiate, the quantifier A becomes "active"
        // also because of nnf, we are adding this
        // todo: delete this and make sure it doesn't negatively affect anything
        // if let Or(terms) = term.repr()
        //     && terms.len() == 2
        //     && let Not(t1) = terms[0].repr()
        // {
        //     let t2 = &terms[1];
        //      debug_println!(
        //         6,
        //         0,
        //         "We actually have an implies with t1 {} and t2 {}",
        //         t1,
        //         t2
        //     );
        //     self.insert_predecessor(&terms[0], Some(num), None, from_quantifier, None);
        //     self.insert_predecessor(t2, Some(num), Some(t1.uid()), from_quantifier, None);
        //     return;
        // }

        // if something is distinct, we add it as disequalities
        // if let Distinct(terms) = term.repr() {
        //     for term in terms {
        //         let h = DeterministicHashMap::new();
        //         for t in terms {
        //             if t != term {
        //                 let disequal_term =
        //                     DisequalTerm { term: (), level: 0, diseq_lit: (), hash: 0, original_disequality: () };
        //                 h.insert(t.uid(), disequal_term);
        //             }
        //             self.insert_predecessor(term, Some(num), None, from_quantifier, Some(h));
        //         }
        //     }
        // }

        // if we don't hit on either of the two previous cases

        for subterm in &subterms {
            debug_println!(
                22,
                4,
                "We are adding the subterm {} of {} to the terms list (and other things)",
                subterm,
                term
            );
            self.insert_predecessor(subterm, Some(num), None, from_quantifier, None);
        }

        // if a quantifier instantiates (f t) and t = s, then we want to add (f t) =  (f s)
        if from_quantifier && !subterms.is_empty() && !previously_inserted {
            let subterms_cloned: Vec<u64> = subterms.iter().map(|x| x.uid()).collect();
            self.find_and_union_to_eclass(num, func.to_string(), subterms_cloned.clone());
            self.union_to_eclass
                .insert((num, func.to_string(), subterms_cloned));
        }
    }

    // Not 100% sure if we need these because we can always look things up with find

    // /// After merging two e-classes (old_root → new_root), update function_indices so that
    // /// all entries previously keyed under old_root are moved to new_root.
    // pub fn merge_function_indices(&mut self, old_root: u64, new_root: u64) {
    //     for indices in self.function_indices.values_mut() {
    //         for pos_idx in indices.iter_mut() {
    //             if let Some(terms) = pos_idx.remove(&old_root) {
    //                 pos_idx.entry(new_root).or_default().extend(terms);
    //             }
    //         }
    //     }
    // }

    // /// Rebuild function_indices from scratch using the current union-find structure.
    // /// Should be called after backtracking to restore index consistency.
    // pub fn rebuild_function_indices(&mut self) {
    //     self.function_indices.clear();
    //     let entries: Vec<(String, u64, Vec<u64>)> = self
    //         .function_maps
    //         .iter()
    //         .flat_map(|(name, terms)| {
    //             terms
    //                 .iter()
    //                 .map(|(term_id, arg_ids)| (name.clone(), *term_id, arg_ids.clone()))
    //         })
    //         .collect();
    //     for (func_name, term_id, arg_ids) in entries {
    //         let arity = arg_ids.len();
    //         let eclasses: Vec<u64> = arg_ids.iter().map(|&a| self.find(a)).collect();
    //         let indices = self
    //             .function_indices
    //             .entry(func_name)
    //             .or_insert_with(|| vec![DeterministicHashMap::new(); arity]);
    //         assert_eq!(indices.len(), arity);
    //         for (i, eclass) in eclasses.into_iter().enumerate() {
    //             indices[i].entry(eclass).or_default().push(term_id);
    //         }
    //     }
    // }

    /// Insert a function application into the canonical output index (function_maps)
    /// and the canonical arg index (function_indices).
    pub fn insert_into_canonical_indices(&mut self, func: String, term_uid: u64, arg_uids: &[u64]) {
        let output_root = self.find(term_uid);
        let arg_roots: Vec<u64> = arg_uids.iter().map(|&a| self.find(a)).collect();
        let arity = arg_uids.len();
        let stamp = self.matching_round;
        // Insert into function_maps (output index)
        self.function_maps
            .entry(func.clone())
            .or_insert_with(FunctionOutputIndex::new)
            .output
            .insert(output_root, stamp, term_uid);
        // Insert into function_indices (arg index)
        let arg_idx = self
            .function_indices
            .entry(func)
            .or_insert_with(|| FunctionArgIndex::new(arity));
        if arg_idx.args.len() == arity {
            for (i, &arg_root) in arg_roots.iter().enumerate() {
                arg_idx.args[i].insert(arg_root, stamp, term_uid);
            }
        }
    }

    /// Merge entries in function_maps and function_indices from old_root into new_root.
    /// Called during union when two e-classes are merged.
    pub fn merge_function_index_roots(&mut self, old_root: u64, new_root: u64) {
        let stamp = self.matching_round;
        // Merge output index entries
        let func_keys: Vec<String> = self.function_maps.keys().cloned().collect();
        for func in func_keys {
            let func_idx = self.function_maps.get_mut(&func).unwrap();
            func_idx.output.merge_roots(old_root, new_root, stamp);
        }
        // Merge arg index entries
        let func_keys: Vec<String> = self.function_indices.keys().cloned().collect();
        for func in func_keys {
            let arg_idx = self.function_indices.get_mut(&func).unwrap();
            for eclass_idx in arg_idx.args.iter_mut() {
                eclass_idx.merge_roots(old_root, new_root, stamp);
            }
        }
    }

    /// Save a snapshot of the canonical indices at the given decision level.
    /// If a snapshot already exists at this level (e.g., level 0 may be re-entered),
    /// we update it with the current state.
    pub fn snapshot_function_indices(&mut self, level: usize) {
        if let Some((snap_level, _, _, _)) = self.function_index_snapshots.last()
            && *snap_level == level
        {
            let last = self.function_index_snapshots.last_mut().unwrap();
            last.1 = self.function_maps.clone();
            last.2 = self.function_indices.clone();
            last.3 = self.matching_round;
            return;
        }
        self.function_index_snapshots.push((
            level,
            self.function_maps.clone(),
            self.function_indices.clone(),
            self.matching_round,
        ));
    }

    /// Restore the canonical indices to the snapshot at the given decision level,
    /// then re-insert terms that were added by quantifier instantiations.
    pub fn restore_function_indices(&mut self, level: usize) {
        // Pop snapshots until we find the right level
        while let Some((snap_level, _, _, _)) = self.function_index_snapshots.last() {
            if *snap_level > level {
                self.function_index_snapshots.pop();
            } else {
                break;
            }
        }
        if let Some((snap_level, snap_maps, snap_indices, snap_round)) =
            self.function_index_snapshots.last()
            && *snap_level == level
        {
            self.function_maps = snap_maps.clone();
            self.function_indices = snap_indices.clone();
            self.matching_round = *snap_round;
        }
        // Re-insert terms that were created by quantifier instantiations.
        // These terms are permanent in the egraph but were added after the snapshot,
        // so they need to be re-added to the restored canonical indices.
        let terms_to_read: Vec<(String, u64, Vec<u64>)> = self.terms_added_by_quantifiers.clone();
        for (func, term_uid, arg_uids) in terms_to_read {
            self.insert_into_canonical_indices(func, term_uid, &arg_uids);
        }
        // Clear at level 0 since everything is permanent
        if level == 0 {
            self.terms_added_by_quantifiers.clear();
        }
    }

    // FIND operation for union-find
    // lazy find, keep finding the representative until you get to something that is a representative of itself
    // design decision: I do not implement path compression. I could, but would make recovering proof much harder
    pub fn find(&self, x: u64) -> u64 {
        let p = &self.proof_forest[x as usize];
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
            self.get_term(t1),
            self.get_term(t2),
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
            self.get_term(t)
        );
        let t_disequalities = &self.proof_forest[t as usize].disequalities();
        debug_println!(19, 2, "We have t_disequalities {:?}", t_disequalities);

        // TODO: should not need to sort disequalities here if we are using a deterministic hashmap
        let sorted_disequalities: Vec<_> = t_disequalities.iter().collect();
        // sorted_disequalities.sort_by_key(|(key, _)| **key);

        for (key, disequality) in sorted_disequalities {
            if !self.valid_hash(disequality.hash, disequality.level) {
                debug_println!(
                    19,
                    0,
                    "We are skipping disequality with {}, disequality: {:?} because it is not at the same level does not have key {}",
                    self.get_term(disequality.term),
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
                self.get_term(t),
                t,
                self.get_term(root),
                root,
                self.get_term(disequality.term)
            );
            if root == t {
                debug_println!(
                    19,
                    4,
                    "We have found a key {} [{}], disequality {:?} with root: {}, t: {}, disequality.term {} and original_disequality {} != {}",
                    self.get_term(*key),
                    key,
                    disequality,
                    self.get_term(root),
                    self.get_term(t),
                    self.get_term(disequality.term),
                    self.get_term(disequality.original_disequality.0),
                    self.get_term(disequality.original_disequality.1)
                );
                // assert! ((smaller_term == self.find(disequality.original_disequality.0) && larger_term == self.find(disequality.original_disequality.1)) || (smaller_term == self.find(disequality.original_disequality.1) && larger_term == self.find(disequality.original_disequality.0)));
                return Some(disequality.clone());
            }
        }
        None
    }

    /// Set the terms corresponding to x and y equal in egraph
    pub fn make_eq(&mut self, x: u64, y: u64) -> i32 {
        debug_println!(5, 0, "We are in make_eq with x {} and y {}", x, y);

        if (x == self.false_term && y == self.true_term)
            || (x == self.true_term && y == self.false_term)
        {
            debug_println!(
                5,
                0,
                "We are in make_eq with x [{}] false and y [{}] true or x [{}] true and y [{}] false",
                self.get_term(x),
                self.get_term(y),
                self.get_term(x),
                self.get_term(y)
            );
            self.get_lit_from_u64(self.false_term)
        } else if (x == self.true_term && y == self.true_term)
            || (x == self.false_term && y == self.false_term)
        {
            debug_println!(
                5,
                0,
                "We are in make_eq with x [{}] true and y [{}] true or x [{}] false and y [{}] false",
                self.get_term(x),
                self.get_term(y),
                self.get_term(x),
                self.get_term(y)
            );
            self.get_lit_from_u64(self.true_term)
        } else if x == self.true_term {
            debug_println!(5, 0, "We are in make_eq with x true and y {}", y);
            self.get_lit_from_u64(y)
        } else if y == self.true_term {
            debug_println!(5, 0, "We are in make_eq with y true and x {}", x);
            self.get_lit_from_u64(x)
        } else if x == self.false_term {
            debug_println!(5, 0, "We are in make_eq with x false and y {}", y);
            -self.get_lit_from_u64(y)
        } else if y == self.false_term {
            debug_println!(5, 0, "We are in make_eq with y false and x {}", x);
            -self.get_lit_from_u64(x)
        } else {
            debug_println!(6, 0, "before10");
            let eq_term_class = self.context.eq(self.get_term(x), self.get_term(y));
            self.get_lit_from_term(&eq_term_class)
        }
    }

    /// Get the canonical form for some term
    /// For example the canoncial form for f(x, y) is (f, root(x), root(y))  
    /// TODO: I don't support canonical forms for non-app, non-eq terms, non-ite terms, but will have to do that eventually
    pub fn get_canonical_form(
        &mut self,
        term_num: u64,
        _level: usize,
    ) -> Option<(Vec<u64>, String, Vec<u64>)> {
        debug_println!(
            5,
            0,
            "We are in get_canonical_form with term_num {} and term {}",
            term_num,
            self.get_term(term_num)
        );
        debug_println!(6, 0, "before11");
        let term = self.get_term(term_num);
        match term.repr() {
            App(func, subterms, ..) => {
                let subterms_u64 = subterms.iter().map(|t| t.uid()).collect::<Vec<_>>();
                let canonical_subterms = subterms_u64
                    .clone()
                    .into_iter()
                    .map(|t| self.find(t))
                    .collect::<Vec<_>>();
                Some((subterms_u64, func.to_string(), canonical_subterms))
            }
            Eq(left, right) => {
                let canonical_left = self.find(left.uid());
                let canonical_right = self.find(right.uid());
                Some((
                    vec![left.uid(), right.uid()],
                    "=".to_string(),
                    vec![canonical_left, canonical_right],
                ))
            }
            Ite(b, t1, t2) => {
                let canonical_b = self.find(b.uid());
                let canonical_left = self.find(t1.uid());
                let canonical_right = self.find(t2.uid());
                Some((
                    vec![b.uid(), t1.uid(), t2.uid()],
                    "ite".to_string(),
                    vec![canonical_b, canonical_left, canonical_right],
                ))
            }
            _ => None,
        }
    }

    /// Checks if the hash is still valid at the given level
    pub fn valid_hash(&self, hash: u64, level: usize) -> bool {
        debug_println!(
            5,
            0,
            "We are in valid_hash with hash {} and level {}",
            hash,
            level
        );
        hash >= self.predecessor_level[level] || hash == 0 || level == 0 // todo: I added this level ==0 ~> I think this is correct but need to double check to be sure
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
            self.get_term(term),
            self.get_term(new_pred_key),
            new_pred
        );
        // if let Some(original_pred) = self.predecessors[term as usize].get(&new_pred_key) {
        //     if (!self.valid_hash(original_pred.hash, original_pred.level)
        //         || new_pred.level <= original_pred.level)
        //         && self.valid_hash(new_pred.hash, new_pred.level)
        //     {
        //          debug_println!(
        //             11,
        //             0,
        //             "For term {}, we are replacing the predecessor {} [level {}, hash {}] with predecessor {} [level {}, hash {}]",
        //             self.get_term(term),
        //             self.get_term(original_pred.predecessor),
        //             original_pred.level,
        //             original_pred.hash,
        //             self.get_term(new_pred_key),
        //             new_pred.level,
        //             new_pred.hash
        //         );
        //         self.predecessors[term as usize].insert(new_pred_key, new_pred);
        //     }
        // } else {
        //      debug_println!(
        //         11,
        //         0,
        //         "For term {}, we are adding the predecessor {} [level {}, hash {}]",
        //         self.get_term(term),
        //         self.get_term(new_pred_key),
        //         new_pred.level,
        //         new_pred.hash
        //     );
        //     self.predecessors[term as usize].insert(new_pred_key, new_pred);
        // }
        // debug_println!(20, 0, "We have predecessor list size {}", self.predecessors[term as usize].len());
        let (new_pred_hash, new_pred_level) = (new_pred.hash, new_pred.level);
        if let Some(original_pred) = self.predecessors[term as usize].insert(new_pred_key, new_pred)
        {
            if !((!self.valid_hash(original_pred.hash, original_pred.level)
                || new_pred_level <= original_pred.level)
                && self.valid_hash(new_pred_hash, new_pred_level))
            {
                // if the old predecessor was valid, we want to keep it
                self.predecessors[term as usize].insert(new_pred_key, original_pred);
            } else {
                debug_println!(
                    11,
                    0,
                    "For term {}, we are replacing the predecessor {} [level {}, hash {}] with predecessor {} [level {}, hash {}]",
                    self.get_term(term),
                    self.get_term(original_pred.predecessor),
                    original_pred.level,
                    original_pred.hash,
                    self.get_term(new_pred_key),
                    new_pred_level,
                    new_pred_hash
                );
            }
        } else {
            debug_println!(
                11,
                0,
                "For term {}, we are adding the predecessor {} [level {}, hash {}]",
                self.get_term(term),
                self.get_term(new_pred_key),
                new_pred_level,
                new_pred_hash
            );
        }
    }

    pub fn check_for_recursive_datatypes(&self) -> Option<Str> {
        self.datatype_info
            .contains_recursive_datatype(&self.context)
    }
}

impl HasArena for Egraph {
    #[inline]
    fn arena(&mut self) -> &mut Arena {
        self.context.arena()
    }
}

impl<T> CNFConversion<Egraph> for T
where
    T: for<'a> CNFConversion<CNFEnv<'a>>,
{
    fn cnf_tseitin(&self, env: &mut Egraph) -> Formula {
        self.cnf_tseitin(&mut env.cnf_env())
    }

    fn nnf(&self, env: &mut Egraph) -> Self {
        self.nnf(&mut env.cnf_env())
    }
}

// check that every variable occurs in each multipattern
// see: https://isabelle.in.tum.de/library/HOL/HOL/SMT.html
// Some SMT solvers support patterns as a quantifier instantiation
// heuristics. Patterns may either be positive terms (tagged by "pat")
// triggering quantifier instantiations -- when the solver finds a
// term matching a positive pattern, it instantiates the corresponding
// quantifier accordingly -- or negative terms (tagged by "nopat")
// inhibiting quantifier instantiations. A list of patterns
// of the same kind is called a multipattern, and all patterns in a
// multipattern are considered conjunctively for quantifier instantiation.
// A list of multipatterns is called a trigger, and their multipatterns
// act disjunctively during quantifier instantiation. Each multipattern
// should mention at least all quantified variables of the preceding
// quantifier block.
fn check_quantifier_validity(triggers: &Vec<&Vec<Term>>, vars: &Vec<String>, term: &Term) {
    for multipattern in triggers {
        let mut contains_var = DeterministicHashMap::new();
        for var in vars {
            contains_var.insert(var.clone(), false);
        }
        for pattern in *multipattern {
            check_quantifier_validity_helper(pattern, &mut contains_var);
        }
        // println!("We have contains_var: {:?}", contains_var);
        for key in contains_var.keys() {
            if !contains_var[key] {
                panic!(
                    "We have variable {} that does not occur in multipattern {:?} for term {}",
                    key, multipattern, term
                );
            }
        }
    }
}

fn check_quantifier_validity_helper(
    term: &Term,
    contains_var: &mut DeterministicHashMap<String, bool>,
) {
    // println!("Checking validity with term {} and contains_var {:?}", term, contains_var);
    match term.repr() {
        Constant(..) | Global(..) => (),
        Local(local) => {
            let local_id = local.symbol.to_string();
            // println!("We have the local_id {}", local_id);
            if let std::collections::btree_map::Entry::Occupied(mut e) =
                contains_var.entry(local_id)
            {
                // println!("We are updating the local_id");
                let _ = Some(e.insert(true));
            }
        }
        App(_, items, _) | And(items) | Or(items) | Xor(items) | Distinct(items) => {
            items
                .iter()
                .for_each(|item| check_quantifier_validity_helper(item, contains_var));
        }
        Eq(t1, t2) => {
            check_quantifier_validity_helper(t1, contains_var);
            check_quantifier_validity_helper(t2, contains_var);
        }
        Not(t) => {
            check_quantifier_validity_helper(t, contains_var);
        }
        Implies(items, t) => {
            check_quantifier_validity_helper(t, contains_var);
            items
                .iter()
                .for_each(|item| check_quantifier_validity_helper(item, contains_var));
        }
        Ite(b, t1, t2) => {
            check_quantifier_validity_helper(b, contains_var);
            check_quantifier_validity_helper(t1, contains_var);
            check_quantifier_validity_helper(t2, contains_var);
        }
        Let(..) | Exists(..) | Forall(..) | Matching(..) | Annotated(..) => {
            panic!("we do not support patterns with {}", term);
        }
    }
}
