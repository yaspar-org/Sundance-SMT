// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::cnf::{CNFCache, CNFConversion, CNFEnv};
use crate::datatypes::process::DatatypeInfo;
use crate::egraphs::congruence_closure::union;
use crate::egraphs::datastructures::{
    Assertion, ConstructorType, DisequalTerm, Polarity::*, Predecessor, Quantifier, TermOption,
};
use crate::egraphs::proofforest::*;
use crate::egraphs::utils::get_subterms;
use crate::utils::{DeterministicHashMap, DeterministicHashSet};
use sat_interface::Formula;
use std::collections::{HashMap, HashSet};
use std::default::Default;
use std::fmt;
use yaspar_ir::ast::{ATerm::*, Context, FetchSort, ObjectAllocatorExt};
use yaspar_ir::ast::{Attribute, Repr, Term, TermAllocator};

impl fmt::Display for Egraph {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "=== Egraph Summary ===")?;

        // Basic statistics
        writeln!(f, "Proof forest entries: {}", self.proof_forest.len())?;
        writeln!(f, "Predecessor relationships: {}", self.predecessors.len())?;
        writeln!(f, "Assertions: {}", self.assertions.len())?;
        writeln!(f, "Quantifiers: {}", self.quantifiers.len())?;
        writeln!(f, "Function maps: {}", self.function_maps.len())?;

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

        // Function maps
        if !self.function_maps.is_empty() {
            writeln!(f, "\n=== Function Applications ===")?;
            for (func_name, applications) in self.function_maps.iter() {
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

/// The egraph datastructure that keeps track of terms, equalities and parents
pub struct Egraph {
    pub context: Context,
    /// map from u64 to Terms (default: all terms are None, two passes go from Uninitialized to Some, todo (amar): clean this up)
    pub terms_list: Vec<TermOption>,
    /// map from vertices (u64) -> ProofForestEdge
    pub proof_forest: Vec<ProofForestEdge>, // u64 -> ProofForestEdge [t <- ]
    /// keeps track of a stack of "edges" to backtrack on
    pub proof_forest_backtrack_stack: Vec<(usize, ProofForestEdge, u64, ProofForestEdge)>,
    /// the set of terms that have been unioned to the eclass from a quantifier
    pub from_quantifier_backtrack_set:
        DeterministicHashMap<u64, (ProofForestEdge, ProofForestEdge, ProofForestEdge, u64)>, // String, Vec<u64>)>,
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
    /// map from functions (String) -> terms of this function
    pub function_maps: DeterministicHashMap<String, Vec<(u64, Vec<u64>)>>, // maps a function name to a list of terms that are of that function
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
    /// store CNF cache
    pub cnf_cache: CNFCache,
}

impl Egraph {
    pub fn new(mut context: Context, lazy_dt: bool, ddsmt: bool, eager_skolem: bool) -> Self {
        let tru = context.get_true();
        let fal = context.get_false();

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
            from_quantifier_backtrack_set: DeterministicHashMap::default(),
            predecessors: vec![DeterministicHashMap::new()],
            predecessor_hash: 1,
            predecessor_level: vec![1, 1],
            assertions: vec![],
            quantifiers: vec![],
            function_maps: DeterministicHashMap::default(),
            true_term: tru.uid(),
            false_term: fal.uid(),
            added_instantiations: HashMap::default(),
            added_skolemizations: DeterministicHashSet::default(),
            predecessors_created_by_quantifiers: DeterministicHashMap::new(),
            datatype_info: DatatypeInfo::new(),
            term_constructors: DeterministicHashMap::new(),
            union_to_eclass: DeterministicHashSet::new(),
            nelson_oppen_ineq_literals: HashSet::new(),
            datatype_axioms_applied: HashSet::new(),
            lazy_dt,
            arithmetic_terms: vec![],
            ddsmt,
            eager_skolem,
            cnf_cache: Default::default(),
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
            self.function_maps
                .entry(func.to_string())
                .or_default()
                .push((num, subterms_u64));
        };

        // inserting the ite term into the list of functions
        if let Ite(b, t1, t2) = term.repr() {
            let subterms = vec![b, t1, t2];
            debug_println!(5, 0, "We are adding the ite subterms {:?}", subterms);
            let subterms_u64 = subterms.iter().map(|t| t.uid()).collect::<Vec<_>>();
            self.function_maps
                .entry("ite".to_string())
                .or_default()
                .push((num, subterms_u64));
        };

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
                    variables,
                    body: inner_term.uid(),
                    id: term.uid(),
                    guard,
                    polarity,
                    skolemized: false,
                });
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

    pub fn find_and_union_to_eclass(&mut self, term_num: u64, func: String, subterms: Vec<u64>) {
        let subterm_num = subterms[0];
        let subterm_root = self.find(subterm_num);
        debug_println!(
            11,
            0,
            "TRYING ECLASS: with term_num {}, term {}, function {}, subterm {}, subterm_root {}",
            term_num,
            self.get_term(term_num),
            func,
            self.get_term(subterm_num),
            self.get_term(subterm_root)
        );

        // if this is an ite statement, then check if boolean is = true/false and if so union it
        // if func == "ite" {
        //      debug_println!(6, 0, "ECLASS ITE CASE with {}", self.get_term(term_num));
        // assert!(subterms.len() == 3);
        // if self.find(subterms[0]) == self.true_term {
        // union_process_ite(&self.get_term(term_num), self, 0,true);
        // } else if self.find(subterms[0]) == self.false_term {
        //         union_process_ite(&self.get_term(term_num), self, 0, true);
        // }
        // }

        // we don't actually want to have or and and unioned using find_and_union_to_eclass, they will be handled
        // by the SAT solver
        // if we did not skip this it could create an infinite loop
        // todo: I think this might jusst be a bandage on a bigger problem. We may be able to create an infinite loop regardless
        // maybe not I need to think about this harder
        // if func == "or" || func == "and" || func == "not" {
        //     return
        // }

        // // println!("{}", self);
        let subterm_root_predecessor = &self.predecessors[subterm_root as usize].clone(); // need to clone here because I mutably borrow later
        // let mut subterm_root_predecessor_vec = subterm_root_predecessor.iter().collect::<Vec<_>>();
        // subterm_root_predecessor_vec.sort();
        for (pred_key, pred) in subterm_root_predecessor {
            debug_println!(6, 0, "before9");
            if !self.valid_hash(pred.hash, pred.level) {
                self.predecessors[subterm_root as usize].remove(pred_key);
                continue;
            }
            debug_println!(
                11,
                0,
                "We have subterm_root_predecessor {} with inner_term {}",
                self.get_term(*pred_key),
                self.get_term(pred.inner_term)
            );
            let pred_term = self.get_term(*pred_key);
            debug_println!(6, 1, "We have the pred_term {}", pred_term);
            let (pred_func, pred_subterms) = get_subterms(&pred_term);
            debug_println!(
                6,
                1,
                "We have the pred_func {} and pred_subterms {:?}",
                pred_func,
                pred_subterms
            );
            if func == pred_func && pred_subterms.len() == subterms.len() {
                let mut equal = true;
                let mut completely_equal = true;
                let mut congruence_pairs = vec![];
                let (mut max_level, mut max_hash) = (0, 0);
                //  debug_println!(10, 0, "{}", self);
                for (pred_subterm, subterm) in pred_subterms.iter().zip(subterms.iter()) {
                    let (pred_subterm_uid, subterm_uid) = (pred_subterm.uid(), *subterm);
                    // let (pred_root, pred_level, pred_hash) = self.find_with_level(pred_subterm_uid, 0, 0);
                    // let (subterm_root, subterm_level, subterm_hash) = self.find_with_level(subterm_uid, 0, 0);
                    let (subterm_equal, subterm_level, subterm_hash) =
                        self.check_equal(pred_subterm_uid, subterm_uid);
                    debug_println!(
                        11,
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

                    // checking if either of these two paths have a higher level, if they do we can use this as a new level/hash
                    if subterm_level > max_level {
                        (max_level, max_hash) = (subterm_level, subterm_hash);
                    }

                    if pred_subterm_uid != subterm_uid {
                        completely_equal = false;
                    }
                    congruence_pairs.push((pred_subterm_uid, subterm_uid));
                }
                if equal && !completely_equal {
                    // todo: I got rid of this because it was erroring, but not sure how to prevent redundancies otherwise
                    // if self.from_quantifier_backtrack_set.contains_key(&term_num) {
                    //     panic!(
                    //         "we should not be considering a term that already exists {} and func {}",
                    //         self.get_term(term_num),
                    //         func
                    //     );
                    // }
                    let equality = ProofForestEdge::Congruence {
                        pairs: congruence_pairs.clone(),
                        size: 0,
                        parent: term_num,
                        child: *pred_key,
                        disequalities: DeterministicHashMap::new(),
                        level: max_level,
                        hash: max_hash,
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
                    // having fixed as true here since these get backtracked on in the special case using from_quantifier_backtrack_set
                    union(term_num, *pred_key, self, equality, max_level, false, true);
                    break;
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
            22,
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
    ) -> Option<(Vec<u64>, (String, Vec<u64>))> {
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
                Some((subterms_u64, (func.to_string(), canonical_subterms)))
            }
            Eq(left, right) => {
                let canonical_left = self.find(left.uid());
                let canonical_right = self.find(right.uid());
                Some((
                    vec![left.uid(), right.uid()],
                    ("=".to_string(), vec![canonical_left, canonical_right]),
                ))
            }
            Ite(b, t1, t2) => {
                let canonical_b = self.find(b.uid());
                let canonical_left = self.find(t1.uid());
                let canonical_right = self.find(t2.uid());
                Some((
                    vec![b.uid(), t1.uid(), t2.uid()],
                    (
                        "ite".to_string(),
                        vec![canonical_b, canonical_left, canonical_right],
                    ),
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
        App(_, items, _) | And(items) | Or(items) | Distinct(items) => {
            // println!("We are in app case with items {:?}", items);
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
