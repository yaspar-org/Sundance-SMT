// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! The `SolverState` struct owns the egraph and all solver-level state
//! (CNF cache, quantifiers, datatypes, theory combination, etc.).
//!
//! External code (propagator, main, quantifier instantiation, etc.) interacts
//! with `SolverState`; the egraph is an internal component accessible via
//! `solver_state.egraph`.

use std::collections::{HashMap, HashSet};
use sat_interface::Formula;
use yaspar_ir::ast::alg::CheckIdentifier;
use yaspar_ir::ast::{Arena, Attribute, Context, FetchSort, HasArena, IdentifierKind, Monomorphization, ObjectAllocatorExt, Repr, Str, Term, TermAllocator};
use yaspar_ir::ast::ATerm::*;

use crate::cnf::{CNFCache, CNFConversion, CNFEnv};
use crate::datatypes::axioms::{learn_ctor_selector_clauses, learn_or_not_term_tester_term};
use crate::datatypes::process::DatatypeInfo;
use crate::debug_println;
use crate::egraphs::datastructures::{
    Assertion, ConstructorType, ConstructorType::*, DisequalTerm, Polarity, Quantifier, TermOption,
};
use crate::egraphs::egraph::{Egraph, valid_hash};
use crate::egraphs::proofforest::ProofForestEdge;
use crate::egraphs::unionfind::ProofTracker;
use crate::log::is_important;
use crate::utils::{DeterministicHashMap, DeterministicHashSet};

/// Solver-level state that wraps the egraph with theory-specific bookkeeping.
///
/// For now, the `Context` (term allocator) is accessed via `self.egraph.context`.
/// It will be moved here in a later step.
pub struct SolverState {
    pub context: Context,
    /// The core egraph (union-find, congruence closure, predecessors, backtracking).
    pub egraph: Egraph,

    /// Maps u64 term UIDs to Term objects.
    pub terms_list: Vec<TermOption>,

    /// Cached assertions (equality, disequality, distinct, tester).
    pub assertions: Vec<Assertion>,

    /// Quantifier instances with triggers and guards.
    pub quantifiers: Vec<Quantifier>,

    /// Tracks quantifier instantiations to avoid duplicates.
    pub added_instantiations: HashMap<u64, HashSet<DeterministicHashMap<String, Term>>>,

    /// Tracks skolemized quantifiers.
    pub added_skolemizations: DeterministicHashSet<u64>,

    /// Terms created by quantifier instantiation and their predecessors.
    pub predecessors_created_by_quantifiers: DeterministicHashMap<u64, DeterministicHashSet<u64>>,

    /// Precomputed datatype constructor/selector info.
    pub datatype_info: DatatypeInfo,

    /// Maps terms to their constructor type (for datatype theory).
    pub term_constructors: DeterministicHashMap<u64, ConstructorType>,

    /// Tracks (term, func, subterms) triples for e-class union after quantifier instantiation.
    pub union_to_eclass: DeterministicHashSet<(u64, String, Vec<u64>)>,

    /// Pairs of terms for which we have learnt x = y \/ x > y \/ x < y.
    pub nelson_oppen_ineq_literals: HashSet<(u64, u64)>,

    /// Terms for which datatype axioms have been applied.
    pub datatype_axioms_applied: HashSet<u64>,

    /// Arithmetic terms for Nelson-Oppen theory combination.
    pub arithmetic_terms: Vec<u64>,

    /// Bidirectional mapping: term UID <-> SAT literal.
    pub cnf_cache: CNFCache,

    /// Whether to instantiate some datatype axioms lazily.
    pub lazy_dt: bool,

    /// Whether DDSMT optimizations are on (experimental, buggy).
    pub ddsmt: bool,

    /// Whether to skolemize eagerly.
    pub eager_skolem: bool,
}

impl SolverState {
    /// Create a new SolverState. Takes ownership of the Context and config flags,
    /// creates the inner Egraph using the existing constructor.
    pub fn new(mut context: Context, lazy_dt: bool, ddsmt: bool, eager_skolem: bool) -> Self {
        let tru = context.get_true();
        let fal = context.get_false();
        let egraph = Egraph::new(tru, fal);
        let datatype_info = DatatypeInfo::from_context(&context);


        SolverState {
            context,
            terms_list: vec![TermOption::None],
            assertions: vec![],
            quantifiers: vec![],
            added_instantiations: HashMap::default(),
            added_skolemizations: DeterministicHashSet::default(),
            predecessors_created_by_quantifiers: DeterministicHashMap::new(),
            datatype_info,
            term_constructors: DeterministicHashMap::new(),
            union_to_eclass: DeterministicHashSet::new(),
            nelson_oppen_ineq_literals: HashSet::new(),
            datatype_axioms_applied: HashSet::new(),
            arithmetic_terms: vec![],
            cnf_cache: Default::default(),
            lazy_dt,
            ddsmt,
            eager_skolem,
            egraph,
        }
    }

    pub fn cnf_env(&mut self) -> CNFEnv<'_> {
        CNFEnv {
            context: &mut self.context,
            cache: &mut self.cnf_cache,
        }
    }

    pub fn get_u64_from_lit_with_polarity(&self, lit: i32) -> (u64, bool) {
        if let Some(num) = self.cnf_cache.var_map_reverse.get(&lit) {
            (*num, true)
        } else if let Some(num) = self.cnf_cache.var_map_reverse.get(&-lit) {
            (*num, false)
        } else {
            panic!("Term {} not found in cnf_cache", lit);
        }
    }

    pub fn get_lit_from_u64(&self, num: u64) -> i32 {
        *self.cnf_cache.var_map.get(&num).unwrap()
    }

    pub fn get_lit_from_u64_safe(&self, num: u64) -> Option<i32> {
        self.cnf_cache.var_map.get(&num).cloned()
    }

    pub fn get_term_from_lit(&mut self, lit: i32) -> Term {
        if let Some(num) = self.cnf_cache.var_map_reverse.get(&lit) {
            self.egraph.get_term(*num)
        } else {
            let num = self.cnf_cache.var_map_reverse.get(&-lit).unwrap();
            self.context.not(self.egraph.get_term(*num))
        }
    }

    pub fn get_term_from_lit_safe(&mut self, lit: i32) -> Option<Term> {
        if let Some(num) = self.cnf_cache.var_map_reverse.get(&lit) {
            Some(self.egraph.get_term(*num))
        } else if let Some(num) = self.cnf_cache.var_map_reverse.get(&-lit) {
            Some(self.context.not(self.egraph.get_term(*num)))
        } else {
            None
        }
    }

    pub fn get_lit_from_term(&self, term: &Term) -> i32 {
        let num = term.uid();
        *self.cnf_cache.var_map.get(&num).unwrap()
    }

    pub fn make_eq(&mut self, x: u64, y: u64) -> i32 {
        if (x == self.egraph.false_term && y == self.egraph.true_term)
            || (x == self.egraph.true_term && y == self.egraph.false_term)
        {
            self.get_lit_from_u64(self.egraph.false_term)
        } else if (x == self.egraph.true_term && y == self.egraph.true_term)
            || (x == self.egraph.false_term && y == self.egraph.false_term)
        {
            self.get_lit_from_u64(self.egraph.true_term)
        } else if x == self.egraph.true_term {
            self.get_lit_from_u64(y)
        } else if y == self.egraph.true_term {
            self.get_lit_from_u64(x)
        } else if x == self.egraph.false_term {
            -self.get_lit_from_u64(y)
        } else if y == self.egraph.false_term {
            -self.get_lit_from_u64(x)
        } else {
            let eq_term_class = self.context.eq(self.egraph.get_term(x), self.egraph.get_term(y));
            self.get_lit_from_term(&eq_term_class)
        }
    }

    pub fn get_term(&self, num: u64) -> Term {
        self.egraph.get_term(num)
    }

    pub fn get_term_ref(&self, num: u64) -> &Term {
        self.egraph.get_term_ref(num)
    }

    pub fn get_term_safe(&self, num: u64) -> TermOption {
        self.egraph.get_term_safe(num)
    }

    pub fn check_for_recursive_datatypes(&self) -> Option<Str> {
        self.datatype_info
            .contains_recursive_datatype(&self.context)
    }

    /// Solver-level recursive term registration.
    /// Walks the term tree, does solver-specific bookkeeping at each node
    /// (arithmetic tracking, quantifier registration), then registers each
    /// term in the egraph via register_term.
    pub fn insert_predecessor(
        &mut self,
        term: &Term,
        parent: Option<u64>,
        guard: Option<u64>,
        from_quantifier: bool,
        disequalities: Option<DeterministicHashMap<u64, DisequalTerm>>,
    ) {
        use crate::egraphs::utils::get_subterms;

        let num = term.uid();

        // Arithmetic term tracking
        if term.get_sort(self.context.arena()).to_string() == "Int" {
            if !self.arithmetic_terms.contains(&num) {
                self.arithmetic_terms.push(num);
            }
        }

        // Register this term in the egraph (non-recursive, single term)
        let previously_inserted = self.egraph.register_term(term, parent, from_quantifier, disequalities);
        if previously_inserted {
            return;
        }

        // Quantifier registration: if this term is a forall/exists, parse and register it
        if let Exists(sorted_vars, middle_term) | Forall(sorted_vars, middle_term) = term.repr() {
            if let Annotated(inner_term, attrs) = middle_term.repr() {
                let mut trigger_ids = vec![];

                for attr in attrs.iter() {
                    if let Attribute::Pattern(s_exprs) = attr {
                        trigger_ids.push(s_exprs.iter().map(|p| p.uid()).collect());
                    }
                }

                let variables: Vec<String> = sorted_vars.iter().map(|x| x.0.to_string()).collect();

                let polarity = if let Forall(..) = term.repr() {
                    Polarity::Universal
                } else {
                    Polarity::Existential
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
            }

            // For quantifier terms, add subterms to terms_list only (not as predecessors)
            let (_, subterms) = get_subterms(term);
            for subterm in &subterms {
                self.egraph.add_to_terms_list(subterm);
            }
            return;
        }

        // Recursively insert subterms
        let (func, subterms) = get_subterms(term);
        for subterm in &subterms {
            self.insert_predecessor(subterm, Some(num), None, from_quantifier, None);
        }

        // If from quantifier instantiation, try to find and merge with existing congruent terms
        if from_quantifier && !subterms.is_empty() {
            let subterms_cloned: Vec<u64> = subterms.iter().map(|x| x.uid()).collect();
            self.egraph.find_and_union_to_eclass(num, func.to_string(), subterms_cloned.clone());
            self.egraph.union_to_eclass
                .insert((num, func.to_string(), subterms_cloned));
        }
    }
}

impl HasArena for SolverState {
    fn arena(&mut self) -> &mut Arena {
        self.context.arena()
    }
}

impl<T> CNFConversion<SolverState> for T
where
    T: for<'a> CNFConversion<CNFEnv<'a>>,
{
    fn cnf_tseitin(&self, env: &mut SolverState) -> Formula {
        self.cnf_tseitin(&mut env.cnf_env())
    }

    fn nnf(&self, env: &mut SolverState) -> Self {
        self.nnf(&mut env.cnf_env())
    }
}

// impl Deref for SolverState {
//     type Target = Egraph;

//     fn deref(&self) -> &Egraph {
//         &self.egraph
//     }
// }

// impl DerefMut for SolverState {
//     fn deref_mut(&mut self) -> &mut Egraph {
//         &mut self.egraph
//     }
// }

/// Process a SAT literal assignment through the egraph.
/// This is the solver-level entry point that classifies the literal and
/// dispatches to the appropriate egraph operation (union, disequality, etc.).
pub fn process_assignment(
    lit: i32,
    solver_state: &mut SolverState,
    level: usize,
    fixed: bool,
    from_quantifier: bool,
    reason: Option<ProofForestEdge>,
) -> Option<Vec<Vec<i32>>> {
    let lazy_dt = solver_state.lazy_dt;
    let ddsmt = solver_state.ddsmt;
    debug_println!(2, 0, "Processing literal {:} at level {}", lit, level);
    let sign = lit > 0;

    let term = solver_state.get_term_from_lit(lit.abs());
    debug_println!(24, 1, "Term: {}", term);
    let assertion = find_if_eq_diseq(&term, sign, solver_state, level, fixed);

    let mut tracker = ProofTracker::new();

    if let Some(t) = solver_state.cnf_cache.var_map_reverse.get(&lit) {
        let res = if let Some(r) = reason.clone() {
            r
        } else {
            ProofForestEdge::Equality {
                size: 0,
                term: Some((*t, solver_state.egraph.true_term)),
                parent: 0,
                child: 0,
                disequalities: DeterministicHashMap::new(),
                level,
                hash: solver_state.egraph.predecessor_hash,
                children: DeterministicHashSet::new(),
            }
        };
        debug_println!(
            16,
            0,
            "We are in process_assignment, unioning with true for lit {} and t {} and true_term {}",
            lit,
            t,
            solver_state.egraph.true_term
        );
        let union_result = solver_state.egraph.cc_union(
            *t,
            solver_state.egraph.true_term,
            res,
            level,
            fixed,
            from_quantifier,
        );
        if let Some(conflict) = union_result.conflict {
            let mut model_terms: Vec<i32> = conflict.equalities
                .iter()
                .map(|(a, b)| -solver_state.make_eq(*a, *b))
                .collect();
            model_terms.push(solver_state.make_eq(conflict.disequality.0, conflict.disequality.1));
            return Some(vec![model_terms]);
        }
    }

    if let Some(t) = solver_state.cnf_cache.var_map_reverse.get(&-lit) {
        let res = if let Some(r) = reason.clone() {
            r
        } else {
            ProofForestEdge::Equality {
                size: 0,
                term: Some((*t, solver_state.egraph.false_term)),
                parent: 0,
                child: 0,
                disequalities: DeterministicHashMap::new(),
                level,
                hash: solver_state.egraph.predecessor_hash,
                children: DeterministicHashSet::new(),
            }
        };
        debug_println!(
            16,
            0,
            "We are in process_assignment, unioning with false for lit {} and t {} and false_term {}",
            lit,
            t,
            solver_state.egraph.false_term
        );
        let union_result = solver_state.egraph.cc_union(
            *t,
            solver_state.egraph.false_term,
            res,
            level,
            fixed,
            from_quantifier,
        );
        if let Some(conflict) = union_result.conflict {
            let mut model_terms: Vec<i32> = conflict.equalities
                .iter()
                .map(|(a, b)| -solver_state.make_eq(*a, *b))
                .collect();
            model_terms.push(solver_state.make_eq(conflict.disequality.0, conflict.disequality.1));
            return Some(vec![model_terms]);
        };
    }

    debug_println!("Finished union to True/False");
    let additional_constraints = match assertion {
        Assertion::Tester {
            ctor_name,
            inner_term,
            term,
        } => {
            let dt_sort = inner_term.get_sort(solver_state);
            let _term_lit = solver_state.get_lit_from_term(&term);
            debug_println!(19, 0, "trying to get for the term {}", inner_term);
            match solver_state.term_constructors.get(&inner_term.uid()).unwrap() {
                Constructor {
                    name,
                    tester_term,
                    hash,
                    level,
                } if valid_hash(*hash, *level, &solver_state.egraph.predecessor_level) => {
                    debug_println!(
                        11,
                        2,
                        "We have a valid prior constructor with name {} (our tester name is {})",
                        name,
                        ctor_name
                    );
                    if *name == ctor_name {
                        debug_println!(11, 2, "name == ctor_name");
                        None
                    } else {
                        debug_println!(11, 2, "name != ctor_name");
                        let tester_cnf = learn_or_not_term_tester_term(
                            solver_state,
                            tester_term.clone(),
                            term.clone(),
                            true,
                        );
                        Some(tester_cnf)
                    }
                }
                _ => {
                    solver_state.term_constructors.insert(
                        inner_term.uid(),
                        Constructor {
                            name: ctor_name.clone(),
                            tester_term: term.clone(),
                            level,
                            hash: solver_state.egraph.predecessor_hash,
                        },
                    );

                    if lazy_dt {
                        let dt_name = solver_state.datatype_info.constructors.get(&ctor_name).unwrap();
                        let dt_dec = solver_state.datatype_info.datatypes.get(dt_name).unwrap();
                        let dt_dec = dt_dec
                            .monomorphize(&dt_sort, solver_state.context.arena())
                            .expect("type invariant violation: datatype fails to monomorphize");

                        let ctor = dt_dec
                            .constructors
                            .iter()
                            .find(|ctor| ctor.ctor == ctor_name)
                            .expect("type checking invariance violation: datatypes")
                            .clone();

                        let ctor_selector_clauses: Vec<Vec<i32>> =
                            learn_ctor_selector_clauses(solver_state, &inner_term, &ctor, &dt_sort, true, ddsmt, lazy_dt);
                        Some(ctor_selector_clauses)
                    } else {
                        None
                    }
                }
            }
        }
        Assertion::Equality { t1, t2, level, .. } => {
            debug_println!(
                16,
                0,
                "Merging: {} = {}",
                solver_state.egraph.get_term(t1),
                solver_state.egraph.get_term(t2)
            );

            let reason = if let Some(r) = reason.clone() {
                r
            } else {
                ProofForestEdge::Equality {
                    size: 0,
                    term: Some((t1, t2)),
                    parent: 0,
                    child: 0,
                    disequalities: DeterministicHashMap::new(),
                    level,
                    hash: solver_state.egraph.predecessor_hash,
                    children: DeterministicHashSet::new(),
                }
            };
            let union_result = solver_state.egraph.cc_union(t1, t2, reason, level, fixed, from_quantifier);
            if let Some(conflict) = union_result.conflict {
                let mut model_terms: Vec<i32> = conflict.equalities
                    .iter()
                    .map(|(a, b)| -solver_state.make_eq(*a, *b))
                    .collect();
                model_terms.push(solver_state.make_eq(conflict.disequality.0, conflict.disequality.1));
                Some(vec![model_terms])
            } else {
                None
            }
        }
        Assertion::Disequality {
            t1,
            t2,
            level,
            hash,
        } => {
            debug_println!(
                16,
                0,
                "Adding disequality {} ≠ {} to stack at level {:?} and hash {}",
                solver_state.egraph.get_term(t1),
                solver_state.egraph.get_term(t2),
                level,
                hash
            );
            // debug_println!(10, 0, "{}", solver_state);

            if let Some(negated_model) =
                solver_state.egraph.leastcommonancestor(t1, t2, &mut ProofTracker::new())
            {
                let mut model_terms: Vec<i32> = negated_model
                    .into_iter()
                    .map(|x| -solver_state.make_eq(x.0, x.1))
                    .collect();
                model_terms.push(solver_state.make_eq(t1, t2));
                debug_println!(
                    16,
                    1,
                    "Contradiction found [1]: {:?} [{:?}]",
                    model_terms
                        .iter()
                        .map(|x| solver_state.get_term_from_lit(*x))
                        .collect::<Vec<_>>(),
                    model_terms
                );
                return Some(vec![model_terms]);
            }
            solver_state.egraph.add_disequality(t1, t2, lit, level, hash);
            None
        }
        Assertion::Distinct { terms, level, hash } => {
            for i in 0..terms.len() {
                for j in i + 1..terms.len() {
                    let (t1, t2) = (terms[i], terms[j]);
                    debug_println!(
                        12,
                        0,
                        "Asserting {} and {} are not equal at level {} with hash {}",
                        solver_state.egraph.get_term(t1),
                        solver_state.egraph.get_term(t2),
                        level,
                        hash
                    );
                    if let Some(negated_model) =
                        solver_state.egraph.leastcommonancestor(t1, t2, &mut ProofTracker::new())
                    {
                        let mut model_terms: Vec<i32> = negated_model
                            .into_iter()
                            .map(|x| -solver_state.make_eq(x.0, x.1))
                            .collect();
                        model_terms.push(-lit);
                        debug_println!(
                            7,
                            1,
                            "Contradiction found [1]: {:?} [{:?}]",
                            model_terms
                                .iter()
                                .map(|x| solver_state.get_term_from_lit(*x))
                                .collect::<Vec<_>>(),
                            model_terms
                        );
                        debug_println!(16, 0, "returning negated model {:?}", model_terms);
                        return Some(vec![model_terms]);
                    }
                    solver_state.egraph.add_disequality(t1, t2, lit, level, hash);
                    // debug_println!(11, 0, "{}", solver_state);
                }
            }
            None
        }
        Assertion::Other => None,
    };

    debug_println!(
        4,
        0,
        "We are in process_assignment, checking for contradiction with true_term {} and false_term {}",
        solver_state.egraph.true_term,
        solver_state.egraph.false_term
    );
    if let Some(negated_model) =
        solver_state.egraph.leastcommonancestor(solver_state.egraph.true_term, solver_state.egraph.false_term, &mut tracker)
    {
        let negated_model_terms: Vec<i32> = negated_model
            .into_iter()
            .map(|x| -solver_state.make_eq(x.0, x.1))
            .collect();
        debug_println!(
            24,
            1,
            "Contradiction found [2] (setting true = false): {:?} [{:?}]",
            negated_model_terms
                .iter()
                .map(|x| solver_state.get_term_from_lit(*x))
                .collect::<Vec<_>>(),
            negated_model_terms
        );
        if is_important(7) {
            for lit in negated_model_terms.clone() {
                debug_println!(7, 4, "{}", solver_state.get_term_from_lit(lit));
            }
        }

        return if let Some(mut constraints) = additional_constraints {
            constraints.push(negated_model_terms);
            Some(constraints)
        } else {
            Some(vec![negated_model_terms])
        };
    }

    debug_println!(
        24,
        0,
        "We have the additional constraints {:?}",
        additional_constraints
    );
    additional_constraints
}

/// Classify a term+sign as an assertion type (equality, disequality, tester, etc.)
pub fn find_if_eq_diseq<'a>(
    term: &'a Term,
    sign: bool,
    solver_state: &'a SolverState,
    level: usize,
    fixed: bool,
) -> Assertion {
    let hash = if !fixed { solver_state.egraph.predecessor_hash } else { 0 };
    match term.repr() {
        App(f, t, _)
            if (matches!(f.get_kind(), Some(IdentifierKind::Is(_)))
                || (f.get_kind().is_none() && f.id_str().get().starts_with("is-")))
                && t.len() == 1
                && sign =>
        {
            let ctor_name = if let Some(IdentifierKind::Is(sym)) = f.get_kind() {
                Some(sym.clone())
            } else {
                let name = &f.id_str().get()[3..];
                solver_state
                    .datatype_info
                    .constructors
                    .keys()
                    .find(|k| *k.get() == *name)
                    .cloned()
            };
            if let Some(ctor_name) = ctor_name {
                let inner_term = t[0].clone();
                Assertion::Tester {
                    ctor_name,
                    inner_term,
                    term: term.clone(),
                }
            } else {
                Assertion::Other
            }
        }

        Eq(left, right) => {
            if sign {
                debug_println!(1, 2, "Creating equality assertion");
                Assertion::Equality {
                    t1: left.uid(),
                    t2: right.uid(),
                    level,
                    hash,
                }
            } else {
                debug_println!(1, 2, "Creating disequality assertion");
                Assertion::Disequality {
                    t1: left.uid(),
                    t2: right.uid(),
                    level,
                    hash,
                }
            }
        }
        Distinct(terms) => {
            if sign {
                debug_println!(1, 2, "Creating equality assertion");
                Assertion::Distinct {
                    terms: terms.iter().map(|x| x.uid()).collect(),
                    level,
                    hash,
                }
            } else {
                panic!("We do not currently support the negation of a disstinct")
            }
        }
        Not(inner) => match inner.repr() {
            Eq(left, right) => {
                debug_println!(1, 2, "Creating disequality assertion");
                assert!(sign);
                Assertion::Disequality {
                    t1: left.uid(),
                    t2: right.uid(),
                    level,
                    hash,
                }
            }
            Distinct(_) => {
                panic!("We do not currently support the negation of a distinct")
            }
            _ => {
                debug_println!(0, 2, "Found negation, treating as Other");
                Assertion::Other
            }
        },
        _ => {
            debug_println!(
                0,
                2,
                "Found unsupported operator: {:?}, treating as Other",
                term.repr()
            );
            Assertion::Other
        }
    }
}
