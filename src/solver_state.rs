// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! The `SolverState` struct owns the egraph and all solver-level state
//! (CNF cache, quantifiers, datatypes, theory combination, etc.).
//!
//! External code (propagator, main, quantifier instantiation, etc.) interacts
//! with `SolverState`; the egraph is an internal component accessible via
//! `solver_state.egraph`.

use std::collections::{HashMap, HashSet};

use yaspar_ir::ast::alg::CheckIdentifier;
use yaspar_ir::ast::{Context, FetchSort, HasArena, IdentifierKind, Monomorphization, Repr, Term};
use yaspar_ir::ast::ATerm::*;

use crate::cnf::CNFCache;
use crate::datatypes::axioms::{learn_ctor_selector_clauses, learn_or_not_term_tester_term};
use crate::datatypes::process::DatatypeInfo;
use crate::debug_println;
use crate::egraphs::datastructures::{
    Assertion, ConstructorType, ConstructorType::*, Quantifier, TermOption,
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
    pub fn new(context: Context, lazy_dt: bool, ddsmt: bool, eager_skolem: bool) -> Self {
        let datatype_info = DatatypeInfo::from_context(&context);
        let egraph = Egraph::new(context, lazy_dt, ddsmt, eager_skolem);

        SolverState {
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
}

/// Process a SAT literal assignment through the egraph.
/// This is the solver-level entry point that classifies the literal and
/// dispatches to the appropriate egraph operation (union, disequality, etc.).
pub fn process_assignment(
    lit: i32,
    egraph: &mut Egraph,
    level: usize,
    fixed: bool,
    from_quantifier: bool,
    reason: Option<ProofForestEdge>,
) -> Option<Vec<Vec<i32>>> {
    debug_println!(2, 0, "Processing literal {:} at level {}", lit, level);
    let sign = lit > 0;

    let term = egraph.get_term_from_lit(lit.abs());
    debug_println!(24, 1, "Term: {}", term);
    let assertion = find_if_eq_diseq(&term, sign, egraph, level, fixed);

    let mut tracker = ProofTracker::new();

    if let Some(t) = egraph.cnf_cache.var_map_reverse.get(&lit) {
        let res = if let Some(r) = reason.clone() {
            r
        } else {
            ProofForestEdge::Equality {
                size: 0,
                term: Some((*t, egraph.true_term)),
                parent: 0,
                child: 0,
                disequalities: DeterministicHashMap::new(),
                level,
                hash: egraph.predecessor_hash,
                children: DeterministicHashSet::new(),
            }
        };
        debug_println!(
            16,
            0,
            "We are in process_assignment, unioning with true for lit {} and t {} and true_term {}",
            lit,
            t,
            egraph.true_term
        );
        if let Some(negated_model) = egraph.cc_union(
            *t,
            egraph.true_term,
            res,
            level,
            fixed,
            from_quantifier,
        ) {
            return Some(negated_model);
        };
    }

    if let Some(t) = egraph.cnf_cache.var_map_reverse.get(&-lit) {
        let res = if let Some(r) = reason.clone() {
            r
        } else {
            ProofForestEdge::Equality {
                size: 0,
                term: Some((*t, egraph.false_term)),
                parent: 0,
                child: 0,
                disequalities: DeterministicHashMap::new(),
                level,
                hash: egraph.predecessor_hash,
                children: DeterministicHashSet::new(),
            }
        };
        debug_println!(
            16,
            0,
            "We are in process_assignment, unioning with false for lit {} and t {} and false_term {}",
            lit,
            t,
            egraph.false_term
        );
        if let Some(negated_model) = egraph.cc_union(
            *t,
            egraph.false_term,
            res,
            level,
            fixed,
            from_quantifier,
        ) {
            return Some(negated_model);
        };
    }

    debug_println!("Finished union to True/False");
    let additional_constraints = match assertion {
        Assertion::Tester {
            ctor_name,
            inner_term,
            term,
        } => {
            let dt_sort = inner_term.get_sort(egraph);
            let _term_lit = egraph.get_lit_from_term(&term);
            debug_println!(19, 0, "trying to get for the term {}", inner_term);
            match egraph.term_constructors.get(&inner_term.uid()).unwrap() {
                Constructor {
                    name,
                    tester_term,
                    hash,
                    level,
                } if valid_hash(*hash, *level, &egraph.predecessor_level) => {
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
                            egraph,
                            tester_term.clone(),
                            term.clone(),
                            true,
                        );
                        Some(tester_cnf)
                    }
                }
                _ => {
                    egraph.term_constructors.insert(
                        inner_term.uid(),
                        Constructor {
                            name: ctor_name.clone(),
                            tester_term: term.clone(),
                            level,
                            hash: egraph.predecessor_hash,
                        },
                    );

                    if egraph.lazy_dt {
                        let dt_name = egraph.datatype_info.constructors.get(&ctor_name).unwrap();
                        let dt_dec = egraph.datatype_info.datatypes.get(dt_name).unwrap();
                        let dt_dec = dt_dec
                            .monomorphize(&dt_sort, egraph.context.arena())
                            .expect("type invariant violation: datatype fails to monomorphize");

                        let ctor = dt_dec
                            .constructors
                            .iter()
                            .find(|ctor| ctor.ctor == ctor_name)
                            .expect("type checking invariance violation: datatypes")
                            .clone();

                        let ctor_selector_clauses: Vec<Vec<i32>> =
                            learn_ctor_selector_clauses(egraph, &inner_term, &ctor, &dt_sort, true);
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
                egraph.get_term(t1),
                egraph.get_term(t2)
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
                    hash: egraph.predecessor_hash,
                    children: DeterministicHashSet::new(),
                }
            };
            egraph.cc_union(t1, t2, reason, level, fixed, from_quantifier)
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
                egraph.get_term(t1),
                egraph.get_term(t2),
                level,
                hash
            );
            debug_println!(10, 0, "{}", egraph);

            if let Some(negated_model) =
                egraph.leastcommonancestor(t1, t2, &mut ProofTracker::new())
            {
                let mut model_terms: Vec<i32> = negated_model
                    .into_iter()
                    .map(|x| -egraph.make_eq(x.0, x.1))
                    .collect();
                model_terms.push(egraph.make_eq(t1, t2));
                debug_println!(
                    16,
                    1,
                    "Contradiction found [1]: {:?} [{:?}]",
                    model_terms
                        .iter()
                        .map(|x| egraph.get_term_from_lit(*x))
                        .collect::<Vec<_>>(),
                    model_terms
                );
                return Some(vec![model_terms]);
            }
            egraph.add_disequality(t1, t2, lit, level, hash);
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
                        egraph.get_term(t1),
                        egraph.get_term(t2),
                        level,
                        hash
                    );
                    if let Some(negated_model) =
                        egraph.leastcommonancestor(t1, t2, &mut ProofTracker::new())
                    {
                        let mut model_terms: Vec<i32> = negated_model
                            .into_iter()
                            .map(|x| -egraph.make_eq(x.0, x.1))
                            .collect();
                        model_terms.push(-lit);
                        debug_println!(
                            7,
                            1,
                            "Contradiction found [1]: {:?} [{:?}]",
                            model_terms
                                .iter()
                                .map(|x| egraph.get_term_from_lit(*x))
                                .collect::<Vec<_>>(),
                            model_terms
                        );
                        debug_println!(16, 0, "returning negated model {:?}", model_terms);
                        return Some(vec![model_terms]);
                    }
                    egraph.add_disequality(t1, t2, lit, level, hash);
                    debug_println!(11, 0, "{}", egraph);
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
        egraph.true_term,
        egraph.false_term
    );
    debug_println!(10, 0, "Checking if true = false {}", egraph);
    if let Some(negated_model) =
        egraph.leastcommonancestor(egraph.true_term, egraph.false_term, &mut tracker)
    {
        let negated_model_terms: Vec<i32> = negated_model
            .into_iter()
            .map(|x| -egraph.make_eq(x.0, x.1))
            .collect();
        debug_println!(
            24,
            1,
            "Contradiction found [2] (setting true = false): {:?} [{:?}]",
            negated_model_terms
                .iter()
                .map(|x| egraph.get_term_from_lit(*x))
                .collect::<Vec<_>>(),
            negated_model_terms
        );
        if is_important(7) {
            for lit in negated_model_terms.clone() {
                debug_println!(7, 4, "{}", egraph.get_term_from_lit(lit));
            }
        }
        debug_println!(7, 0, "{}", egraph);

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
    egraph: &'a Egraph,
    level: usize,
    fixed: bool,
) -> Assertion {
    let hash = if !fixed { egraph.predecessor_hash } else { 0 };
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
                egraph
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
