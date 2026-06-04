// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Classic congruence closure algorithm

use crate::datatypes::axioms::{learn_ctor_selector_clauses, learn_or_not_term_tester_term};
use crate::egraphs::proofforest::ProofForestEdge;
use crate::utils::{
    DeterministicHashMap, DeterministicHashSet,
};
use yaspar_ir::ast::alg::CheckIdentifier;
use yaspar_ir::ast::{
    FetchSort, HasArena, IdentifierKind, Monomorphization, Repr, Term,
};

use crate::debug_println;
use crate::egraphs::datastructures::{
    Assertion, ConstructorType::*,
};
use crate::egraphs::egraph::{Egraph, valid_hash};
use crate::egraphs::unionfind::ProofTracker;
use crate::log::is_important;
use yaspar_ir::ast::ATerm::*;

// todo might be able to get rid fo reason now
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

    // note this basically assumes the postive polarity is always in the map from i32->u64
    // this should be true based on how we do
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
            // need to add isC(n) => n = C(C^1(n),..., C^m(n))
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
                        None // don't need to add anything
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

                        // todo: we want do this by calling this helper function but it currently
                        // note that the from_quantifier = true is important here
                        // it essentially says that this is a term that we learn not necessarily at level 0
                        // but we want to retain this term even after we backtrack
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
                return Some(vec![model_terms]); // Return negated model as the contradiction explanation
            }
            egraph.add_disequality(t1, t2, lit, level, hash); // adding the disequality to the egraph
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
                        return Some(vec![model_terms]); // Return negated model as the contradiction explanation
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
    //  debug_println!(4, 0, "{}", egraph);
    debug_println!(10, 0, "Checking if true = false {}", egraph);
    if let Some(negated_model) =
        egraph.leastcommonancestor(egraph.true_term, egraph.false_term, &mut tracker)
    {
        let negated_model_terms: Vec<i32> = negated_model
            .into_iter()
            .map(|x| -egraph.make_eq(x.0, x.1))
            .collect();
        // negated_model_terms.push(egraph.make_eq(egraph.true_term, egraph.false_term));
        // todo : we never seem to get an early contradction here, but we should in theory always get one
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

        // Return negated model as the contradiction explanation
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

pub fn find_if_eq_diseq<'a>(
    term: &'a Term,
    sign: bool,
    egraph: &'a Egraph,
    level: usize,
    fixed: bool, // todo: get rid of fixed and have it be represented by hash 0
) -> Assertion {
    // assert! (!fixed); // I think we should never have things be fixed basically
    let hash = if !fixed { egraph.predecessor_hash } else { 0 };
    match term.repr() {
        // Match both tester syntaxes: (_ is Ctor) and (is-Ctor x)
        App(f, t, _)
            if (matches!(f.get_kind(), Some(IdentifierKind::Is(_)))
                || (f.get_kind().is_none() && f.id_str().get().starts_with("is-")))
                && t.len() == 1
                && sign =>
        {
            // Extract the constructor name from whichever syntax was used
            let ctor_name = if let Some(IdentifierKind::Is(sym)) = f.get_kind() {
                // (_ is Ctor) — indexed identifier, ctor name is directly available
                Some(sym.clone())
            } else {
                // (is-Ctor x) — strip "is-" prefix and look up the constructor
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
                // is-X where X is not a known constructor; treat as uninterpreted
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
                assert!(sign); // sign must be positive
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
            // TODO: does this actually matter anymore?
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


pub fn add_parent(
    proof_parent: ProofForestEdge,
    parent: u64,
    new_child: u64,
    level: usize,
    hash: u64,
) -> ProofForestEdge {
    match proof_parent {
        ProofForestEdge::Root {
            size: _,
            child: _,
            disequalities: _,
            children: _,
        } => {
            panic!("ERROR: We are trying to add a parent to a root1");
        }
        ProofForestEdge::Congruence {
            size,
            pairs,
            disequalities,
            children,
            ..
        } => ProofForestEdge::Congruence {
            size,
            pairs,
            parent,
            child: new_child,
            disequalities,
            level,
            hash,
            children,
        },
        ProofForestEdge::Equality {
            size,
            term,
            disequalities,
            children,
            ..
        } => ProofForestEdge::Equality {
            size,
            term,
            parent,
            child: new_child,
            disequalities,
            level,
            hash,
            children,
        },
    }
}

pub fn get_parent(proof_parent: &ProofForestEdge) -> u64 {
    debug_println!(6, 0, "We are getting the parent of {:?}", proof_parent);
    match proof_parent {
        ProofForestEdge::Root { .. } => {
            panic!("ERROR: We are trying to add a parent to a root2");
        }
        ProofForestEdge::Congruence {
            parent: proof_parent,
            ..
        } => *proof_parent,
        ProofForestEdge::Equality {
            parent: proof_parent,
            ..
        } => *proof_parent,
    }
}

pub fn get_child(proof_parent: &ProofForestEdge) -> u64 {
    match proof_parent {
        ProofForestEdge::Root {
            child,
            disequalities: _,
            ..
        } => *child,
        ProofForestEdge::Congruence { child, .. } => *child,
        ProofForestEdge::Equality { child, .. } => *child,
    }
}


