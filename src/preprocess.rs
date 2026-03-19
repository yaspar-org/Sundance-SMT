// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Preprocessing step for function/ITE that takes in boolean inputs.
//! see for example "tests/regression/smt_files/edge_cases/test_bool.smt2" or
//! ""tests/regression/smt_files/edge_cases/test_bool_ite.smt2"" for an example

use sat_interface::Formula;
use yaspar_ir::ast::{ATerm::*, Attribute, TermAllocator};
use yaspar_ir::ast::{FetchSort, ObjectAllocatorExt, Repr, Term};

use crate::cnf::CNFConversion as _;
use crate::datatypes::axioms::find_datatype_axioms;
use crate::debug_println;
use crate::egraphs::egraph::Egraph;
use crate::utils::DeterministicHashSet;

/// For each Boolean subterm, we apply the Tseitin transformation and add those clauses
/// We also include subcalls to `find_datatype_axioms` and `process_ite` to process datatype and ite axioms
pub fn check_for_function_bool(
    term: &Term,
    egraph: &mut Egraph,
    from_quantifier: bool,
) -> Vec<Vec<i32>> {
    debug_println!(
        16,
        0,
        "checking for function bool in term {} with from_quantifier {}",
        term,
        from_quantifier
    );
    let mut vector = vec![];

    if let Some(formula) = process_ite(term, egraph, from_quantifier) {
        vector.extend(formula.into_iter().map(|x| x.0));
    }

    let sort = term.get_sort(egraph);
    // checking if term is a bool
    if sort == egraph.bool_sort() {
        // if a term is a bool, but not part of the cnf, we need to add it
        debug_println!(
            16,
            0,
            "term {} is a bool, checking if it is in the cnf cache",
            term
        );
        if !egraph.cnf_cache.var_map.contains_key(&term.uid()) {
            let nnf_term = term.nnf(egraph);
            let cnf_formula = term.cnf_tseitin(egraph).into_iter().map(|x| x.0);

            egraph.insert_predecessor(&nnf_term, None, None, from_quantifier, None); // todo: I think its right to have a from_quantifier here

            vector.extend(cnf_formula);
            debug_println!(
                16,
                0,
                "term {} is not in the cnf cache, adding its cnf formula {:?}",
                term,
                vector
            );

            // the last clause will be asserting the literal so we drop it
            let vector_lit = vector.pop().unwrap();
            // might not have term in context because of simplifications done in flat_and/flat_or
            // see tests/regression/smt_files/edge_cases/tseitin.smt2 for an example
            if let Some(l) = egraph.cnf_cache.var_map.get(&term.uid()) {
                assert!(vector_lit.len() == 1 && (vector_lit[0] == *l));
            } else {
                // For terms like ite/implies, cnf_tseitin converts to NNF first, so only the NNF
                // term's UID ends up in var_map. Register the original term's UID here so
                // downstream code (e.g. the tautology clause below) can find its literal.
                assert!(vector_lit.len() == 1);
                if vector_lit.len() == 1 {
                    egraph.cnf_cache.var_map.insert(term.uid(), vector_lit[0]);
                    egraph
                        .cnf_cache
                        .var_map_reverse
                        .insert(vector_lit[0], term.uid());
                }
            }
        }

        // for each bool term with corresponding literal "l", we must add the clause "-l l 0"
        // might not have term in context because of simplications done in flat_and/flat_or
        if let Some(lit) = egraph.cnf_cache.var_map.get(&term.uid()) {
            vector.push(vec![-lit, *lit]);
        }
    }

    // if a term has a datatype type, then create tester applications for each constructor
    if egraph.datatype_info.is_datatype(sort.sort_name()) {
        vector.extend(find_datatype_axioms(term, &sort, egraph, from_quantifier))
    }

    match term.repr() {
        App(_, items, _) | And(items) | Or(items) | Xor(items) | Distinct(items) => {
            vector.extend(
                items
                    .iter()
                    .flat_map(|t| check_for_function_bool(t, egraph, from_quantifier)),
            );
        }
        Eq(a, b) => {
            vector.extend(check_for_function_bool(a, egraph, from_quantifier));
            vector.extend(check_for_function_bool(b, egraph, from_quantifier));
        }
        Not(t) | Annotated(t, _) => {
            vector.extend(check_for_function_bool(t, egraph, from_quantifier));
        }
        Implies(items, p) => {
            vector.extend(check_for_function_bool(p, egraph, from_quantifier));
            vector.extend(
                items
                    .iter()
                    .flat_map(|t| check_for_function_bool(t, egraph, from_quantifier)),
            );
        }
        Ite(b, x, y) => {
            vector.extend(check_for_function_bool(b, egraph, from_quantifier));
            vector.extend(check_for_function_bool(x, egraph, from_quantifier));
            vector.extend(check_for_function_bool(y, egraph, from_quantifier));
        }
        Matching(t, pattern_arms) => {
            vector.extend(check_for_function_bool(t, egraph, from_quantifier));
            vector.extend(pattern_arms.iter().flat_map(|pattern| {
                check_for_function_bool(&pattern.body, egraph, from_quantifier)
            }));
        }
        Forall(var_bindings, t) | Exists(var_bindings, t) => {
            // if we have a forall statement equivalent to false, it must be false (just an optimization to help with ddsmt)
            if egraph.ddsmt {
                let var_binding_strings = var_bindings.iter().map(|x| x.0.get()).collect();
                let nnf_t = t.nnf(egraph); // kind've wasteful but necessary to get ddsmt to play nicely (todo: could eventually remove this)
                if !check_if_var_occurs_in_term(&nnf_t, &var_binding_strings, egraph) {
                    let equality = egraph.eq(term.clone(), t.clone());
                    let nnf_term = equality.nnf(egraph);
                    egraph.insert_predecessor(&nnf_term, None, None, from_quantifier, None);
                    let cnf_formula = nnf_term
                        .cnf_tseitin(egraph)
                        .into_iter()
                        .map(|x| x.into_iter().collect::<Vec<_>>());
                    let sub_formula = check_for_function_bool(&nnf_t, egraph, from_quantifier);
                    debug_println!(
                        19,
                        0,
                        "We have the additional cnf_formula {:?}",
                        cnf_formula
                    );
                    vector.extend(cnf_formula);
                    debug_println!(
                        19,
                        0,
                        "We have the additional sub_formula {:?}",
                        sub_formula
                    );
                    vector.extend(sub_formula)
                }

                // also if we have a pattern that contains a subterm that is a datatype (and it contains none of the bound variables)
                // then we still want to instantiate adt axioms for it
                // this is just an optimization to help with ddsmt, I don't think this actually matters in practice
                // todo: could maybe delete this eventually
                if let Annotated(_, attrs) = t.repr() {
                    for attr in attrs {
                        if let Attribute::Pattern(patterns) = &attr {
                            for pattern in patterns {
                                let additional_pattern_constraints = get_pattern_dt_constraints(
                                    pattern,
                                    &var_binding_strings,
                                    egraph,
                                    from_quantifier,
                                );
                                debug_println!(
                                    19,
                                    0,
                                    "We have the additional constraints {:?}",
                                    additional_pattern_constraints
                                );
                                vector.extend(additional_pattern_constraints)
                            }
                        }
                    }
                }
            }
        }
        Let(_, _) => panic!("We should have inlined lets by now"),
        Constant(..) | Global(..) | Local(..) => (), // todo: I think existentials should be handled separately when they get skolemized but not 100% sure about this
    };
    debug_println!(16, 0, "returning {:?}", vector);
    vector
}

/// gets datatype constraints from a pattern
fn get_pattern_dt_constraints(
    pattern: &Term,
    vars: &DeterministicHashSet<&String>,
    egraph: &mut Egraph,
    from_quantifier: bool,
) -> Vec<Vec<i32>> {
    let mut vector = vec![];

    // if the pattern does not occur in the term, we can treat it like a datatype
    if !check_if_var_occurs_in_term(pattern, vars, egraph) {
        let sort = pattern.get_sort(egraph);
        if egraph.datatype_info.is_datatype(sort.sort_name()) {
            vector.extend(find_datatype_axioms(
                pattern,
                &sort,
                egraph,
                from_quantifier,
            ))
        }
    }

    match pattern.repr() {
        App(_, args, _) => {
            for arg in args {
                vector.extend(get_pattern_dt_constraints(
                    arg,
                    vars,
                    egraph,
                    from_quantifier,
                ))
            }
        }
        Ite(b, t1, t2) => {
            vector.extend(get_pattern_dt_constraints(b, vars, egraph, from_quantifier));
            vector.extend(get_pattern_dt_constraints(
                t1,
                vars,
                egraph,
                from_quantifier,
            ));
            vector.extend(get_pattern_dt_constraints(
                t2,
                vars,
                egraph,
                from_quantifier,
            ))
        }
        // no subcases to consider
        Global(..) | Constant(..) | Local(..) => {}
        _ => {
            panic!("We do not support patterns with {}", pattern)
        }
    };

    vector
}

// checks if any of the variables occur in a term
fn check_if_var_occurs_in_term(
    term: &Term,
    var_bindings: &DeterministicHashSet<&String>,
    egraph: &mut Egraph,
) -> bool {
    debug_println!(
        19,
        0,
        "checking if var {:?} occurs in term {}",
        var_bindings,
        term
    );
    match term.repr() {
        Constant(_, _) => false,
        Global(_, _) => false,
        Local(local) => var_bindings.contains(local.symbol.get()),
        // for And and Or, if they contain a false or true respectively, not that we don't have to consider it
        // this is a ddsmt optimization (dont produce sound proofs for this)
        And(items) => {
            if egraph.ddsmt {
                for item in items {
                    if item == &egraph.get_false() {
                        return false;
                    }
                }
            }
            items
                .iter()
                .any(|t| check_if_var_occurs_in_term(t, var_bindings, egraph))
        }
        Or(items) => {
            if egraph.ddsmt {
                for item in items {
                    if item == &egraph.get_true() {
                        return false;
                    }
                }
            }
            items
                .iter()
                .any(|t| check_if_var_occurs_in_term(t, var_bindings, egraph))
        }
        Xor(items) => items
            .iter()
            .any(|t| check_if_var_occurs_in_term(t, var_bindings, egraph)),
        App(_, items, _) | Distinct(items) => items
            .iter()
            .any(|t| check_if_var_occurs_in_term(t, var_bindings, egraph)),
        Annotated(t, _) | Not(t) => check_if_var_occurs_in_term(t, var_bindings, egraph),
        Eq(t1, t2) => {
            check_if_var_occurs_in_term(t1, var_bindings, egraph)
                || check_if_var_occurs_in_term(t2, var_bindings, egraph)
        }
        Implies(items, t) => items.iter().fold(
            check_if_var_occurs_in_term(t, var_bindings, egraph),
            |acc, t| acc || check_if_var_occurs_in_term(t, var_bindings, egraph),
        ),
        Ite(t1, t2, t3) => {
            check_if_var_occurs_in_term(t1, var_bindings, egraph)
                || check_if_var_occurs_in_term(t2, var_bindings, egraph)
                || check_if_var_occurs_in_term(t3, var_bindings, egraph)
        }
        Exists(var_bindings_innner, t) | Forall(var_bindings_innner, t) => {
            // Create a new set excluding the bound variables
            let mut filtered_vars = var_bindings.clone();
            for var_binding in var_bindings_innner {
                filtered_vars.remove(var_binding.0.get());
            }
            check_if_var_occurs_in_term(t, &filtered_vars, egraph)
        }
        Let(..) | Matching(..) => todo!(),
    }
}

fn process_ite(term: &Term, egraph: &mut Egraph, from_quantifier: bool) -> Option<Formula> {
    if let Ite(b, t1, t2) = term.repr() {
        let eq1 = egraph.eq(term.clone(), t1.clone());
        let imp1 = egraph.implies(vec![b.clone()], eq1);

        let eq2 = egraph.eq(term.clone(), t2.clone());
        let not_b = egraph.not(b.clone());
        let imp2 = egraph.implies(vec![not_b], eq2);

        let ite_axioms = egraph.and(vec![imp1, imp2]);
        let ite_axioms_nnf = ite_axioms.nnf(egraph);
        egraph.insert_predecessor(&ite_axioms_nnf, None, None, from_quantifier, None);
        Some(ite_axioms_nnf.cnf_tseitin(egraph))
    } else {
        None
    }
}
