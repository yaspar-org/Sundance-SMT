// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Preprocessing step for function/ITE that takes in boolean inputs.
//! see for example "tests/regression/smt_files/edge_cases/test_bool.smt2" or
//! ""tests/regression/smt_files/edge_cases/test_bool_ite.smt2"" for an example

use sat_interface::Formula;
use yaspar_ir::ast::alg::{Identifier, Index, QualifiedIdentifier};
use yaspar_ir::ast::{ATerm::*, Attribute, Sort, TermAllocator};
use yaspar_ir::ast::{FetchSort, ObjectAllocatorExt, Repr, StrAllocator, Term};

use crate::cnf::CNFConversion as _;
use crate::egraphs::datastructures::ConstructorType;
use crate::egraphs::egraph::Egraph;
use crate::utils::DeterministicHashSet;

/// For each Boolean subterm, we apply the Tseitin transformation and add those clauses
/// We also include subcalls to `find_datatype_axioms` and `process_ite` to process datatype and ite axioms
pub fn check_for_function_bool(
    term: &Term,
    egraph: &mut Egraph,
    from_quantifier: bool,
) -> Vec<Vec<i32>> {
    // todo: I added the from_quantifier flag because of the insert_predecessor calls. I think this is right
    let mut vector = vec![];

    if let Some(formula) = process_ite(term, egraph, from_quantifier) {
        vector.extend(formula.into_iter().map(|x| x.0));
    }

    let sort = term.get_sort(egraph);
    // checking if term is a bool
    if sort == egraph.bool_sort() {
        // if a term is a bool, but not part of the cnf, we need to add it
        if !egraph.cnf_cache.var_map.contains_key(&term.uid()) {
            let nnf_term = term.nnf(egraph);
            let cnf_formula = term.cnf_tseitin(egraph).into_iter().map(|x| x.0);

            egraph.insert_predecessor(&nnf_term, None, None, from_quantifier, None); // todo: I think its right to have a from_quantifier here

            vector.extend(cnf_formula);

            // the last clause will be asserting the literal so we drop it
            let vector_lit = vector.pop().unwrap();
            // might not have term in context because of simplifications done in flat_and/flat_or
            // see tests/regression/smt_files/edge_cases/tseitin.smt2 for an example
            // todo: below doesn't do anything; remove it
            if let Some(l) = egraph.cnf_cache.var_map.get(&term.uid()) {
                assert!(vector_lit.len() == 1 && (vector_lit[0] == *l));
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
    // println!("returning {:?}", vector);
    vector
}

/// finds the datatype axioms
fn find_datatype_axioms(
    term: &Term, // must be a datatype term
    sort: &Sort, // the sort of the given term
    egraph: &mut Egraph,
    // todo: this variable is only used in a very limited way
    from_quantifier: bool,
) -> Vec<Vec<i32>> {
    let mut vector = vec![];
    let dt_dec = if let Some(ctors) = egraph
        .datatype_info
        .datatypes
        .get(sort.sort_name())
        .cloned()
    {
        ctors
    } else {
        // misuse of this function; sort should be a datatype
        return vector;
    };

    let bool_sort = egraph.bool_sort();
    let is_symbol = egraph.allocate_symbol("is");

    // Step 1. Store the constructor in term_constructors
    let num = term.uid();
    if egraph.datatype_axioms_applied.contains(&num) {
        return vector;
    }
    egraph.datatype_axioms_applied.insert(num);

    // todo: why do we need this? missing Global case?
    if !egraph.term_constructors.contains_key(&num) {
        if let App(f, _, _) = term.repr()
            && egraph.datatype_info.constructors.contains_key(f.id_str())
        {
            let tester_identifier = Identifier {
                symbol: is_symbol.clone(),
                indices: vec![Index::Symbol(f.id_str().clone())],
            };
            // insert (_ is X)
            let tester_term = egraph.app(
                tester_identifier.into(),
                vec![term.clone()],
                Some(bool_sort.clone()),
            );
            // todo: we are not handling is-X here
            egraph.term_constructors.insert(
                num,
                ConstructorType::Constructor {
                    name: f.id_str().clone(),
                    tester_term,
                    hash: 0,
                    level: 0,
                },
            );
        } else {
            egraph
                .term_constructors
                .insert(num, ConstructorType::Uninitialized);
        }
    }

    // Step 2. Learn the clause isC1(t) \/ ... \/ isCm(t)

    // Collect all constructors for this datatype sort

    let mut tester_apps = vec![];

    // Create tester applications for each constructor: (_ is ConstructorName) term
    // todo: get this to work
    for ctor in &dt_dec.constructors {
        let ctor_name = &ctor.ctor;
        // Create the tester identifier: (_ is ConstructorName)

        let tester_identifier = Identifier {
            symbol: is_symbol.clone(),
            indices: vec![Index::Symbol(ctor_name.clone())],
        };

        // todo: also need (is-ConstructorName term)
        // Create the tester application: ((_ is ConstructorName) term)
        let tester_app = egraph.app(
            tester_identifier.into(),
            vec![term.clone()],
            Some(bool_sort.clone()),
        );

        // adding the clause ((_ is ConstructorName) (ConstructorName ...)) if relevant
        match term.repr() {
            App(f, _, _) | Global(f, _) if *f.id_str() == *ctor_name => {
                debug_println!(12, 0, "TESTER Constructor CASE");
                let tester_app_nnf = tester_app.nnf(egraph);
                egraph.insert_predecessor(&tester_app_nnf, None, None, from_quantifier, None);
                let tester_app_cnf = tester_app_nnf.cnf_tseitin(egraph).into_iter().map(|x| x.0);
                debug_println!(25, 10, "(assert {})", tester_app);
                vector.extend(tester_app_cnf);
            }
            _ => {}
        };

        tester_apps.push(tester_app);
    }

    let tester_or = if tester_apps.len() == 1 {
        tester_apps[0].clone()
    } else {
        egraph.or(tester_apps)
    };
    debug_println!(12, 0, "TESTER OR CASE");
    debug_println!(25, 10, "(assert {})", tester_or);
    egraph.insert_predecessor(&tester_or, None, None, from_quantifier, None);
    // Add the tester to CNF processing
    // let tester_cnf = &tester_app.cnf_tseitin(&mut *egraph);
    let tester_cnf = tester_or.cnf_tseitin(egraph).into_iter().map(|x| x.0);
    debug_println!(12, 2, "this gives us {:?}", tester_cnf);
    vector.extend(tester_cnf);

    // Step 2.5. Learn the constraint (is-f t) => t = f(f^0(t) ... f^m(t))
    // as long as we are not doing lazy datatypes
    if !egraph.lazy_dt {
        for ctor in &dt_dec.constructors {
            let ctor_name = &ctor.ctor;
            // todo: repeating from last for loop, can probably combine stuff
            let tester_identifier = Identifier {
                symbol: is_symbol.clone(),
                indices: vec![Index::Symbol(ctor_name.clone())],
            };
            let tester_app = egraph.app(
                tester_identifier.into(),
                vec![term.clone()],
                Some(bool_sort.clone()),
            );

            let mut selectors_apps = vec![];
            for sel in &ctor.args {
                let sel_app = egraph.app(
                    QualifiedIdentifier::simple(sel.0.clone()),
                    vec![term.clone()],
                    Some(sel.2.clone()),
                );

                // include new constraints for subterms
                let additional_constraints = find_datatype_axioms(&sel_app, sort, egraph, false);
                vector.extend(additional_constraints.clone());

                selectors_apps.push(sel_app);
            }

            // this needs to be a variable if ctor talks in no arguments
            let ctor_id = QualifiedIdentifier::simple(ctor_name.clone());
            let ctor_app = if selectors_apps.is_empty() {
                // we directly use sort becasue we will be using equality
                egraph.global(ctor_id, Some(sort.clone()))
            } else {
                egraph.app(ctor_id, selectors_apps, Some(sort.clone()))
            };

            let eq = egraph.eq(term.clone(), ctor_app);
            let imp = egraph.implies(vec![tester_app], eq);
            debug_println!(25, 10, "(assert {})", imp);
            let imp_nnf = imp.nnf(egraph);
            egraph.insert_predecessor(&imp_nnf, None, None, false, None);
            let imp_cnf = imp.cnf_tseitin(egraph);
            let clauses = imp_cnf.0.iter().map(|c| c.0.clone());
            vector.extend(clauses);
        }
    }

    // Step 3. Learn the constraint  /\_i=1^k f_i(f(t1, ... tk)) = t_i
    if let App(f, terms, _) = term.repr()
        && egraph.datatype_info.constructors.contains_key(f.id_str())
    {
        let ctor = dt_dec
            .constructors
            .iter()
            .find(|ctor| ctor.ctor == *f.id_str())
            .unwrap();

        assert_eq!(terms.len(), ctor.args.len());

        for (sel_term, sel) in terms.iter().zip(ctor.args.iter()) {
            let so = sel_term.get_sort(egraph);
            let sel_app = &egraph.app(
                QualifiedIdentifier::simple(sel.0.clone()),
                vec![term.clone()],
                Some(so),
            );
            let sel_eq = egraph.eq(sel_app.clone(), sel_term.clone());
            debug_println!(25, 10, "(assert {})", sel_eq);
            debug_println!(14 - 3, 0, "adding in {}", sel_eq);
            let sel_eq_nnf = sel_eq.nnf(egraph);
            egraph.insert_predecessor(&sel_eq_nnf, None, None, false, None);
            let sel_eq_cnf = sel_eq.cnf_tseitin(egraph);
            let clauses = sel_eq_cnf.0.iter().map(|c| c.0.clone());
            vector.extend(clauses)
        }
    }
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
