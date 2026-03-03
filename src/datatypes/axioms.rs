// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0


use std::vec;

use yaspar_ir::ast::alg::{Identifier, Index, QualifiedIdentifier};
use yaspar_ir::ast::{ATerm::*, TermAllocator};
use yaspar_ir::ast::{ObjectAllocatorExt, Repr, StrAllocator, Term};

use crate::cnf::CNFConversion as _;
use crate::egraphs::datastructures::ConstructorType;
use crate::egraphs::egraph::Egraph;



/// For a term of datatype sort, we want to learn the following axioms:
/// 1. isC1(t) \/ ... \/ isCm(t) where C1, ..., Cm are the constructors of the datatype
/// 2. (is-f t) => t = f(f^0(t) ... f^m(t)) for each constructor f of the   datatype where f^0, ..., f^m are the selectors of f
/// 2.5. (is-f t) => t = f(f^0(t) ... f^m(t)) for each constructor f of the datatype where f^0, ..., f^m are the selectors of f (by default we add this lazily based on the assignment in term_constructors)
/// 3. /\_i=1^k f_i(f(t1, ... tk)) = t_i for term = f(t1, ..., tk) where f is a constructor with selectors f_1, ..., f_k and subterms t1, ..., tk.
/// (done lazily) 4. We also need to ~isCi(t) \/ ~isCj(t) for each pair of distinct constructors Ci and Cj of the datatype (we do this lazily based on the assignment in term_constructors)
/// Note that we also need to include the datatype axioms for the selectors if they are of datatype sort, so we
pub fn find_datatype_axioms(
    term: &Term,
    sort: String,
    egraph: &mut Egraph,
    from_quantifier: bool,
) -> Vec<Vec<i32>> {
    let mut vector = vec![];
    let num = term.uid();
    if egraph.datatype_axioms_applied.contains(&num) {
        return vector;
    }
    egraph.datatype_axioms_applied.insert(num);

    // Step 1. Store the constructor in term_constructors
    if !egraph.term_constructors.contains_key(&num) {
        add_to_term_constructors(egraph, term);
    } 

    // Collect all constructors for this datatype sort
    let mut datatype_constructors = Vec::new();
    for (ctor_name, ctor_info) in &egraph.datatype_info.constructors {
        if ctor_info.datatype == sort {
            datatype_constructors.push(ctor_name.clone());
        }
    }

    // Step 2. Learn the clause isC1(t) \/ ... \/ isCm(t)
    let tester_cnf = learn_exactly_one_tester_clause(egraph, term, &datatype_constructors, from_quantifier);

    vector.extend(tester_cnf);

    // Step 2.5. Learn the constraint (is-f t) => t = f(f^0(t) ... f^m(t))
    // as long as we are not doing lazy datatypes
    if !egraph.lazy_dt {
        let ctor_selector_cnf = learn_ctor_selector_clause(egraph, term, &datatype_constructors);
        vector.extend(ctor_selector_cnf);
    }

    // Step 3. Learn the constraint  /\_i=1^k f_i(f(t1, ... tk)) = t_i
    if let App(f, terms, _) = term.repr()
        && egraph
            .datatype_info
            .constructors
            .contains_key(f.id_str().get())
    {
        let selector_ctor_cnf = learn_selector_ctor_clause(egraph, term, f.id_str().get().to_string(), terms);
        vector.extend(selector_ctor_cnf);
    }
    vector
}


/// Adds a term to term_constructors which keeps track of the correct constructor of each term. 
/// Note that the axiom `~isCi(t) \/ ~isCj(t)` is added lazily based on the assignment in term_constructors
/// if the term is of the form C(t1, ..., tm) where C is a constructor, we add it as a Constructor with the tester term (_ is C) t
/// otherwise, we add it as Uninitialized and we will update it later if we learn that 
fn add_to_term_constructors(egraph: &mut Egraph, term: &Term) {
    let num = term.uid();
    if let App(f, _, _) = term.repr()
        && egraph
            .datatype_info
            .constructors
            .contains_key(f.id_str().as_str())
    {
        let ctor_symbol = egraph.context.allocate_string(f.to_string()); 
        let is_symbol = egraph.context.allocate_str("is");              
        let tester_identifier = Identifier {
            symbol: is_symbol,
            indices: vec![Index::Symbol(ctor_symbol)],
        };
        let tester_qid = QualifiedIdentifier(tester_identifier, None); 
        // Create the tester application: ((_ is ConstructorName) term)
        // we are creating this here because we will use it when we want to learn the datatype axiom ~isCi(t) \/ ~isCj(t)
        let bool_sort = egraph.context.bool_sort();
        let tester_term = egraph
            .context
            .app(tester_qid, vec![term.clone()], Some(bool_sort));
        egraph.term_constructors.insert(
            num,
            ConstructorType::Constructor {
                name: f.to_string(),
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

/// For a term of datatype sort, learn the clause isC1(t) \/ ... \/ isCm(t) where C1, ..., Cm are the constructors of the datatype
/// if the term is of the form C(t1, ..., tm) where C is a constructor, we also add the clause (isC1(t) \/ ... \/ isCm(t)) /\ isC(t) where C is the constructor of the term
fn learn_exactly_one_tester_clause(egraph: &mut Egraph, term: &Term, datatype_constructors: &Vec<String>, from_quantifier: bool) -> Vec<Vec<i32>> {
    let mut vector: Vec<_> = vec![];

    let mut tester_apps = vec![];

    // Create tester applications for each constructor: (_ is ConstructorName) term
    let is_symbol = egraph.context.allocate_str("is"); // todo: maybe this should have allocate_symbol instead??
    let bool_sort = egraph.context.bool_sort();
    for ctor_name in datatype_constructors {
        // Create the tester identifier: (_ is ConstructorName)
        let ctor_symbol = egraph.context.allocate_string(ctor_name.clone()); // egraph.context.get_symbol_str(&ctor_name)
        let tester_identifier = Identifier {
            symbol: is_symbol.clone(),
            indices: vec![Index::Symbol(ctor_symbol)],
        };

        let tester_qid = QualifiedIdentifier(tester_identifier, None); // todo: not sure if I actually need a type here

        // Create the tester application: ((_ is ConstructorName) term)
        let tester_app =
            egraph
                .context
                .app(tester_qid, vec![term.clone()], Some(bool_sort.clone()));

        // adding the clause ((_ is ConstructorName) (ConstructorName ...)) if relevant
        match term.repr() {
            App(f, _, _) | Global(f, _) if *f.id_str().get() == *ctor_name => {
                debug_println!(12, 0, "TESTER Constructor CASE");
                let tester_app_nnf = tester_app.nnf(egraph);
                egraph.insert_predecessor(&tester_app_nnf, None, None, from_quantifier, None);
                let tester_app_cnf = tester_app_nnf
                    .cnf_tseitin(egraph)
                    .into_iter()
                    .map(|x| x.into_iter().collect::<Vec<_>>())
                    .collect::<Vec<_>>();
                debug_println!(25, 10, "(assert {})", tester_app);
                // note that you cannot just return tester_app_cnf here because we also need that (not (isCj(t))) for all other constructors
                // todo: could have an optimization where you have a per-eclass tester application that 
                vector.extend(tester_app_cnf);
            }
            _ => {}
        };

        tester_apps.push(tester_app);
    }

    let tester_or = if tester_apps.len() == 1 {
        tester_apps.remove(0)
    } else {
        egraph.context.or(tester_apps)
    };
    debug_println!(12, 0, "TESTER OR CASE");
    debug_println!(25, 10, "(assert {})", tester_or);
    egraph.insert_predecessor(&tester_or, None, None, from_quantifier, None);
    // CNF the tester_or and add it to the vector
    let tester_cnf = tester_or
        .cnf_tseitin(egraph)
        .into_iter()
        .map(|x| x.into_iter().collect::<Vec<_>>())
        .collect::<Vec<_>>();
    vector.extend(tester_cnf.clone());  
    vector
}

/// For a term of datatype sort, learn the clause (is-f t) => t = f(f^0(t) ... f^m(t)) for each constructor f of the datatype where f^0, ..., f^m are the selectors of f
fn learn_ctor_selector_clause(egraph: &mut Egraph, term: &Term, datatype_constructors: &Vec<String>) -> Vec<Vec<i32>> {

    let mut vector = vec![];

    let is_symbol = egraph.context.allocate_str("is"); 
    let bool_sort = egraph.context.bool_sort();

    for ctor_name in datatype_constructors {
        // todo: repeating from last for loop, can probably combine stuff
        let ctor_symbol = egraph.context.allocate_string(ctor_name.clone()); 
        let tester_identifier = Identifier {
            symbol: is_symbol.clone(),
            indices: vec![Index::Symbol(ctor_symbol.clone())],
        };
        let tester_qid = QualifiedIdentifier(tester_identifier, None);
        let tester_app =
            egraph
                .context
                .app(tester_qid, vec![term.clone()], Some(bool_sort.clone()));

        let mut selectors_apps = vec![];
        let ctor_info = egraph
            .datatype_info
            .constructors
            .get(&ctor_name.to_string())
            .unwrap();
        let selector_sorts = &ctor_info.field_sorts.clone();
        for (i, field) in ctor_info.field_names.iter().enumerate() {
            let sel_name = &egraph.context.allocate_symbol(field);
            let sel_app = egraph.context.app(
                QualifiedIdentifier::simple(sel_name.clone()),
                vec![term.clone()],
                Some(selector_sorts[i].clone()),
            );
            selectors_apps.push(sel_app);
        }

        // this needs to be a variable if ctor talks in no arguments
        let ctor_app = if selectors_apps.is_empty() {
            let ctor_id = QualifiedIdentifier::simple_sorted(
                ctor_symbol,
                ctor_info.datatype_sort.clone(),
            ); // todo: not sure if this is the right was to do it, gets printed out as (as ctor ctor) -> I think it doesnt make a difference
            egraph
                .context
                .global(ctor_id, Some(ctor_info.datatype_sort.clone())) //ctor_local, Some(ctor_sort))
        } else {
            let ctor_id = QualifiedIdentifier::simple(ctor_symbol);
            let ctor_sort = ctor_info.datatype_sort.clone();
            egraph
                .context
                .app(ctor_id, selectors_apps.clone(), Some(ctor_sort))
        };

        for (i, sel_app) in selectors_apps.clone().iter().enumerate() {
            // include new constraints for subterms
            let sort = selector_sorts[i].to_string();
            if egraph.datatype_info.sorts.contains_key(&sort) {
                let additional_constraints = find_datatype_axioms(sel_app, sort, egraph, false);
                vector.extend(additional_constraints.clone());
            }
        }

        let eq = egraph.context.eq(term.clone(), ctor_app);
        let imp = egraph.context.implies(vec![tester_app], eq);
        debug_println!(25, 10, "(assert {})", imp);
        let imp_nnf = imp.nnf(egraph);
        egraph.insert_predecessor(&imp_nnf, None, None, false, None);
        let imp_cnf = imp.cnf_tseitin(egraph);
        let clauses = imp_cnf.0.iter().map(|c| c.0.clone());
        vector.extend(clauses);
    }
    vector
}


/// We are learning the clause /\_i=1^k f_i(f(t1, ... tk)) = t_i
/// for term = f(t1, ..., tk) where f is a constructor with selectors f_1, ..., f_k and subterms t1, ..., tk.
/// Note that we also need to include the datatype axioms for the selectors if they are of datatype sort, so we call find_datatype_axioms on each selector application as well
fn learn_selector_ctor_clause( egraph: &mut Egraph, term: &Term, f: String, subterms: &Vec<Term>,) -> Vec<Vec<i32>> {
    let mut vector = vec![];
    let ctor_info = egraph
        .datatype_info
        .constructors
        .get(&f.to_string())
        .unwrap();
    let mut selector_names = vec![];
    for field in &ctor_info.field_names {
        let sym = &egraph.context.allocate_symbol(field);
        selector_names.push(sym.clone());
    }
    let selector_sorts = ctor_info.field_sorts.clone();
    assert!(subterms.len() == selector_names.len());
    assert!(subterms.len() == selector_sorts.len());
    let terms_selectors = subterms
        .iter()
        .zip(selector_names.into_iter().zip(selector_sorts));



    for (sel_term, (sel_name, sel_sort)) in terms_selectors {
        let sel_app = &egraph.context.app(
            QualifiedIdentifier::simple(sel_name.clone()),
            vec![term.clone()],
            Some(sel_sort),
        );
        let sel_eq = egraph.context.eq(sel_app.clone(), sel_term.clone());
        debug_println!(25, 10, "(assert {})", sel_eq);
        let sel_eq_nnf = sel_eq.nnf(egraph);
        egraph.insert_predecessor(&sel_eq_nnf, None, None, false, None);
        let sel_eq_cnf = sel_eq.cnf_tseitin(egraph); // todo: do I need any more preprocessing

        let clauses = sel_eq_cnf.0.iter().map(|c| c.0.clone());
        vector.extend(clauses) 
    }

    vector
}
