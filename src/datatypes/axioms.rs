// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::vec;

use yaspar_ir::ast::alg::{ConstructorDec, DatatypeDec, Identifier, Index, QualifiedIdentifier};
use yaspar_ir::ast::{ATerm::*, CheckedApi, FetchSort, Sort, Str, TermAllocator};
use yaspar_ir::ast::{ObjectAllocatorExt, Repr, StrAllocator, Term};

use crate::cnf::CNFConversion as _;
use crate::debug_println;
use crate::egraphs::datastructures::ConstructorType;
use crate::egraphs::egraph::Egraph;
use crate::preprocess::check_for_function_bool;

/// For a term of datatype sort, we want to learn the following axioms:
/// 1. isC1(t) \/ ... \/ isCm(t) where C1, ..., Cm are the constructors of the datatype
/// 2. (is-f t) => t = f(f^0(t) ... f^m(t)) for each constructor f of the   datatype where f^0, ..., f^m are the selectors of f
/// 3. (is-f t) => t = f(f^0(t) ... f^m(t)) for each constructor f of the datatype where f^0, ..., f^m are the selectors of f (by default we add this lazily based on the assignment in term_constructors)
/// 4. /\_i=1^k f_i(f(t1, ... tk)) = t_i for term = f(t1, ..., tk) where f is a constructor with selectors f_1, ..., f_k and subterms t1, ..., tk.
///    (done lazily)
/// 5. We also need to ~isCi(t) \/ ~isCj(t) for each pair of distinct constructors Ci and Cj of the datatype (we do this lazily based on the assignment in term_constructors)
///    Note that we also need to include the datatype axioms for the selectors if they are of datatype sort, so we need to recursively call find_datatype_axioms on the selector applications as well.
pub fn find_datatype_axioms(
    term: &Term, // must be a datatype term
    sort: &Sort, // the sort of the given term
    egraph: &mut Egraph,
    from_quantifier: bool, // this is necessary because of the calls to insert_predecessor where we need to know whether the axiom is from a quantifier or not
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
        // the sort is not a datatype
        return vector;
    };

    // Step 1. Store the constructor in term_constructors
    let num = term.uid();
    if egraph.datatype_axioms_applied.contains(&num) {
        return vector;
    }
    egraph.datatype_axioms_applied.insert(num);

    if !egraph.term_constructors.contains_key(&num) {
        add_to_term_constructors(egraph, term);
    }

    // Step 2. Learn the clause isC1(t) \/ ... \/ isCm(t)
    let tester_apps = learn_exactly_one_tester_clause(egraph, term, &dt_dec, from_quantifier);
    vector.extend(tester_apps);

    // Step 2.5. Learn the constraint (is-f t) => t = f(f^0(t) ... f^m(t))
    // as long as we are not doing lazy datatypes
    if !egraph.lazy_dt {
        let ctor_selector_clauses = learn_ctors_selector_clauses(egraph, term, sort, &dt_dec);
        vector.extend(ctor_selector_clauses);
    }

    // Step 3. Learn the constraint  /\_i=1^k f_i(f(t1, ... tk)) = t_i
    if let App(f, terms, _) = term.repr()
        && egraph.datatype_info.constructors.contains_key(f.id_str())
    {
        let selector_ctor_clauses =
            learn_selector_ctor_clause(egraph, term, f.id_str(), terms, &dt_dec, from_quantifier);
        vector.extend(selector_ctor_clauses);
    }
    vector
}

/// Adds a term to term_constructors which keeps track of the correct constructor of each term.
/// Note that the axiom `~isCi(t) \/ ~isCj(t)` is added lazily based on the assignment in term_constructors
/// if the term is of the form C(t1, ..., tm) where C is a constructor, we add it as a Constructor with the tester term (_ is C) t
/// otherwise, we add it as Uninitialized and we will update it later if we learn that
fn add_to_term_constructors(egraph: &mut Egraph, term: &Term) {
    let num = term.uid();
    // todo: missing Global case?
    if let App(f, _, _) = term.repr()
        && egraph.datatype_info.constructors.contains_key(f.id_str())
    {
        let bool_sort = egraph.bool_sort();
        let is_symbol = egraph.allocate_symbol("is");

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

/// For a term of datatype sort, learn the clause isC1(t) \/ ... \/ isCm(t) where C1, ..., Cm are the constructors of the datatype
/// if the term is of the form C(t1, ..., tm) where C is a constructor, we also add the clause (isC1(t) \/ ... \/ isCm(t)) /\ isC(t) where C is the constructor of the term
fn learn_exactly_one_tester_clause(
    egraph: &mut Egraph,
    term: &Term,
    dt_dec: &DatatypeDec<Str, Sort>,
    from_quantifier: bool,
) -> Vec<Vec<i32>> {
    // Collect all constructors for this datatype sort
    let is_symbol = egraph.allocate_symbol("is");
    let bool_sort = egraph.bool_sort();
    let mut vector = vec![];

    let mut tester_apps = vec![];

    // Create tester applications for each constructor: (_ is ConstructorName) term
    for ctor in &dt_dec.constructors {
        let ctor_name = &ctor.ctor;
        // Create the tester identifier: (_ is ConstructorName)

        let tester_identifier = Identifier {
            symbol: is_symbol.clone(),
            indices: vec![Index::Symbol(ctor_name.clone())],
        };

        // todo: also need (is-ConstructorName term)
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
        tester_apps.pop().unwrap()
    } else {
        egraph.or(tester_apps)
    };
    debug_println!(12, 0, "TESTER OR CASE");
    debug_println!(25, 10, "(assert {})", tester_or);
    egraph.insert_predecessor(&tester_or, None, None, from_quantifier, None);
    let tester_cnf = tester_or.cnf_tseitin(egraph).into_iter().map(|x| x.0);
    vector.extend(tester_cnf);
    vector
}

/// For a term of datatype sort, learn the clause (is-f t) => t = f(f^0(t) ... f^m(t)) for each constructor f of the datatype where f^0, ..., f^m are the selectors of f
fn learn_ctors_selector_clauses(
    egraph: &mut Egraph,
    term: &Term,
    sort: &Sort,
    dt_dec: &DatatypeDec<Str, Sort>,
) -> Vec<Vec<i32>> {
    let mut vector = vec![];

    for ctor in &dt_dec.constructors {
        let ctor_selector_clauses = learn_ctor_selector_clauses(egraph, term, ctor, sort, false);
        vector.extend(ctor_selector_clauses);
    }
    vector
}

/// For a term of datatype sort, learn the clause (is-f t) => t = f(f^0(t) ... f^m(t)) for each constructor f of the datatype where f^0, ..., f^m for a specific constructor f are the selectors of f
pub fn learn_ctor_selector_clauses(
    egraph: &mut Egraph,
    term: &Term,
    ctor: &ConstructorDec<Str, Sort>,
    sort: &Sort,
    from_quantifier: bool,
) -> Vec<Vec<i32>> {
    let is_symbol = egraph.allocate_symbol("is");
    let bool_sort = egraph.bool_sort();

    let ctor_name = &ctor.ctor;
    let tester_identifier = Identifier {
        symbol: is_symbol.clone(),
        indices: vec![Index::Symbol(ctor_name.clone())],
    };
    let tester_app = egraph.app(
        tester_identifier.into(),
        vec![term.clone()],
        Some(bool_sort.clone()),
    );

    let mut selector_apps = vec![];
    for sel in &ctor.args {
        let sel_app = egraph
            .context
            .typed_simp_app(sel.0.clone(), vec![term.clone()])
            .expect("type checking invariance violation: constructors");
        selector_apps.push(sel_app);
    }

    // have the simple_sorted id for the global case and the simple id for the appp case
    let ctor_id = QualifiedIdentifier::simple(ctor_name.clone());
    let ctor_app = if selector_apps.is_empty() {
        egraph.global(ctor_id, Some(sort.clone()))
    } else {
        egraph.app(ctor_id, selector_apps, Some(sort.clone()))
    };
    let eq = egraph.eq(term.clone(), ctor_app);

    let eq_nnf = eq.nnf(egraph);
    egraph.insert_predecessor(&eq_nnf, None, None, true, None);

    // note that additioanl constraints are needed for `datatypes/ctor_sel_term_additional_dt_constraints3.smt2`
    let mut vector = check_for_function_bool(&eq_nnf, egraph, false);
    let eq_cnf = eq_nnf.cnf_tseitin(egraph);
    assert_eq!(eq_cnf.0.len(), 1);
    let eq_clause = eq_cnf.0[0].0.clone();
    assert_eq!(eq_clause.len(), 1);

    let imp = egraph.implies(vec![tester_app], eq);
    debug_println!(25, 10, "(assert {})", imp);
    let imp_nnf = imp.nnf(egraph);
    egraph.insert_predecessor(&imp_nnf, None, None, from_quantifier, None);
    let imp_cnf = imp.cnf_tseitin(egraph);
    let clauses = imp_cnf.0.iter().map(|c| c.0.clone());
    vector.extend(clauses);
    vector
}

/// We are learning the clause /\_i=1^k f_i(f(t1, ... tk)) = t_i
/// for term = f(t1, ..., tk) where f is a constructor with selectors f_1, ..., f_k and subterms t1, ..., tk.
/// Note that we also need to include the datatype axioms for the selectors if they are of datatype sort, so we call find_datatype_axioms on each selector application as well
fn learn_selector_ctor_clause(
    egraph: &mut Egraph,
    term: &Term,
    f: &Str,
    subterms: &[Term],
    dt_dec: &DatatypeDec<Str, Sort>,
    from_quantifier: bool,
) -> Vec<Vec<i32>> {
    let mut vector = vec![];
    let ctor = dt_dec
        .constructors
        .iter()
        .find(|ctor| ctor.ctor == *f)
        .unwrap();

    assert_eq!(subterms.len(), ctor.args.len());

    for (sel_term, sel) in subterms.iter().zip(ctor.args.iter()) {
        let so = sel_term.get_sort(egraph);
        let sel_app = &egraph.app(
            QualifiedIdentifier::simple(sel.0.clone()),
            vec![term.clone()],
            Some(so),
        );
        let sel_eq = egraph.eq(sel_app.clone(), sel_term.clone());
        debug_println!(25, 10, "(assert {})", sel_eq);
        let sel_eq_nnf = sel_eq.nnf(egraph);
        egraph.insert_predecessor(&sel_eq_nnf, None, None, from_quantifier, None);
        let sel_eq_cnf = sel_eq.cnf_tseitin(egraph);
        let clauses = sel_eq_cnf.into_iter().map(|c| c.0);
        vector.extend(clauses)
    }
    vector
}

/// Learn the clause ~isCi(t) \/ ~isCj(t) for each pair of distinct constructors Ci and Cj of the datatype based on the assignment in term_constructors
/// This is called lazily during the congruence_closure algorithm
pub fn learn_or_not_term_tester_term(
    egraph: &mut Egraph,
    term: Term,
    tester_term: Term,
    from_quantifier: bool,
) -> Vec<Vec<i32>> {
    let not_tester_term = egraph.not(tester_term.clone());
    let not_term = egraph.not(term);
    let or_not_tester_not_term = egraph.or(vec![not_tester_term, not_term]);
    egraph.insert_predecessor(&or_not_tester_not_term, None, None, from_quantifier, None);
    let tester_cnf = or_not_tester_not_term
        .cnf_tseitin(egraph)
        .into_iter()
        .map(|x| x.0)
        .collect();
    debug_println!(25, 10, "(assert {})", or_not_tester_not_term,);
    debug_println!(12, 2, "This gives us {:?}", tester_cnf);
    tester_cnf
}
