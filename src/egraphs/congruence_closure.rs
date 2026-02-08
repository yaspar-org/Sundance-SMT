//! Classic congruence closure algorithm

use crate::cnf::CNFConversion as _;
use crate::egraphs::proofforest::ProofForestEdge;
use crate::preprocess::check_for_function_bool;
use crate::utils::{fmt_termlist, DeterministicHashMap, DeterministicHashSet};
use yaspar_ir::ast::alg::{CheckIdentifier, QualifiedIdentifier};
use yaspar_ir::ast::{FetchSort, IdentifierKind, Repr, StrAllocator, Term, TermAllocator};

use crate::egraphs::datastructures::{Assertion, ConstructorType::*, DisequalTerm, Predecessor};
use crate::egraphs::egraph::Egraph;
use crate::egraphs::unionfind::ProofTracker;
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
    debug_println!(1, 1, "Term: {}", term);
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
        if let Some(negated_model) = union(
            *t,
            egraph.true_term,
            egraph,
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
        if let Some(negated_model) = union(
            *t,
            egraph.false_term,
            egraph,
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
            let term_lit = egraph.get_lit_from_term(&term);
            debug_println!(19, 0, "trying to get for the term {}", inner_term);
            match egraph.term_constructors.get(&inner_term.uid()).unwrap() {
                Constructor {
                    name,
                    tester_term,
                    hash,
                    level,
                } if egraph.valid_hash(*hash, *level) => {
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
                        let not_tester_term = egraph.context.not(tester_term.clone());
                        let not_term = egraph.context.not(term);
                        let or_not_tester_not_term =
                            egraph.context.or(vec![not_tester_term, not_term]);
                        egraph.insert_predecessor(&or_not_tester_not_term, None, None, false, None);
                        let tester_cnf = or_not_tester_not_term
                            .cnf_tseitin(egraph)
                            .into_iter()
                            .map(|x| x.into_iter().collect::<Vec<_>>())
                            .collect();
                        debug_println!(25, 10, "(assert {})", or_not_tester_not_term,);
                        debug_println!(12, 2, "This gives us {:?}", tester_cnf);
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
                    ); // todo: don't need to clone the term

                    if egraph.lazy_dt {
                        let ctor_info = egraph.datatype_info.constructors.get(&ctor_name).unwrap();
                        let selector_names = &ctor_info.field_names;
                        let selector_sorts = &ctor_info.field_sorts;
                        let selector_name_sorts = selector_names.iter().zip(selector_sorts);
                        let mut selector_apps = vec![];
                        for (sel, sort) in selector_name_sorts {
                            let sym = &egraph.context.allocate_symbol(sel);
                            let sel_id = QualifiedIdentifier::simple(sym.clone()); // todo: maybe just store this in egraph, so I don't have to recompute
                            let sel_app = egraph.context.app(
                                sel_id,
                                vec![inner_term.clone()],
                                Some(sort.clone()),
                            ); // todo: not sure if I should give the sort here
                            selector_apps.push(sel_app);
                        }
                        let ctor_sym = &egraph.context.allocate_symbol(&ctor_name);

                        // have the simple_sorted id for the global case and the simple id for the appp case
                        let ctor_app = if selector_apps.is_empty() {
                            let ctor_id = QualifiedIdentifier::simple_sorted(
                                ctor_sym.clone(),
                                ctor_info.datatype_sort.clone(),
                            ); // todo: not sure if this is the right was to do it, gets printed out as (as ctor ctor) -> I think it doesnt make a difference
                            egraph
                                .context
                                .global(ctor_id, Some(ctor_info.datatype_sort.clone())) //ctor_local, Some(ctor_sort))
                        } else {
                            let ctor_id = QualifiedIdentifier::simple(ctor_sym.clone());
                            let ctor_sort = ctor_info.datatype_sort.clone();
                            egraph.context.app(ctor_id, selector_apps, Some(ctor_sort))
                        };
                        let eq = egraph.context.eq(inner_term, ctor_app);

                        // note Can't do it this way and need to do it the below way otherwise tests/regression/smt_files/edge_cases_quantifiers/predecessor_backtrack_insert5.smt2, etc are wrong
                        // need to investigate why

                        // let imp = egraph.context.implies(vec![term], eq);
                        // let imp_nnf = imp.sundance_nnf(&mut *egraph.context);
                        // debug_println!(24,8, "(assert {})", imp);
                        // egraph.insert_predecessor(&imp_nnf, None, None, true, None);
                        // let mut additional_constraints = check_for_function_bool(&imp_nnf, egraph, false);
                        // let imp_cnf = imp_nnf.cnf_tseitin(&mut *egraph.context); // todo: do I need any more preprocessing

                        // for clause in imp_cnf {
                        //     additional_constraints.push(clause.0);
                        // }
                        // Some(additional_constraints)

                        let eq_nnf = eq.nnf(egraph);
                        debug_println!(14 - 3, 0, "adding in {}", eq_nnf);
                        egraph.insert_predecessor(&eq_nnf, None, None, true, None);

                        let mut additional_constraints =
                            check_for_function_bool(&eq_nnf, egraph, false);
                        let eq_cnf = eq_nnf.cnf_tseitin(egraph); // todo: do I need any more preprocessing
                        assert_eq!(eq_cnf.0.len(), 1);
                        let eq_clause = eq_cnf.0[0].0.clone();
                        assert_eq!(eq_clause.len(), 1);
                        let eq_lit = eq_clause[0];
                        debug_println!(25, 10, "(assert (=> {} {}))", term, eq);

                        additional_constraints.push(vec![-term_lit, eq_lit]);

                        // note we don't actually want to add -term_lit as a condition on the additional constraints
                        // for constraint in &mut additional_constraints {
                        //     constraint.push(-term_lit);
                        // }
                        Some(additional_constraints)
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
            union(t1, t2, egraph, reason, level, fixed, from_quantifier)
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
                leastcommonancestor(t1, t2, egraph, &mut ProofTracker::new())
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
                        leastcommonancestor(t1, t2, egraph, &mut ProofTracker::new())
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
        leastcommonancestor(egraph.true_term, egraph.false_term, egraph, &mut tracker)
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
        for lit in negated_model_terms.clone() {
            debug_println!(7, 4, "{}", egraph.get_term_from_lit(lit));
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
        // todo: support both kinds of testers when we update Yaspar info
        App(f, t, _) if matches!(f.get_kind(), Some(IdentifierKind::Is(_))) && sign => {
            assert_eq!(t.len(), 1);
            // we have to do the following because if let guard is experimental, c.f. https://github.com/rust-lang/rust/issues/51114
            let ctor_name = if let Some(IdentifierKind::Is(sym)) = f.get_kind() {
                sym.clone()
            } else {
                panic!("we just tested it!");
            };
            let inner_term = t[0].clone();
            Assertion::Tester {
                ctor_name: ctor_name.to_string(),
                inner_term,
                term: term.clone(),
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

fn leastcommonancestor_helper(
    u: u64,
    v: u64,
    egraph: &Egraph,
    tracker: &mut ProofTracker,
    indent: usize,
) -> Option<Vec<(u64, u64)>> {
    debug_println!(
        20,
        indent,
        "checking the equality of {} and {}",
        egraph.get_term(u),
        egraph.get_term(v)
    );
    let mut visited = DeterministicHashSet::default();

    // Follow and record the path from u to its root
    let mut path_from_u = vec![];
    let mut curr = u;

    if indent > 100 {
        debug_println!(11, 0, "We have the proof forest :{}", egraph);
        panic!("Should not have this many recusive calls to LCH");
    }
    loop {
        // debug_println!(16, 0, "curr {}", egraph.get_term(curr));
        let parent = egraph.proof_forest[curr as usize].clone();
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

    // Follow path from v until we hit a node visited by u's path
    let mut path_from_v = vec![];
    curr = v;
    let mut parent: ProofForestEdge;
    loop {
        // debug_println!(16, 0, "curr [round 2] {}: {}", egraph.get_term(curr), curr);
        parent = egraph.proof_forest[curr as usize].clone();
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
            // if this happens, they are not in the same equivalence class and thus unequal
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
    // For each pair in the proof path
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
                debug_println!(20, indent + 12, "Congruence ");
                for (t1, t2) in pairs.clone() {
                    debug_println!(
                        20,
                        indent + 12,
                        "{} [{}] ~ {} [{}] ",
                        egraph.get_term(t1),
                        t1,
                        egraph.get_term(t2),
                        t2
                    );
                }
                proof_congruences.push(pairs);
            }
            ProofForestEdge::Equality { term, .. } => {
                if let Some((t1, t2)) = term {
                    // if the term is None, then it comes from setting a term = annotated term, and we do not need it for conflict
                    debug_println!(
                        20,
                        indent + 12,
                        "Equality {} [{}] = {} [{}]",
                        egraph.get_term(t1),
                        t1,
                        egraph.get_term(t2),
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

    // need to handle equalities first then congurences
    for pairs in proof_congruences {
        for pair in pairs {
            if let Some(subproof) =
                leastcommonancestor_helper(pair.0, pair.1, egraph, tracker, indent + 1)
            {
                final_proof.extend(subproof);
            }
        }
    }
    Some(final_proof)
}

pub fn leastcommonancestor(
    u: u64,
    v: u64,
    egraph: &Egraph,
    tracker: &mut ProofTracker,
) -> Option<Vec<(u64, u64)>> {
    debug_println!(
        11,
        1,
        "Finding least common ancestor for {} and {}",
        egraph.get_term(u),
        egraph.get_term(v)
    );
    leastcommonancestor_helper(u, v, egraph, tracker, 0)
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

/// UNION operation for union-find
///
/// As an optimization, could potentially add the tree
/// with smaller depth as a child of tree with larget depth.
/// This will result in the tree depth being bound by log(n)
///
/// Doing the union thing where we combine trees by making y the root
/// and adding edge x -> y. Good for recovering proof at the end,
/// but this could double/triple the max tree size at each iteration
///
/// design decision: don't have eager updates for equivalence class and inverting tree
pub fn union(
    x: u64,
    y: u64,
    egraph: &mut Egraph,
    proof_parent: ProofForestEdge,
    level: usize,
    fixed: bool,
    from_quantifier: bool,
) -> Option<Vec<Vec<i32>>> {
    let x_root = egraph.find(x);
    let y_root = egraph.find(y);
    debug_println!(6, 1, "{}", egraph);
    debug_println!(6, 0, "before1");
    debug_println!(
        22,
        1,
        "Unioning vertices [{}] {}  and [{}] {}  (roots: {} [{}] and {} [{}]) at level {} with {}",
        x,
        egraph.get_term(x),
        y,
        egraph.get_term(y),
        x_root,
        egraph.get_term(x_root),
        y_root,
        egraph.get_term(y_root),
        level,
        proof_parent
    );
    debug_println!(11, 0, "{}", egraph);
    assert_eq!(
        egraph.get_term(x).get_sort(&mut egraph.context),
        egraph.get_term(y).get_sort(&mut egraph.context),
        "We are comparing terms {} and {}",
        egraph.get_term(x),
        egraph.get_term(y)
    );

    if x_root == y_root {
        debug_println!(
            16,
            2,
            "{} and {} are already in the same equivalence class",
            egraph.get_term(x),
            egraph.get_term(y)
        );
        return None;
    }

    // keep track of original proof_parent
    let proof_parent_original = proof_parent.clone();

    // making x the parent of y ~> could also do this based on relative depth of x and y tree
    let proof_parent: ProofForestEdge =
        add_parent(proof_parent, x, y, level, egraph.predecessor_hash);

    let y_root_parent = &egraph.proof_forest[y_root as usize];

    if !fixed {
        // not adding fixed levels to backtracking based on what Armin said
        if !from_quantifier {
            debug_println!(
                16,
                0,
                "BACKTTRACK STACK: adding equalitity between {} and {} with y_root: {}",
                egraph.get_term(x),
                egraph.get_term(y),
                egraph.get_term(y_root)
            );
            egraph.proof_forest_backtrack_stack.push((
                level,
                proof_parent.clone(),
                y_root,
                y_root_parent.clone(),
            ));
            // this gets give to proof forest_patrack with inputs (proof_parent, y_root, y_root_parent, egraph)
        } else {
            debug_println!(
                11,
                0,
                "QUANTIFIER STACK: adding equalitity between {} and {} with y_root: {}",
                egraph.get_term(x),
                egraph.get_term(y),
                egraph.get_term(y_root)
            );
            assert!(
                matches!(proof_parent_original, ProofForestEdge::Congruence { .. }),
                "Expected {} to be a Congruence",
                proof_parent_original
            );
            // if level != 0 {
            egraph.from_quantifier_backtrack_set.insert(
                x,
                (
                    proof_parent_original,
                    y_root_parent.clone(),
                    proof_parent.clone(), // proof_parent_original
                    y_root,
                ),
            );
            // }
            // this gets give to proof forest_patrack with inputs (proof_parent, y_root, y_root_parent, egraph)
        }
    }

    debug_println!(
        16,
        2,
        "Making {} the root of its equivalence class [previously was {}]",
        egraph.get_term(y),
        egraph.get_term(y_root)
    );
    make_root(y, proof_parent, egraph);

    // need to add the new disequalities into x_root
    // TODO: could also clean up some backtracking stuff here, probably want to factor this into its own function
    let (x_root_disequalities_edge, y_root_disequalities_edge) = if x_root > y_root {
        let split = egraph.proof_forest.split_at_mut(x_root as usize);
        (&mut split.1[0], &split.0[y_root as usize])
    } else {
        let split = egraph.proof_forest.split_at_mut(y_root as usize);
        (&mut split.0[x_root as usize], &split.1[0])
    };

    let y_root_disequalities = y_root_disequalities_edge.disequalities();
    let x_root_disequalities = x_root_disequalities_edge.disequalities_mut();

    // when we copy things over, make sure we only copy things over that are valid and that we are updating the hash/level -> this caused some very tricky bugs
    // TODO: write helper functions to make copying over hased things easier
    for (key, value) in y_root_disequalities {
        // make sure we update the disequality level
        if value.hash >= egraph.predecessor_level[value.level]
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
                (level, egraph.predecessor_level[level])
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
                && (x_disequality.hash >= egraph.predecessor_level[x_disequality.level]
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
        egraph.get_term(x),
        egraph.get_term(y),
        egraph.proof_forest[x as usize].disequalities()
    );
    if let Some(disequality) = egraph.check_self_disequality(x_root).clone() {
        debug_println!(
            11,
            0,
            "B. Checking the equality {} = {} with disequality {} != {}",
            egraph.get_term(x),
            egraph.get_term(y),
            egraph.get_term(disequality.original_disequality.0),
            egraph.get_term(disequality.original_disequality.1)
        );
        let mut tracker = ProofTracker::new();
        // tracker.initialize_tracker(egraph.num_vars as u64);
        if let Some(negated_model) = leastcommonancestor(
            disequality.original_disequality.0,
            disequality.original_disequality.1,
            egraph,
            &mut tracker,
        ) {
            let mut model_terms: Vec<i32> = negated_model
                .into_iter()
                .map(|x| -egraph.make_eq(x.0, x.1))
                .collect();
            model_terms.push(-disequality.diseq_lit);
            debug_println!(
                7,
                1,
                "Contradiction found [3]: {:?} [{:?}]",
                model_terms
                    .iter()
                    .map(|x| egraph.get_term_from_lit(*x))
                    .collect::<Vec<_>>(),
                model_terms
            );
            return Some(vec![model_terms]); // Return negated model as the contradiction explanation (todo: ideally would want to have a way to specify this is a model to the thing we pass to, but this is not possible at least with our current setup)
        } else {
            debug_println!(16, 0, "{}", egraph);
            panic!(
                "Should have found a equality between {} [root: {}] and {} [root: {}]",
                egraph.get_term(disequality.original_disequality.0),
                egraph.get_term(egraph.find(disequality.original_disequality.0)),
                egraph.get_term(disequality.original_disequality.1),
                egraph.get_term(egraph.find(disequality.original_disequality.1)),
            );
        }
    }

    union_predecessors(x_root, y_root, egraph, level, fixed, from_quantifier)
}

/// Make vertex the root of its tree
fn make_root(vertex: u64, proof_parent: ProofForestEdge, egraph: &mut Egraph) {
    debug_println!(
        16,
        0,
        "Making {} the root with proof_parent {}",
        egraph.get_term(vertex),
        proof_parent
    );
    let old_parent = egraph.proof_forest[vertex as usize].clone();
    let disequalities = match old_parent {
        ProofForestEdge::Root { disequalities, .. } => disequalities,
        ProofForestEdge::Congruence {
            size: _, // note we don't use size right now, but could in the future
            pairs,
            parent,
            child,
            disequalities,
            level,
            hash,
            children,
        } => {
            assert_eq!(child, vertex);
            make_root(
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
                egraph,
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
            make_root(
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
                egraph,
            );
            disequalities
        }
    };
    let new_proof_parent = proof_parent.set_disequalities(disequalities);
    egraph.proof_forest[vertex as usize] = new_proof_parent;
}

/// Given u and v (roots of u_original and v_original), check the predecessors of
/// each of these and union them if they have become equal
///
/// TODO: I probably actually don't want this to delete all of the predecessors of u because it will screw up backtracking
/// you only have to do it for predecessor terms that are roots of a congruent class
/// once you merge two predecessor states, then you don't need to look at it until you backtrack
///
/// TODO: need to implement a backtracking where I change the predecessor hash
fn union_predecessors(
    u: u64,
    v: u64,
    egraph: &mut Egraph,
    level: usize,
    fixed: bool,
    from_quantifier: bool,
) -> Option<Vec<Vec<i32>>> {
    debug_println!(
        11,
        1,
        "Unioning predecessors of {} [{}, Predecessors: {}] and {} [{}, Predecessors: {}]",
        egraph.get_term(u),
        u,
        fmt_termlist(
            egraph.predecessors[u as usize]
                .keys()
                .map(|x| egraph.get_term(*x))
                .collect::<Vec<_>>()
        ),
        egraph.get_term(v),
        v,
        fmt_termlist(
            egraph.predecessors[v as usize]
                .keys()
                .map(|x| egraph.get_term(*x))
                .collect::<Vec<_>>()
        )
    );

    let predecessors_u = egraph.predecessors[u as usize].clone();
    let predecessors_v = egraph.predecessors[v as usize].clone();

    let mut canonical_forms_u: DeterministicHashMap<(String, Vec<u64>), Vec<(Vec<u64>, u64)>> =
        DeterministicHashMap::default();

    // BTreeMap already provides deterministic iteration order
    for (pred_u_key, predecessor_u) in predecessors_u.iter() {
        if !egraph.valid_hash(predecessor_u.hash, predecessor_u.level) {
            debug_println!(
                11,
                2,
                "CANONICAL_FORMS_U: Skipping predecessor {} of {} [original: {}] as it has hash {} at level {} and correct hash is {}",
                egraph.get_term(predecessor_u.predecessor),
                egraph.get_term(u),
                egraph.get_term(predecessor_u.inner_term),
                predecessor_u.hash,
                predecessor_u.level,
                egraph.predecessor_level[predecessor_u.level]
            );
            egraph.predecessors[u as usize].remove(pred_u_key);
            continue;
        }
        debug_println!(
            11,
            2,
            "1.We are in union_predecessors trying to get term for {}",
            egraph.get_term(predecessor_u.predecessor)
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

        if let Some((original_subterms, canonical_form)) =
            egraph.get_canonical_form(predecessor_u.predecessor, level)
        {
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

    // basically the issue was that in `union_predecessors` when you create a `canonical_term_u`,
    // you fix it, but then you compare to a for loop iterating through all terms in v and iteratively
    // computing the canonical_term_v, but this could change as you are iterating through the loop
    // so we want to precompute the canonical terms of v
    let predecessor_v_canonical_forms = predecessors_v
        .iter()
        .map(|(pred_v_key, predecessor_v)| {
            (
                pred_v_key,
                predecessor_v,
                egraph.get_canonical_form(predecessor_v.predecessor, level),
            )
        })
        .collect::<Vec<_>>();

    // moving predecessors from v to u
    for (pred_key, pred_val) in predecessors_v.clone() {
        debug_println!(
            11,
            0,
            "We are are adding predecessor {} (of  {}) to {} [level: {}, hash: {}]",
            egraph.get_term(pred_key),
            egraph.get_term(pred_val.inner_term),
            egraph.get_term(u),
            level,
            egraph.predecessor_hash
        );
        let new_pred = Predecessor {
            level,
            hash: egraph.predecessor_hash,
            predecessor: pred_key,
            inner_term: pred_val.inner_term,
        };
        egraph.add_predecessor(u, pred_key, new_pred);
    }

    for (pred_v_key, predecessor_v, canonical_form_v) in predecessor_v_canonical_forms {
        if !egraph.valid_hash(predecessor_v.hash, predecessor_v.level) {
            debug_println!(
                11,
                5,
                "Skipping predecessor {} of {} [original: {}] as it has hash {} at level {} and correct hash is {}",
                egraph.get_term(predecessor_v.predecessor),
                egraph.get_term(v),
                egraph.get_term(predecessor_v.inner_term),
                predecessor_v.hash,
                predecessor_v.level,
                egraph.predecessor_level[predecessor_v.level]
            );
            debug_println!(
                11,
                5,
                "The current level is {} and hash is {}",
                level,
                egraph.predecessor_hash
            );
            egraph.predecessors[v as usize].remove(pred_v_key);
            continue;
        }
        debug_println!(
            11,
            3,
            "L. We are in union_predecessors trying to get term for {}",
            egraph.get_term(predecessor_v.predecessor)
        );

        // checking if the ite leads to a contradiction
        // if let Some(negated_model) =
        //     union_process_ite(&egraph.get_term(predecessor_v.predecessor), egraph, level, from_quantifier)
        // {
        //      debug_println!(
        //         11,
        //         4,
        //         "N. [exiting union_pred] of {} andn {} Contradiction found in union_predecessors, we have the following negated_model: {:?}",
        //         egraph.get_term(u),
        //         egraph.get_term(v),
        //         negated_model
        //     );
        //     return Some(negated_model);
        // }

        if let Some((original_subterms, canonical_form)) = canonical_form_v {
            debug_println!(
                11,
                6,
                "3. We are in union_predecessors for v and have canonical form {:?} for {}",
                canonical_form,
                egraph.get_term(predecessor_v.predecessor)
            );
            if let Some(u_forms) = canonical_forms_u.get(&canonical_form) {
                debug_println!(5, 0, "We have the following u_forms {:?}", u_forms);
                for (u_original_subterms, canonical_form_u) in u_forms {
                    debug_println!(
                        16,
                        0,
                        "We are actually merging the two predecessors {} and {}",
                        egraph.get_term(*canonical_form_u),
                        egraph.get_term(predecessor_v.predecessor)
                    );
                    debug_println!(16, 0, "We have u_original_subterms: ");
                    for term in u_original_subterms {
                        debug_println!(16, 4, "{}", egraph.get_term(*term));
                    }

                    debug_println!(16, 0, "We have original_subterms: ");
                    for term in original_subterms.clone() {
                        debug_println!(16, 4, "{}", egraph.get_term(term));
                    }

                    let terms_pairwise = u_original_subterms
                        .clone()
                        .into_iter()
                        .zip(original_subterms.clone().into_iter())
                        .collect::<Vec<(u64, u64)>>();
                    let proof_parent = ProofForestEdge::Congruence {
                        size: 0,
                        pairs: terms_pairwise,
                        parent: 0,
                        child: 0,
                        disequalities: DeterministicHashMap::new(),
                        level,
                        hash: egraph.predecessor_hash,
                        children: DeterministicHashSet::new(),
                    }; // TODO: I can't have a child of -1 anymore, but I think doing it like this is correct

                    // TODO: this is a hackish way to add this if the equality occurs in the formula
                    if let Some(negated_model) = union_process_assignment(
                        // u_original,
                        // v_original,
                        *canonical_form_u,
                        predecessor_v.predecessor,
                        egraph,
                        proof_parent,
                        level,
                        fixed,
                        from_quantifier,
                    ) {
                        debug_println!(
                            11,
                            5,
                            "[exiting union_pred] of {} and {} In union_predecessors, we have the following negated_model: {:?}",
                            egraph.get_term(u),
                            egraph.get_term(v),
                            negated_model
                        );
                        return Some(negated_model);
                    }
                }
            }
        }
    }
    debug_println!(
        11,
        0,
        "[exiting union_pred] of {} and {} with None",
        egraph.get_term(u),
        egraph.get_term(v)
    );
    None
}

/// Helper function called by union_predecessors that represents a recursive call
/// to union
///
/// TODO: would be cleaner to have union_predecessors just call union
fn union_process_assignment(
    x: u64,
    y: u64,
    egraph: &mut Egraph,
    proof_parent: ProofForestEdge,
    level: usize,
    fixed: bool,
    from_quantifier: bool,
) -> Option<Vec<Vec<i32>>> {
    debug_println!(6, 0, "before4");
    let new_assignment = egraph.context.eq(egraph.get_term(x), egraph.get_term(y));
    // if there is a new assignment, we need to check if the equality term exists, if it does we need to work on that
    // otherwise we can just consider the union of these two terms
    if let Some(new_assignment_lit) = egraph.cnf_cache.var_map.get(&new_assignment.uid()) {
        // note we don't want reason to be the above thing because the explanation is still the same as teh explanation before
        let reason = proof_parent;
        debug_println!(
            16,
            0,
            "We are in union_process_assignment trying to process assignment for x: {} [{}] and y: {} [{}] and fixed {}",
            egraph.get_term(x),
            x,
            egraph.get_term(y),
            y,
            fixed
        );
        // if let ProofForestEdge::Congruence{pairs, ..} = proof_parent && pairs.len() == 1 {
        //     debug_println!(
        //     16,
        //     0,
        //     "We have x_original: {} [{}] and y_original {} [{}] and Congruence with {} [{}] and {} [{}]",
        //     egraph.get_term(x_original),
        //     x_original,
        //     egraph.get_term(y_original),
        //     y_original,
        //     egraph.get_term(pairs[0].0),
        //     pairs[0].0,
        //     egraph.get_term(pairs[0].1),
        //     pairs[0].1
        //     )
        // }
        let negated_model_additional_constraints_opt = process_assignment(
            *new_assignment_lit,
            egraph,
            level,
            false,
            from_quantifier,
            Some(reason),
        );
        // assert!(additional_constraints_opt.is_none()); // this should be done becaue right now we only get new constraints for a datatype literal
        if let Some(negated_model) = negated_model_additional_constraints_opt {
            debug_println!(
                6,
                0,
                "We have the following negated_model: {:?}",
                negated_model
            );
            return Some(negated_model);
        };
    } else {
        debug_println!(
            16,
            0,
            "We are in union_process_assignment trying to union {} and {} with fixed {}",
            egraph.get_term(x),
            egraph.get_term(y),
            fixed
        );
        if let Some(negated_model) =
            union(x, y, egraph, proof_parent, level, fixed, from_quantifier)
        {
            return Some(negated_model);
        }
    };
    None
}

pub fn proof_forest_backtrack(
    equality: ProofForestEdge,
    y: u64,
    y_parent: ProofForestEdge,
    egraph: &mut Egraph,
) {
    let child = &get_child(&equality);
    let child_edge = egraph.proof_forest[*child as usize].clone();
    let parent = &get_parent(&equality);
    let parent_edge = egraph.proof_forest[*parent as usize].clone();

    assert_eq!(egraph.find(*child), egraph.find(*parent));

    debug_println!(
        16,
        0,
        "Backtracking on {} with child {} and parent {} and y_term {}",
        equality,
        egraph.get_term(*child),
        egraph.get_term(*parent),
        egraph.get_term(y)
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
        // if this is the case, the edge has been reversed at some point
        // and the child is actually the parent
        debug_println!(6, 0, "we are reversing the edge");
        debug_println!(10, 0, "{}", egraph);
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
        egraph.get_term(*child),
        egraph.predecessors[*child as usize]
    );

    let childs_child = get_child(&child_edge);

    // we are adding disequalities from the "parent" edge to the child
    let mut new_disequalities = DeterministicHashMap::new();
    for (k, v) in child_edge.disequalities().iter() {
        if egraph.valid_hash(v.hash, v.level) {
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

    // do the same for predecessors
    let child_root = ProofForestEdge::Root {
        size: 0,
        child: childs_child,
        disequalities: new_disequalities,
        children: DeterministicHashSet::new(), // todo: need to actually update children
    };

    egraph.proof_forest[*child as usize] = child_root;

    // when backtracking undo the make_root from union
    debug_println!(
        16,
        0,
        "Making {} the root on a backtrack",
        egraph.get_term(y)
    );
    make_root(y, y_parent, egraph);

    // for (pred_key, pred_value) in _ {
    //     egraph.add_predecessor(y, new_pred_key, new_pred);
    // }
}
