//! Instantiation of quantifiers

use std::cell::RefCell;
use std::rc::Rc;

use crate::cnf::CNFConversion as _;
use crate::egraphs::datastructures::Polarity;
use crate::egraphs::egraph::Egraph;
use crate::preprocess::check_for_function_bool;
use crate::proof::proof_tracer::SMTProofTracker;
use crate::quantifiers::skolem::skolemize;
use crate::utils::{DeterministicHashMap, DeterministicHashSet};
use yaspar_ir::ast::ATerm::{
    And, Annotated, App, Constant, Distinct, Eq, Exists, Forall, Global, Implies, Ite, Let, Local,
    Matching, Not, Or,
};
use yaspar_ir::ast::{Attribute, FetchSort, HasArena, LetElim, Repr, Term, TermAllocator};

#[derive(Debug, Clone)]
pub enum QuantifierInstance {
    Instantiation { clause: Vec<i32> },
    Skolemization { clause: Vec<i32> },
}

/// Returns a list of quantifier instantiation given the assignment and current state of the egraph
///  
/// TODO: level is only used for printing, can get rid of it later
/// (could use it for actiavte_bits, but right now we are activating everything at level 0)
pub fn instantiate_quantifiers(
    egraph: &mut Egraph,
    proof_tracker: &Rc<RefCell<SMTProofTracker>>,
    assignments: &Vec<i32>,
    level: usize,
) -> Vec<QuantifierInstance> {
    let quantifiers = &egraph.quantifiers.clone();
    let mut instantiations = vec![];
    debug_println!(24, 0, "Starting a matching round");
    for quantifier in quantifiers {
        debug_println!(
            19,
            0,
            "We have the quantifier {}",
            egraph.get_term(quantifier.id)
        );
        // check if the quantifier is assigned
        let quantifier_literal = egraph.get_lit_from_u64(quantifier.id);
        assert!(quantifier_literal != 0); // todo: note I think this should actually always be positive but not sure
        let quantifier_assignment = assignments[quantifier_literal.unsigned_abs() as usize];

        // if the quantifier is unsassigned, we can skip it
        if quantifier_assignment == 0
        // || (quantifier_assignment > 0 && quantifier_literal < 0)
        // || (quantifier_assignment < 0 && quantifier_literal > 0)
        {
            debug_println!(12, 0, "after4");
            debug_println!(
                6,
                0,
                "We are skipping the quantifier {} with quantifier_literal {} and quantifier_assignment {} | assignments {:?}",
                egraph.get_term(quantifier.id),
                quantifier_literal,
                quantifier_assignment,
                assignments
            );
            continue;
        }

        // if an odd number of these is true -> XOR true -> skolemize
        // if an even number of these is true -> XOR false -> instantiate
        let quantifier_polarity = (quantifier_assignment > 0)
            ^ (quantifier_literal > 0)
            ^ (quantifier.polarity == Polarity::Existential);

        // if the quantifier in a negative polarity or we doin g ddsmt optimizations, and we haven't skolemized it yet, then we skolemize it
        // todo: replace egraph.added_skolemizations. with the skolemized flag in the quantifier
        if (quantifier_polarity || egraph.eager_skolem)
            && !egraph.added_skolemizations.contains(&quantifier.id)
        {
            debug_println!(
                6,
                0,
                "We are skolemizing the quantifier {} with quantifier_literal {} and quantifier_assignment {} | assignments {:?}",
                egraph.get_term(quantifier.id),
                quantifier_literal,
                quantifier_assignment,
                assignments
            );

            let term = egraph.get_term(quantifier.id);
            // let negated_term =
            //     if let Universal = quantifier.polarity {egraph.cnfenv.context.not(term)} else {term};

            let polarity = quantifier.polarity == Polarity::Universal;

            // todo: replace this with the skolemized flag in the quantifier
            if egraph.added_skolemizations.contains(&quantifier.id) {
                continue;
            }

            let (skolemized_quantifier, skolem_vars) =
                skolemize(&term, &mut egraph.cnfenv.context, polarity);

            egraph.added_skolemizations.insert(quantifier.id);

            let skolemized_quantifier: Term =
                skolemized_quantifier.let_elim(&mut egraph.cnfenv.context);
            // let (skolemized_quantifier, _) = skolemize(&skolemized_quantifier, egraph.cnfenv.context, &mut egraph.skolem_counter);
            let skolemized_quantifier = skolemized_quantifier.nnf(&mut egraph.cnfenv);
            let additional_constraints =
                check_for_function_bool(&skolemized_quantifier, egraph, true);
            debug_println!(19, 0, "we are skolemizing {}", term);
            debug_println!(26, 0, "(assert {})", skolemized_quantifier);
            debug_println!(
                24,
                8,
                "from quantifier {} [{}]",
                egraph.get_term(quantifier.id),
                quantifier.id
            );

            // note that from_quantifier is true here
            egraph.insert_predecessor(&skolemized_quantifier, None, None, true, None);
            let clauses = skolemized_quantifier.cnf_tseitin(&mut egraph.cnfenv);

            // learning (not \forall P(x)) => P(c)
            // equivalent to \forall P(x) \/ P(c)
            // if it comes from existential, it becomes (not \exists P(x)) \/ P(c)
            let quantifier_literal = if quantifier.polarity == Polarity::Universal {
                quantifier_literal
            } else {
                -quantifier_literal
            };

            let skolemized_term_literal = egraph.get_lit_from_term(&skolemized_quantifier);

            let quantifier_implies_skolemization_clause =
                vec![quantifier_literal, skolemized_term_literal];
            proof_tracker.borrow_mut().add_skolem_clause(
                quantifier_implies_skolemization_clause.clone(),
                Some(skolem_vars.clone()),
            );
            // this is the only skolemization clause we need to assume in the proof. Everything else is just a theory literal
            instantiations.push(QuantifierInstance::Skolemization {
                clause: quantifier_implies_skolemization_clause,
            });

            // todo: ideally, we want a whole term that is implied via skolemization and is assumed to be true and then everything else can still be checked
            for clause in clauses {
                let mut clause = clause.0;
                clause.push(-skolemized_term_literal);

                // only want the declaration on the first go around
                // if first {
                //     proof_tracker.borrow_mut().add_skolem_clause(clause.clone(), Some(skolem_vars.clone()));
                //     first = false;
                // } else {
                //     proof_tracker.borrow_mut().add_skolem_clause(clause.clone(), None);
                // }
                instantiations.push(QuantifierInstance::Skolemization { clause })
            }

            for mut clause in additional_constraints {
                clause.push(-skolemized_term_literal);
                // proof_tracker.borrow_mut().add_skolem_clause(clause.clone(), None);
                instantiations.push(QuantifierInstance::Skolemization { clause })
            }
        }

        // if this was a skolemization case, we don't want to instantiate
        //
        if quantifier_polarity {
            continue;
        }

        debug_println!(
            19,
            0,
            "instantiating the quantifier {}",
            egraph.get_term(quantifier.id)
        );
        let triggers = &quantifier.triggers;
        // note we consider patterns in a multipattern conjunctively and multipatterns in a trigger disjunctively
        for multipattern in triggers {
            let body = quantifier.body;
            let trigger_term_pairs = multipattern.iter().map(|t| (*t, None)).collect::<Vec<_>>();

            let mut assignments = DeterministicHashMap::default();
            debug_println!(12, 0, "after8");
            debug_println!(
                19,
                0,
                "About to match quantifier body {} with trigger {:?}",
                egraph.get_term(body),
                trigger_term_pairs
            );
            debug_println!(12, 0, "after9");
            let list_assignments = match_term(&mut assignments, trigger_term_pairs, egraph);

            if list_assignments.is_empty() {
                debug_println!(
                    24,
                    0,
                    "No substitutions for {}",
                    egraph.get_term(quantifier.id)
                );
            }

            debug_println!(7, 0, "We have the following list of assignments:");
            let mut substitutions = vec![];
            for (subs, activation_depth) in list_assignments.iter() {
                // todo: maybe need to come up with a more efficient representation than adding in subs
                // but I don't want to add in the substituted term for two reasons: (1) I want to avoid
                // calling substitute when I don't need to and (2) if a term contains a quantifier, two
                // equivalent terms will actually be unequal
                // maybe I eventually want to do something in the match_term function
                // we are doing a lot of redundant work. It would be nice to have something
                // like semi-naive evaluation for datalog
                if let Some(set) = egraph.added_instantiations.get(&quantifier.id)
                    && set.contains(subs)
                {
                    // println!("Skipping the instantiation {} for {}", t, egraph.get_term(quantifier.id));
                    continue;
                }
                egraph
                    .added_instantiations
                    .entry(quantifier.id)
                    .or_default()
                    .insert(subs.clone());

                debug_println!(22, 0, "The body is {}", body);
                debug_println!(22, 0, "The assignment is");
                for sub in subs {
                    debug_println!(22, 4, "{} |-> {}", sub.0, sub.1)
                }
                debug_println!(6, 0, "before12");
                let substituted_term = substitute(&egraph.get_term(body), subs, egraph);
                substitutions.push((substituted_term, activation_depth, subs));
            }

            if substitutions.is_empty() {
                debug_println!(
                    6,
                    0,
                    "We are skipping the quantifier {} because it has no substitutions",
                    egraph.get_term(quantifier.id)
                );
                continue;
            }

            debug_println!(6, 0, "Starting to look at substitutions");
            debug_println!(6, 0, "{}", egraph);
            for (t, &activation_depth, _) in substitutions {
                // skipping instantiations that have already been added
                // TODO: need to come up with a more efficient way to do this
                // TODO: have egraph.added_instantiations as a string right now, really want to go back to u32

                // if this came from a negated existential, we have to negate the term

                // println!("original_t: {}", t);
                let t = if quantifier.polarity == Polarity::Existential {
                    egraph.cnfenv.context.not(t)
                } else {
                    t
                };

                debug_println!(
                    22,
                    0,
                    "We are adding the instantiation {} for quantifier {} at level {}",
                    t.clone(),
                    egraph.get_term(quantifier.id),
                    level
                );

                debug_println!(4, 0, "We have the term {} with id {}", t, t.uid());

                // eliminating lets
                let let_elim_term = t.let_elim(&mut egraph.cnfenv.context);

                debug_println!(
                    8,
                    0,
                    "{} is an instantiation of {} at depth {}",
                    let_elim_term,
                    egraph.get_term(quantifier.id),
                    activation_depth
                );

                let nnf_term = let_elim_term.nnf(&mut egraph.cnfenv);

                debug_println!(26, 4, "(assert {})", nnf_term.clone());
                debug_println!(
                    24,
                    8,
                    "from quantifier {} [{}]",
                    egraph.get_term(quantifier.id),
                    quantifier.id
                );

                debug_println!(
                    7,
                    0,
                    "We have the nnf term {} with id {}",
                    nnf_term,
                    nnf_term.uid()
                );

                // note we do this after nnf
                // this might lead to weirdness when you have equality of booleans not being represented in egraph
                // but it should be fine. This is necessary becasue we need to look up lits
                // todo: also might be less efficient as well because we are losing structure from original formula in the egraph
                egraph.insert_predecessor(&nnf_term, None, None, true, None);

                let cnf_term = nnf_term.cnf_tseitin(&mut egraph.cnfenv);
                debug_println!(7, 0, "We have the cnf term {:?}", cnf_term);

                let mut clauses: Vec<_> = cnf_term
                    .clone()
                    .into_iter()
                    .map(|x| x.into_iter().collect::<Vec<_>>())
                    .collect();

                let quantifier_literal = egraph.get_lit_from_u64(quantifier.id);

                let quantifier_literal = if quantifier.polarity == Polarity::Universal {
                    -quantifier_literal
                } else {
                    quantifier_literal
                };

                // basically the final clause from cnf is the top level term
                // we want to say quantifier => top level term
                let mut final_clause = clauses.pop().unwrap();
                final_clause.push(quantifier_literal);
                clauses.push(final_clause);

                // the bug comes from the additional constraints
                // basically the additional constraints are valid lits -> converted to valid u64, but may not be in the actual term mapping
                // it should be added in insert_predecessor which calls get_or_insert which adds into terms_list
                let additional_constraints = check_for_function_bool(&nnf_term, egraph, true);
                clauses.extend(additional_constraints);

                // could activate bits here (the level should not be 0)
                // activate_bits(&t, 0, egraph);

                for clause in clauses {
                    let instantiation = QuantifierInstance::Instantiation { clause };
                    instantiations.push(instantiation); // TODO: I would prefer to push t.uid() here, but it seems like the uid is not getting adding to the terms list
                }
            }
        }
    }
    instantiations
}

/// Given a term and a list of substitutions, substitutes variables into term
///
/// TODO: it might be more efficient to take in a Term instead of a i32
/// TODO: dont need to return new term
fn substitute(
    term: &Term,
    substitutions: &DeterministicHashMap<String, Term>,
    egraph: &mut Egraph,
) -> Term {
    match term.repr() {
        Constant(..) => term.clone(),
        Global(_, _) => term.clone(),
        Local(local) => {
            if let Some(v) = substitutions.get(&local.symbol.to_string()) {
                v.clone()
            } else {
                term.clone()
            }
        }
        App(qualified_identifier, args, sort) => {
            let new_args = args
                .iter()
                .map(|arg| substitute(arg, substitutions, egraph))
                .collect::<Vec<_>>();

            egraph
                .cnfenv
                .context
                .app(qualified_identifier.clone(), new_args, sort.clone())
        }
        And(items) => {
            let new_items = items
                .iter()
                .map(|item| substitute(item, substitutions, egraph))
                .collect::<Vec<_>>();
            egraph.cnfenv.context.and(new_items)
        }
        Or(items) => {
            let new_items = items
                .iter()
                .map(|item| substitute(item, substitutions, egraph))
                .collect::<Vec<_>>();
            egraph.cnfenv.context.or(new_items)
        }
        Eq(a, b) => {
            let (new_a, new_b) = (
                substitute(a, substitutions, egraph),
                substitute(b, substitutions, egraph),
            );
            egraph.cnfenv.context.eq(new_a, new_b)
        }
        Not(t) => {
            let new_t = substitute(t, substitutions, egraph);
            egraph.cnfenv.context.not(new_t)
        }
        Implies(items, implicant) => {
            // assert!(items.len() == 1);
            let new_items = items
                .iter()
                .map(|item| substitute(item, substitutions, egraph))
                .collect();
            let new_implicant = substitute(implicant, substitutions, egraph);

            egraph.cnfenv.context.implies(new_items, new_implicant)
        }
        Forall(var_bindings, middle_term) => {
            // TODO: I don't know if this is actually correct. Will have to investigate the nested forall case further
            if let Annotated(inner_term, attrs) = middle_term.repr() {
                // I need to remove the variables from the substitution that are bound inside
                let mut substitutions = substitutions.clone();
                for s in var_bindings.iter() {
                    substitutions.remove(&s.0.to_string());
                }

                let new_inner_term = substitute(inner_term, &substitutions, egraph);

                let mut new_attrs = vec![];
                for attr in attrs.iter() {
                    if let Attribute::Pattern(s_exprs) = &attr {
                        let new_s_exprs = s_exprs
                            .iter()
                            .map(|x| substitute(x, &substitutions, egraph))
                            .collect::<Vec<_>>();
                        new_attrs.push(Attribute::Pattern(new_s_exprs));
                    }
                    // else {
                    //     panic!("We have a forall case that is not annotated with a pattern: {} and attrs {:?}", term_rep, attrs);
                    // }
                }

                assert!(!new_attrs.is_empty());

                let new_middle_term = egraph.cnfenv.context.annotated(new_inner_term, new_attrs);
                let new_term = egraph
                    .cnfenv
                    .context
                    .forall(var_bindings.clone(), new_middle_term);
                new_term.clone()
            } else {
                panic!("We have a forall case that is not annotated");
            }
        }
        Exists(var_bindings, middle_term) => {
            // I need to remove the variables from the substitution that are bound inside
            if let Annotated(inner_term, attrs) = middle_term.repr() {
                let mut substitutions = substitutions.clone();
                for s in var_bindings.iter() {
                    substitutions.remove(&s.0.to_string());
                }

                let new_inner_term = substitute(inner_term, &substitutions, egraph);

                let mut new_attrs = vec![];
                for attr in attrs.iter() {
                    if let Attribute::Pattern(s_exprs) = &attr {
                        let new_s_exprs = s_exprs
                            .iter()
                            .map(|x| substitute(x, &substitutions, egraph))
                            .collect::<Vec<_>>();
                        new_attrs.push(Attribute::Pattern(new_s_exprs));
                    }
                    // else {
                    //     panic!("We have a forall case that is not annotated with a pattern: {} and attrs {:?}", term_rep, attrs);
                    // }
                }

                assert!(!new_attrs.is_empty());

                let new_middle_term = egraph.cnfenv.context.annotated(new_inner_term, new_attrs);
                let new_term = egraph
                    .cnfenv
                    .context
                    .exists(var_bindings.clone(), new_middle_term); // I think this gets skolemized but when??
                new_term.clone()
            } else {
                panic!(
                    "We have a forall exists where inner exists has no pattern {}",
                    term
                );
            }
        }
        Ite(cond, t1, t2) => {
            let (new_cond, new_t1, new_t2) = (
                substitute(cond, substitutions, egraph),
                substitute(t1, substitutions, egraph),
                substitute(t2, substitutions, egraph),
            );
            egraph.cnfenv.context.ite(new_cond, new_t1, new_t2)
        }
        Annotated(t, anns) => {
            let new_t = substitute(t, substitutions, egraph);
            egraph.cnfenv.context.annotated(new_t, anns.clone())
        }
        Distinct(args) => {
            let new_args = args
                .iter()
                .map(|t| substitute(t, substitutions, egraph))
                .collect();
            egraph.cnfenv.context.distinct(new_args)
        }
        // _ => term.clone() // todo: actually need to implement these extra cases
        Let(..) => todo!(),
        Matching(..) => todo!(),
    }
}

/// The simplify algorithm for matching patterns, iteratively
/// building a list of assignments for the free variables in the pattern
/// see https://mmoskal.github.io/smt/e-matching.pdf
///
/// Returing assignments as DeterministicHashMap<u64, u64> and DeterministicHashMap<string, u64>,
/// since then it is easier to substitute things when you have a nested forall case
///
/// TODO: I might need to think about writing this tail recursively eventually
pub fn match_term<'a>(
    assignment: &'a mut DeterministicHashMap<String, Term>,
    trigger_term_pairs: Vec<(u64, Option<u64>)>,
    egraph: &'a mut Egraph,
) -> Vec<(DeterministicHashMap<String, Term>, usize)> {
    if trigger_term_pairs.is_empty() {
        debug_println!(
            6,
            0,
            "We have reached the bottom case with assignment {:?}",
            assignment
        );
        return vec![(assignment.clone(), 0)];
    }
    let (trigger, term) = trigger_term_pairs[0];
    debug_println!(6, 0, "before13");
    let trigger_term = &egraph.get_term(trigger);
    if let Some(t) = term {
        debug_println!(
            6,
            0,
            "We are matching trigger {} with term {} and assignment {:?}",
            trigger_term,
            egraph.get_term(t),
            assignment
        );
    } else {
        debug_println!(
            6,
            0,
            "We are matching trigger {} with term None and assignment {:?}",
            trigger_term,
            assignment
        );
    }
    match trigger_term.repr() {
        Global(_, _) => {
            debug_println!(
                6,
                0,
                "We are matching global term {} with trigger {} to the term {}",
                trigger_term,
                egraph.get_term(trigger),
                egraph.get_term(term.unwrap())
            );
            if term.is_none() || egraph.find(trigger) == egraph.find(term.unwrap()) {
                match_term(assignment, trigger_term_pairs[1..].to_vec(), egraph)
            } else {
                vec![]
            }
        }
        Constant(..) => {
            debug_println!(
                6,
                0,
                "We are matching constant term {} with term {} and assignment {:?}",
                trigger_term,
                egraph.get_term(term.unwrap()),
                assignment
            );
            if term.is_none() || egraph.find(trigger) == egraph.find(term.unwrap()) {
                match_term(assignment, trigger_term_pairs[1..].to_vec(), egraph)
            } else {
                vec![]
            }
        }
        Local(local) => {
            debug_println!(
                6,
                0,
                "We are matching local term {} with term {} and assignment {:?}",
                trigger_term,
                egraph.get_term(term.unwrap()),
                assignment
            );
            match assignment.get(&local.symbol.to_string()) {
                Option::None => {
                    debug_println!(6, 0, "We are inserting the local term into the assignment");
                    debug_println!(6, 0, "before14");
                    assert!(
                        *local.sort.as_ref().unwrap()
                            == egraph
                                .get_term(term.unwrap())
                                .get_sort(egraph.cnfenv.context.arena())
                    ); // checking that things are typechecked
                    assignment.insert(local.symbol.to_string(), egraph.get_term(term.unwrap()));

                    // we cannot just return match_term(*, *, *) because we need to consider the activation depth of the current term
                    // TODO: maybe there is a better way to do this, where we only check the activation depth at the highest level
                    let new_assignments =
                        match_term(assignment, trigger_term_pairs[1..].to_vec(), egraph);
                    // let current_activation_depth =
                    //     egraph.terms_active[term.unwrap() as usize].unwrap_or_default();
                    // if current_activation_depth >= egraph.max_activation_depth {
                    //      debug_println!(
                    //         6,
                    //         0,
                    //         "We are skipping the term (as a substitution) {} because it is too deep",
                    //         egraph.get_term(term.unwrap())
                    //     );
                    //     return vec![];
                    // }

                    new_assignments
                        .iter()
                        .map(|(a, d)| (a.clone(), usize::max(*d, 0))) // note can get rid of this 0 it represents activation depth which we are not using
                        .collect::<Vec<_>>()
                }
                Some(v) if egraph.find(v.uid()) == egraph.find(term.unwrap()) => {
                    debug_println!(6, 0, "The local term matches the assignment");
                    match_term(assignment, trigger_term_pairs[1..].to_vec(), egraph)
                }
                Some(assignment_term) => {
                    debug_println!(
                        6,
                        0,
                        "The local term does not match the assignment term {}",
                        assignment_term
                    );
                    debug_println!(6, 0, "{}", egraph);
                    vec![]
                }
            }
        }
        App(func, args, _) => {
            debug_println!(6, 0, "We are matching app term {} with args:", trigger_term);
            debug_println!(6, 0, "before15");
            let func_name = func.id_str();
            let args_ref = args.iter().collect::<Vec<_>>();
            find_assignments_on_term(
                term,
                func_name,
                args_ref,
                trigger_term_pairs,
                assignment,
                egraph,
            )
        }
        Ite(b, t1, t2) => find_assignments_on_term(
            term,
            &"ite".to_string(),
            vec![b, t1, t2],
            trigger_term_pairs,
            assignment,
            egraph,
        ),
        _ => panic!(
            "Trigger term {} is not an App, ITE or variable",
            trigger_term
        ),
    }
}

// given a term and a func_name, returns a list of assignments
fn find_assignments_on_term(
    term: Option<u64>,
    func_name: &String,
    args: Vec<&Term>,
    trigger_term_pairs: Vec<(u64, Option<u64>)>,
    assignment: &mut DeterministicHashMap<String, Term>,
    egraph: &mut Egraph,
) -> Vec<(DeterministicHashMap<String, Term>, usize)> {
    let _ = args
        .iter()
        .map(|a| debug_println!(6, 0, "{}", egraph.get_term(a.uid())))
        .collect::<Vec<_>>();
    let mut list_assignments = Vec::new();

    // let func_name = &func.id_str().to_string();
    let function_terms = egraph.function_maps.get(func_name);
    // if there are no terms of this function, then we cannot do a specific instantiation
    if function_terms.is_none() {
        debug_println!(5, 0, "Function term not found: {}", func_name);
        return vec![];
    }

    let function_terms = function_terms.unwrap().clone();
    // checks that we don't consider the same set of subterms twice
    let mut considered_function_terms = DeterministicHashSet::default();

    // note that we need to get the root of the term here,
    // because the input to the function is not necessarily a root
    let term_root = term.map(|t| egraph.find(t));
    debug_println!(16, 0, "For the function {} we have the terms:", func_name);
    for (i, subterms) in function_terms {
        debug_println!(16, 4, "{}", egraph.get_term(i));
        // TODO: the number of terms could potentially grow
        // TODO: this could actually be made more efficient, by maybe considering an egraph with only active terms

        assert!(subterms.len() == args.len());

        let i_root = egraph.find(i);
        if term_root.is_none() || term_root.unwrap() == i_root {
            // comparing term to i_root, since term should already be a root based on definition of new_pairs
            // basically checking if we repeat the same subterms
            let subterms_canonical = subterms.iter().map(|s| egraph.find(*s)).collect::<Vec<_>>();

            if considered_function_terms.contains(&subterms_canonical) {
                debug_println!(
                    6,
                    0,
                    "We are skipping the term {} because it is already considered",
                    egraph.get_term(i)
                );
                continue;
            }
            considered_function_terms.insert(subterms_canonical);

            // originally Some(*find(s)), but thats buggy take ~f(t) and (t = B(true)) as an example (skips the instantiation we want because it is a root)
            // for some x in a pattern, we were substituting in root(t) when we match x |-> t, but this is bad.
            // Fixed by substituting t instead of root(t)
            let mut new_pairs = args
                .iter()
                .zip(subterms.iter())
                .map(|(a, s)| (a.uid(), Some(*s)))
                .collect::<Vec<_>>();
            new_pairs.extend(trigger_term_pairs[1..].to_vec());
            debug_println!(6, 0, "We have the new pairs {:?}", new_pairs);
            // note we need to clone the assignment here because each subcase should have its own assignment, TODO: is there a more efficient way to do this? I think not
            let new_assignments = match_term(&mut assignment.clone(), new_pairs, egraph);
            debug_println!(6, 0, "We have the new assignments {:?}", new_assignments);

            list_assignments.extend(
                new_assignments.iter().map(|(a, _)| (a.clone(), 0)), // todo the 0 here comes from activation depth, we can get rid of it
            );
        }
    }
    debug_println!(
        6,
        0,
        "We have the list of assignments {:?}",
        list_assignments
    );
    list_assignments
}
