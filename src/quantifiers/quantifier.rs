// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Instantiation of quantifiers

use std::cell::RefCell;
use std::rc::Rc;

use crate::cnf::{CNFConversion,push_literal_if_not_tautology};
use crate::egraphs::datastructures::Polarity;
use crate::egraphs::egraph::Egraph;
use crate::preprocess::check_for_function_bool;
use crate::proof::{ProofStepType,SMTProofTracer,Theory};
use crate::quantifiers::skolem::skolemize;
use crate::utils::{DeterministicHashMap, DeterministicHashSet};

use crate::debug_println;
use crate::log::is_important;
use yaspar_ir::ast::{
    ATerm, FetchSort, HasArena, LetElim, Repr, Substitute, Substitution, Term, TermAllocator,
};

#[derive(Debug, Clone)]
pub enum QuantifierInstance {
    Instantiation { clause: Vec<i32> },
    Skolemization { clause: Vec<i32> },
}

/// Returns a list of quantifier instantiation given the assignment and current state of the egraph
///  
/// TODO: level is only used for printing, can get rid of it later
/// (could use it for activate_bits, but right now we are activating everything at level 0)
pub fn instantiate_quantifiers(
    egraph: &mut Egraph,
    proof_tracer: &Rc<RefCell<SMTProofTracer>>,
    assignments: &Vec<i32>,
    level: usize,
) -> Vec<QuantifierInstance> {
    debug_println!(24, 0, "Starting a matching round");
    let quantifiers = &egraph.quantifiers.clone();
    let mut instantiations = vec![];
    let mut skolemized_quantifier_idxs = vec![];

    // We `enumerate()` so we can update quantifiers[i].skolemized after the loop
    for (i, quantifier) in quantifiers.iter().enumerate() {
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

        // if the quantifier is unassigned, we can skip it
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

        // if an odd number of these is true (i.e., XOR true) -> skolemize
        // if an even number of these is true (i.e., XOR false) -> instantiate
        let quantifier_is_exists = quantifier.polarity == Polarity::Existential;
        let quantifier_polarity = (quantifier_assignment > 0) ^ (quantifier_literal > 0) ^ quantifier_is_exists;

        // if the quantifier has positive polarity or we are doing ddsmt optimizations, and we haven't skolemized it yet, then we skolemize it
        if (quantifier_polarity || egraph.eager_skolem) && !quantifier.skolemized {
            debug_println!(
                6,
                0,
                "We are skolemizing the quantifier {} with quantifier_literal {} and quantifier_assignment {} | assignments {:?}",
                egraph.get_term(quantifier.id),
                quantifier_literal,
                quantifier_assignment,
                assignments,
            );

            // Record this `Quantifier`'s index, so we can update its `.skolemized` field at the end
            skolemized_quantifier_idxs.push(i);

            // Skolemize the term
            let term = egraph.get_term(quantifier.id);
            let (skolem, skolem_vars) =
                skolemize(&term, &mut egraph.context, quantifier_is_exists);

            // Reduce the skolemized term, since Sundance doesn't simplify formulas under quantifiers during parsing
            let reduced_skolem: Term = skolem.let_elim(&mut egraph.context);
            let reduced_skolem = reduced_skolem.nnf(egraph);
            let additional_constraints =
                check_for_function_bool(&reduced_skolem, egraph, true);

            // Register the reduction with the egraph            
            egraph.insert_predecessor(&reduced_skolem, None, None, true, None);

            // Apply the Tseitin transformation to the reduced formula.
            // NOTE: We must do this step *before* we add a Skolemization eDRAT proof step,
            // since Sundance aggressively caches boolean sub-terms in its `CNFEnv` cache.
            // We want Sundance to register those DIMACS literals before we specially
            // request a new one for the un-reduced skolem term, just in case they match.
            // (If they match, then `cnf_tseitin()` won't process any sub-terms, since
            // the function otherwise has a cache hit.)
            let clauses = reduced_skolem.cnf_tseitin(egraph);

            debug_println!(19, 0, "we are skolemizing {}", term);
            debug_println!(26, 0, "(assert {})", reduced_skolem);
            debug_println!(
                24,
                8,
                "from quantifier {} [{}]",
                egraph.get_term(quantifier.id),
                quantifier.id,
            );

            // Now we add proof clause(s) to the eDRAT proof to justify the Skolemization.
            // Store the DIMACS literals we need beforehand.
            let quantifier_dimacs_literal = if quantifier_is_exists { quantifier_literal } else { -quantifier_literal };
            let reduced_skolem_literal = egraph.get_lit_from_term(&reduced_skolem);
            let skolem_literal = if skolem.uid() != reduced_skolem.uid() {
                // Note: This must happen *after* calling `reduced_skolem.cnf_tseitin()`
                egraph.get_or_allocate_lit_for_term(&skolem)
            } else {
                0
            };

            proof_tracer.borrow_mut().push_skolem_or_instantiation_derivation(
                quantifier_dimacs_literal,
                skolem_literal, &skolem,
                reduced_skolem_literal, &reduced_skolem,
                ProofStepType::Skolemization { 
                    parent_term: quantifier_literal,
                    skolem_vars,
                },
            );

            // The SAT solver ultimately learns the Skolem as an implication
            let skolem_imp = vec![-quantifier_dimacs_literal, reduced_skolem_literal];
            instantiations.push(QuantifierInstance::Skolemization {
                clause: skolem_imp,
            });

            // Finally, clauses from the Tseitin transformation and from `additional_constraints`
            // are implied by the reduced skolem formula.
            
            // Lambda to add the skolem literal to the Tseitin/additional_constraints clauses
            let mut add_clause = |mut clause: Vec<i32>, theory: Theory| {
                if push_literal_if_not_tautology(&mut clause, -reduced_skolem_literal) {
                    proof_tracer.borrow_mut().add_theory_clause(&clause, theory);
                    instantiations.push(QuantifierInstance::Skolemization { clause })
                }
            };

            for clause in clauses {
                add_clause(clause.0, Theory::Boolean);
            }

            // CC TODO: Differentiate between `ite` axioms and `datatype` axioms
            for clause in additional_constraints {
                add_clause(clause, Theory::Boolean);
            }
        }

        // if this was a skolemization case, we don't want to instantiate
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

                if is_important(22) {
                    debug_println!(22, 0, "The body is {}", body);
                    debug_println!(22, 0, "The assignment is");
                    for sub in subs {
                        debug_println!(22, 4, "{} |-> {}", sub.0, sub.1)
                    }
                }
                debug_println!(6, 0, "before12");
                let term = egraph.get_term(body);
                let substitution = Substitution::new(
                    subs.iter().map(|(s, t)| (s, t.clone())),
                    &mut egraph.context,
                );
                let substituted_term = term.subst(&substitution, &mut egraph.context);
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
                let t = if quantifier_is_exists {
                    egraph.context.not(t)
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
                let let_elim_term = t.let_elim(&mut egraph.context);

                debug_println!(
                    8,
                    0,
                    "{} is an instantiation of {} at depth {}",
                    let_elim_term,
                    egraph.get_term(quantifier.id),
                    activation_depth
                );

                let nnf_term = let_elim_term.nnf(egraph);

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
                // but it should be fine. This is necessary because we need to look up lits
                // todo: also might be less efficient as well because we are losing structure from original formula in the egraph
                egraph.insert_predecessor(&nnf_term, None, None, true, None);

                let cnf_term = nnf_term.cnf_tseitin(egraph);
                debug_println!(7, 0, "We have the cnf term {:?}", cnf_term);

                let mut clauses: Vec<_> = cnf_term
                    .clone()
                    .into_iter()
                    .map(|x| x.into_iter().collect::<Vec<_>>())
                    .collect();

                let quantifier_dimacs_literal = if quantifier_is_exists { -quantifier_literal } else { quantifier_literal };
                let nnf_term_literal = egraph.get_lit_from_term(&nnf_term);
                let subst_literal = if t.uid() != nnf_term.uid() {
                    // Reserve a fresh DIMACS literal for the un-reduced term.
                    // Note: This must happen *after* calling `nnf_term.cnf_tseitin()`
                    egraph.get_or_allocate_lit_for_term(&t)
                } else {
                    0
                }; 

                // Add the "quantifier implies instantiation" clause to the proof
                proof_tracer.borrow_mut().push_skolem_or_instantiation_derivation(
                    quantifier_dimacs_literal,
                    subst_literal, &t,
                    nnf_term_literal, &nnf_term,
                    ProofStepType::Instantiation,
                );

                // Add proof steps witnessing the Tseitin transformation of `nnf_term`
                proof_tracer.borrow_mut().push_steps(&clauses, ProofStepType::TheoryClause(Theory::Boolean));

                // the bug comes from the additional constraints
                // basically the additional constraints are valid lits -> converted to valid u64, but may not be in the actual term mapping
                // it should be added in insert_predecessor which calls get_or_insert which adds into terms_list
                let additional_constraints = check_for_function_bool(&nnf_term, egraph, true);
                proof_tracer.borrow_mut().push_steps(&additional_constraints, ProofStepType::TheoryClause(Theory::Background));
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

    // Now mark the quantifier indices as skolemized
    for i in skolemized_quantifier_idxs {
        egraph.quantifiers[i].skolemized = true;
    }

    instantiations
}

/// The simplify algorithm for matching patterns, iteratively
/// building a list of assignments for the free variables in the pattern
/// see <https://mmoskal.github.io/smt/e-matching.pdf>
///
/// todo: @Amar the following comment is out of date
/// Returning assignments as DeterministicHashMap<u64, u64> and DeterministicHashMap<string, u64>,
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
    if is_important(6) {
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
    }
    match trigger_term.repr() {
        ATerm::Global(_, _) => {
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
        ATerm::Constant(..) => {
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
        ATerm::Local(local) => {
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
                                .get_sort(egraph.context.arena())
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
        ATerm::App(func, args, _) => {
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
        ATerm::Ite(b, t1, t2) => find_assignments_on_term(
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
