// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Instantiation of quantifiers

use std::cell::RefCell;
use std::rc::Rc;

use crate::cnf::CNFConversion;
use crate::egraphs::datastructures::Polarity;
use crate::preprocess::check_for_function_bool;
use crate::proof::proof_tracer::SMTProofTracker;
use crate::quantifiers::skolem::skolemize;
// TODO: These functions should take &mut SolverState and use solver_state.egraph for egraph ops.
// For now they take &mut Egraph directly since the fields haven't been moved yet.
use crate::solver_state::SolverState;
use crate::utils::DeterministicHashMap;

use crate::debug_println;
use yaspar_ir::ast::{
    LetElim, Substitute, Substitution, Term, TermAllocator,
};

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
    solver_state: &mut SolverState,
    proof_tracker: &Rc<RefCell<SMTProofTracker>>,
    assignments: &Vec<i32>,
    level: usize,
) -> Vec<QuantifierInstance> {
    let eager_skolem = solver_state.eager_skolem;
    let ddsmt = solver_state.ddsmt;
    let lazy_dt = solver_state.lazy_dt;
    let quantifiers = &solver_state.quantifiers.clone();
    let mut instantiations = vec![];
    debug_println!(24, 0, "Starting a matching round");
    for quantifier in quantifiers {
        debug_println!(
            19,
            0,
            "We have the quantifier {}",
            solver_state.get_term(quantifier.id)
        );
        // check if the quantifier is assigned
        let quantifier_literal = solver_state.get_lit_from_u64(quantifier.id);
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
                solver_state.get_term(quantifier.id),
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
        // todo: replace solver_state.added_skolemizations. with the skolemized flag in the quantifier
        if (quantifier_polarity || eager_skolem)
            && !solver_state.added_skolemizations.contains(&quantifier.id)
        {
            debug_println!(
                6,
                0,
                "We are skolemizing the quantifier {} with quantifier_literal {} and quantifier_assignment {} | assignments {:?}",
                solver_state.get_term(quantifier.id),
                quantifier_literal,
                quantifier_assignment,
                assignments
            );

            let term = solver_state.get_term(quantifier.id);
            // let negated_term =
            //     if let Universal = quantifier.polarity {solver_state.context.not(term)} else {term};

            let polarity = quantifier.polarity != Polarity::Universal;

            // todo: replace this with the skolemized flag in the quantifier
            if solver_state.added_skolemizations.contains(&quantifier.id) {
                continue;
            }

            let (skolemized_quantifier, skolem_vars) =
                skolemize(&term, &mut solver_state.context, polarity);

            solver_state.added_skolemizations.insert(quantifier.id);

            let skolemized_quantifier: Term = skolemized_quantifier.let_elim(&mut solver_state.context);
            // let (skolemized_quantifier, _) = skolemize(&skolemized_quantifier, solver_state.context, &mut solver_state.skolem_counter);
            let skolemized_quantifier = skolemized_quantifier.nnf(solver_state);
            let additional_constraints =
                check_for_function_bool(&skolemized_quantifier, solver_state, true, ddsmt, lazy_dt);
            debug_println!(19, 0, "we are skolemizing {}", term);
            debug_println!(26, 0, "(assert {})", skolemized_quantifier);
            debug_println!(
                24,
                8,
                "from quantifier {} [{}]",
                solver_state.get_term(quantifier.id),
                quantifier.id
            );

            // note that from_quantifier is true here
            solver_state.insert_predecessor(&skolemized_quantifier, None, None, true);
            let clauses = skolemized_quantifier.cnf_tseitin(solver_state);

            // learning (not \forall P(x)) => P(c)
            // equivalent to \forall P(x) \/ P(c)
            // if it comes from existential, it becomes (not \exists P(x)) \/ P(c)
            let quantifier_literal = if quantifier.polarity == Polarity::Universal {
                quantifier_literal
            } else {
                -quantifier_literal
            };

            let skolemized_term_literal = solver_state.get_lit_from_term(&skolemized_quantifier);

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
            solver_state.get_term(quantifier.id)
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
                solver_state.get_term(body),
                trigger_term_pairs
            );
            debug_println!(12, 0, "after9");
            let list_assignments = solver_state.egraph.match_term(&mut assignments, trigger_term_pairs);

            if list_assignments.is_empty() {
                debug_println!(
                    24,
                    0,
                    "No substitutions for {}",
                    solver_state.get_term(quantifier.id)
                );
            }

            debug_println!(7, 0, "We have the following list of assignments:");
            let mut substitutions = vec![];
            for subs_ids in list_assignments.iter() {
                // Convert ID map to Term map for substitution
                let subs: DeterministicHashMap<String, Term> = subs_ids
                    .iter()
                    .map(|(k, v)| (k.clone(), solver_state.get_term(*v)))
                    .collect();

                if let Some(set) = solver_state.added_instantiations.get(&quantifier.id)
                    && set.contains(&subs)
                {
                    continue;
                }
                solver_state
                    .added_instantiations
                    .entry(quantifier.id)
                    .or_default()
                    .insert(subs.clone());

                debug_println!(6, 0, "before12");
                let term = solver_state.get_term(body);
                let substitution = Substitution::new(
                    subs.iter().map(|(s, t)| (s, t.clone())),
                    &mut solver_state.context,
                );
                let substituted_term = term.subst(&substitution, &mut solver_state.context);
                substitutions.push((substituted_term, subs));
            }

            if substitutions.is_empty() {
                debug_println!(
                    6,
                    0,
                    "We are skipping the quantifier {} because it has no substitutions",
                    solver_state.get_term(quantifier.id)
                );
                continue;
            }

            debug_println!(6, 0, "Starting to look at substitutions");
            for (t, _) in substitutions {
                // skipping instantiations that have already been added
                // TODO: need to come up with a more efficient way to do this
                // TODO: have solver_state.added_instantiations as a string right now, really want to go back to u32

                // if this came from a negated existential, we have to negate the term

                // println!("original_t: {}", t);
                let t = if quantifier.polarity == Polarity::Existential {
                    solver_state.context.not(t)
                } else {
                    t
                };

                debug_println!(
                    22,
                    0,
                    "We are adding the instantiation {} for quantifier {} at level {}",
                    t.clone(),
                    solver_state.get_term(quantifier.id),
                    level
                );

                debug_println!(4, 0, "We have the term {} with id {}", t, t.uid());

                // eliminating lets
                let let_elim_term = t.let_elim(&mut solver_state.context);

                debug_println!(
                    8,
                    0,
                    "{} is an instantiation of {}",
                    let_elim_term,
                    solver_state.get_term(quantifier.id)
                );

                let nnf_term = let_elim_term.nnf(solver_state);

                debug_println!(26, 4, "(assert {})", nnf_term.clone());
                debug_println!(
                    24,
                    8,
                    "from quantifier {} [{}]",
                    solver_state.get_term(quantifier.id),
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
                solver_state.insert_predecessor(&nnf_term, None, None, true);

                let cnf_term = nnf_term.cnf_tseitin(solver_state);
                debug_println!(7, 0, "We have the cnf term {:?}", cnf_term);

                let mut clauses: Vec<_> = cnf_term
                    .clone()
                    .into_iter()
                    .map(|x| x.into_iter().collect::<Vec<_>>())
                    .collect();

                let quantifier_literal = solver_state.get_lit_from_u64(quantifier.id);

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
                let additional_constraints = check_for_function_bool(&nnf_term, solver_state, true, ddsmt, lazy_dt);
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

// match_term and find_assignments_on_term moved to Egraph methods in solver_state.rs
