// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Instantiation of quantifiers

use std::cell::RefCell;
use std::rc::Rc;

use crate::cnf::{CNFConversion, push_literal_if_not_tautology};
use crate::egraphs::EgraphTrait;
use crate::preprocess::check_for_function_bool;
use crate::proof::{ProofStepType, SMTProofTracer, Theory};
use crate::quantifiers::skolem::skolemize;
use crate::solver_state::SolverState;
use crate::solver_types::Polarity;
use crate::utils::DeterministicHashMap;

use crate::debug_println;
use yaspar_ir::ast::{LetElim, Substitute, Substitution, Term, TermAllocator};

#[derive(Debug, Clone)]
pub enum QuantifierInstance {
    Instantiation { clause: Vec<i32> },
    Skolemization { clause: Vec<i32> },
}

struct DeferredInstantiation {
    substituted_term: Term,
    is_exists: bool,
    literal: i32,
    quantifier_id: u64,
}

/// Returns a list of quantifier instantiation given the assignment and current state of the egraph
///
/// TODO: level is only used for printing, can get rid of it later
/// (could use it for activate_bits, but right now we are activating everything at level 0)
pub fn instantiate_quantifiers(
    solver_state: &mut SolverState,
    proof_tracer: &Rc<RefCell<SMTProofTracer>>,
    assignments: &Vec<i32>,
    level: usize,
) -> Vec<QuantifierInstance> {
    let eager_skolem = solver_state.eager_skolem;
    let ddsmt = solver_state.ddsmt;
    let lazy_dt = solver_state.lazy_dt;
    debug_println!(24, 0, "Starting a matching round");
    let quantifiers = &solver_state.quantifiers.clone();
    let mut instantiations = vec![];
    let mut skolemized_quantifier_idxs = vec![];
    let mut deferred_instantiations: Vec<DeferredInstantiation> = vec![];

    // We `enumerate()` so we can update quantifiers[i].skolemized after the loop
    for (i, quantifier) in quantifiers.iter().enumerate() {
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
                solver_state.get_term(quantifier.id),
                quantifier_literal,
                quantifier_assignment,
                assignments
            );
            continue;
        }

        // if an odd number of these is true (i.e., XOR true) -> skolemize
        // if an even number of these is true (i.e., XOR false) -> instantiate
        let quantifier_is_exists = quantifier.polarity == Polarity::Existential;
        let quantifier_polarity =
            (quantifier_assignment > 0) ^ (quantifier_literal > 0) ^ quantifier_is_exists;

        // if the quantifier has positive polarity or we are doing ddsmt optimizations, and we haven't skolemized it yet, then we skolemize it
        if (quantifier_polarity || eager_skolem) && !quantifier.skolemized {
            debug_println!(
                6,
                0,
                "We are skolemizing the quantifier {} with quantifier_literal {} and quantifier_assignment {} | assignments {:?}",
                solver_state.get_term(quantifier.id),
                quantifier_literal,
                quantifier_assignment,
                assignments,
            );

            // Record this `Quantifier`'s index, so we can update its `.skolemized` field at the end
            skolemized_quantifier_idxs.push(i);

            // Skolemize the term
            let term = solver_state.get_term(quantifier.id);
            let (skolem, skolem_vars) =
                skolemize(&term, &mut solver_state.context, quantifier_is_exists);

            // Reduce the skolemized term, since Sundance doesn't simplify formulas under quantifiers during parsing
            let reduced_skolem: Term = skolem.let_elim(&mut solver_state.context);
            let reduced_skolem = reduced_skolem.nnf(solver_state);
            let additional_constraints =
                check_for_function_bool(&reduced_skolem, solver_state, true, ddsmt, lazy_dt);

            // Register the reduction with the egraph
            solver_state.insert_predecessor(&reduced_skolem, None, None, true);

            // Apply the Tseitin transformation to the reduced formula.
            // NOTE: We must do this step *before* we add a Skolemization eDRAT proof step,
            // since Sundance aggressively caches boolean sub-terms in its `CNFEnv` cache.
            // We want Sundance to register those DIMACS literals before we specially
            // request a new one for the un-reduced skolem term, just in case they match.
            // (If they match, then `cnf_tseitin()` won't process any sub-terms, since
            // the function otherwise has a cache hit.)
            let clauses = reduced_skolem.cnf_tseitin(solver_state);

            debug_println!(19, 0, "we are skolemizing {}", term);
            debug_println!(26, 0, "(assert {})", reduced_skolem);
            debug_println!(
                24,
                8,
                "from quantifier {} [{}]",
                solver_state.get_term(quantifier.id),
                quantifier.id,
            );

            // Now we add proof clause(s) to the eDRAT proof to justify the Skolemization.
            // Store the DIMACS literals we need beforehand.
            let quantifier_dimacs_literal = if quantifier_is_exists {
                quantifier_literal
            } else {
                -quantifier_literal
            };
            let reduced_skolem_literal = solver_state.get_lit_from_term(&reduced_skolem);
            let skolem_literal = if skolem.uid() != reduced_skolem.uid() {
                // Note: This must happen *after* calling `reduced_skolem.cnf_tseitin()`
                solver_state.get_or_allocate_lit_for_term(&skolem)
            } else {
                0
            };

            proof_tracer
                .borrow_mut()
                .push_skolem_or_instantiation_derivation(
                    quantifier_dimacs_literal,
                    skolem_literal,
                    &skolem,
                    reduced_skolem_literal,
                    &reduced_skolem,
                    ProofStepType::Skolemization {
                        parent_term: quantifier_literal,
                        skolem_vars,
                    },
                );

            // The SAT solver ultimately learns the Skolem as an implication
            let skolem_imp = vec![-quantifier_dimacs_literal, reduced_skolem_literal];
            instantiations.push(QuantifierInstance::Skolemization { clause: skolem_imp });

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
            solver_state.get_term(quantifier.id)
        );
        let triggers = &quantifier.triggers;
        // note we consider patterns in a multipattern conjunctively and multipatterns in a trigger disjunctively
        for multipattern in triggers {
            let body = quantifier.body;
            let trigger_term_pairs: Vec<(usize, Option<u32>)> =
                multipattern.iter().map(|t| (*t, None)).collect();

            debug_println!(12, 0, "after8");
            debug_println!(
                19,
                0,
                "About to match quantifier body {} with trigger {:?}",
                solver_state.get_term(body),
                trigger_term_pairs
            );
            debug_println!(12, 0, "after9");
            let list_assignments = solver_state.egraph.match_triggers(trigger_term_pairs);

            if list_assignments.is_empty() {
                debug_println!(
                    6,
                    0,
                    "We are skipping the quantifier {} because it has no substitutions",
                    solver_state.get_term(quantifier.id)
                );
                continue;
            }

            debug_println!(7, 0, "We have the following list of assignments:");
            for subs_ids in list_assignments.iter() {
                // Convert ID map to Term map for substitution
                let subs: DeterministicHashMap<String, Term> = subs_ids
                    .iter()
                    .map(|(k, v)| {
                        (
                            k.clone(),
                            solver_state.get_term(solver_state.to_solver_uid(*v)),
                        )
                    })
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
                deferred_instantiations.push(DeferredInstantiation {
                    substituted_term,
                    is_exists: quantifier_is_exists,
                    literal: quantifier_literal,
                    quantifier_id: quantifier.id,
                });
            }
        }
    }

    process_deferred_instantiations(
        deferred_instantiations,
        solver_state,
        proof_tracer,
        ddsmt,
        lazy_dt,
        level,
        &mut instantiations,
    );

    // Now mark the quantifier indices as skolemized
    for i in skolemized_quantifier_idxs {
        solver_state.quantifiers[i].skolemized = true;
    }

    instantiations
}

fn process_deferred_instantiations(
    deferred_instantiations: Vec<DeferredInstantiation>,
    solver_state: &mut SolverState,
    proof_tracer: &Rc<RefCell<SMTProofTracer>>,
    ddsmt: bool,
    lazy_dt: bool,
    level: usize,
    instantiations: &mut Vec<QuantifierInstance>,
) {
    debug_println!(6, 0, "Starting to process deferred instantiations");
    for DeferredInstantiation {
        substituted_term,
        is_exists,
        literal,
        quantifier_id,
    } in deferred_instantiations
    {
        let t = if is_exists {
            solver_state.context.not(substituted_term)
        } else {
            substituted_term
        };

        debug_println!(
            22,
            0,
            "We are adding the instantiation {} for quantifier {} at level {}",
            t.clone(),
            solver_state.get_term(quantifier_id),
            level
        );

        debug_println!(4, 0, "We have the term {} with id {}", t, t.uid());

        let let_elim_term = t.let_elim(&mut solver_state.context);

        debug_println!(
            8,
            0,
            "{} is an instantiation of {}",
            let_elim_term,
            solver_state.get_term(quantifier_id)
        );

        let nnf_term = let_elim_term.nnf(solver_state);

        debug_println!(26, 4, "(assert {})", nnf_term.clone());
        debug_println!(
            24,
            8,
            "from quantifier {} [{}]",
            solver_state.get_term(quantifier_id),
            quantifier_id
        );

        debug_println!(
            7,
            0,
            "We have the nnf term {} with id {}",
            nnf_term,
            nnf_term.uid()
        );

        solver_state.insert_predecessor(&nnf_term, None, None, true);

        let cnf_term = nnf_term.cnf_tseitin(solver_state);
        debug_println!(7, 0, "We have the cnf term {:?}", cnf_term);

        let mut clauses: Vec<_> = cnf_term
            .clone()
            .into_iter()
            .map(|x| x.into_iter().collect::<Vec<_>>())
            .collect();

        let quantifier_dimacs_literal = if is_exists { -literal } else { literal };
        let nnf_term_literal = solver_state.get_lit_from_term(&nnf_term);
        // Must happen *after* `cnf_tseitin` so Tseitin literals are registered first
        let subst_literal = if t.uid() != nnf_term.uid() {
            solver_state.get_or_allocate_lit_for_term(&t)
        } else {
            0
        };

        proof_tracer
            .borrow_mut()
            .push_skolem_or_instantiation_derivation(
                quantifier_dimacs_literal,
                subst_literal,
                &t,
                nnf_term_literal,
                &nnf_term,
                ProofStepType::Instantiation,
            );

        proof_tracer
            .borrow_mut()
            .push_steps(&clauses, ProofStepType::TheoryClause(Theory::Boolean));

        let additional_constraints =
            check_for_function_bool(&nnf_term, solver_state, true, ddsmt, lazy_dt);
        proof_tracer.borrow_mut().push_steps(
            &additional_constraints,
            ProofStepType::TheoryClause(Theory::Background),
        );
        clauses.extend(additional_constraints);

        for clause in clauses {
            let instantiation = QuantifierInstance::Instantiation { clause };
            instantiations.push(instantiation);
        }
    }
}

// match_term and find_assignments_on_term moved to Egraph methods in solver_state.rs
