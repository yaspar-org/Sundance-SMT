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
use yaspar_ir::ast::{LetElim, Sort, Str, Substitute, Substitution, Term, TermAllocator};

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

struct DeferredSkolemization {
    skolem: Term,
    skolem_vars: Vec<(Str, Sort)>,
    is_exists: bool,
    literal: i32,
}

/// Returns a list of quantifier instantiation given the assignment and current state of the egraph
pub fn instantiate_quantifiers(
    solver_state: &mut SolverState,
    proof_tracer: &Rc<RefCell<SMTProofTracer>>,
    assignments: &[i32],
) -> Vec<QuantifierInstance> {
    let eager_skolem = solver_state.eager_skolem;
    let ddsmt = solver_state.ddsmt;
    let lazy_dt = solver_state.lazy_dt;
    debug_println!(24, 0, "Starting a matching round");
    let quantifiers = &solver_state.quantifiers.clone();
    let mut instantiations = vec![];
    let mut skolemized_quantifier_idxs = vec![];
    let mut deferred_skolemizations: Vec<DeferredSkolemization> = vec![];
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
        if quantifier_assignment == 0 {
            continue;
        }

        // if an odd number of these is true (i.e., XOR true) -> skolemize
        // if an even number of these is true (i.e., XOR false) -> instantiate
        let quantifier_is_exists = quantifier.polarity == Polarity::Existential;
        let quantifier_polarity =
            (quantifier_assignment > 0) ^ (quantifier_literal > 0) ^ quantifier_is_exists;

        // if the quantifier has positive polarity or we are doing ddsmt optimizations, and we haven't skolemized it yet, then we skolemize it
        if (quantifier_polarity || eager_skolem) && !quantifier.skolemized {
            skolemized_quantifier_idxs.push(i);

            let term = solver_state.get_term(quantifier.id);
            let (skolem, skolem_vars) =
                skolemize(&term, &mut solver_state.context, quantifier_is_exists);

            deferred_skolemizations.push(DeferredSkolemization {
                skolem,
                skolem_vars,
                is_exists: quantifier_is_exists,
                literal: quantifier_literal,
            });
        }

        // if this was a skolemization case, we don't want to instantiate
        if quantifier_polarity {
            continue;
        }

        let triggers = &quantifier.triggers;
        // note we consider patterns in a multipattern conjunctively and multipatterns in a trigger disjunctively
        for multipattern in triggers {
            let body = quantifier.body;
            let trigger_term_pairs: Vec<(usize, Option<u32>)> =
                multipattern.iter().map(|t| (*t, None)).collect();

            let list_assignments = solver_state.egraph.match_triggers(trigger_term_pairs);

            if list_assignments.is_empty() {
                continue;
            }

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

    instantiations.extend(process_deferred_skolemizations(
        deferred_skolemizations,
        solver_state,
        proof_tracer,
        ddsmt,
        lazy_dt,
    ));

    instantiations.extend(process_deferred_instantiations(
        deferred_instantiations,
        solver_state,
        proof_tracer,
        ddsmt,
        lazy_dt,
    ));

    // Now mark the quantifier indices as skolemized
    for i in skolemized_quantifier_idxs {
        solver_state.quantifiers[i].skolemized = true;
    }

    instantiations
}

fn process_deferred_skolemizations(
    deferred_skolemizations: Vec<DeferredSkolemization>,
    solver_state: &mut SolverState,
    proof_tracer: &Rc<RefCell<SMTProofTracer>>,
    ddsmt: bool,
    lazy_dt: bool,
) -> Vec<QuantifierInstance> {
    let mut results = vec![];
    for DeferredSkolemization {
        skolem,
        skolem_vars,
        is_exists,
        literal,
    } in deferred_skolemizations
    {
        let reduced_skolem: Term = skolem.let_elim(&mut solver_state.context);
        let reduced_skolem = reduced_skolem.nnf(solver_state);
        let additional_constraints =
            check_for_function_bool(&reduced_skolem, solver_state, true, ddsmt, lazy_dt);

        solver_state.insert_predecessor(&reduced_skolem, None, None, true);

        // Must do Tseitin *before* allocating the skolem literal — see comment on instantiation path
        let clauses = reduced_skolem.cnf_tseitin(solver_state);

        debug_println!(26, 0, "(assert {})", reduced_skolem);

        let quantifier_dimacs_literal = if is_exists { literal } else { -literal };
        let reduced_skolem_literal = solver_state.get_lit_from_term(&reduced_skolem);
        // Must happen *after* `cnf_tseitin` so Tseitin literals are registered first
        let skolem_literal = if skolem.uid() != reduced_skolem.uid() {
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
                    parent_term: literal,
                    skolem_vars,
                },
            );

        let skolem_imp = vec![-quantifier_dimacs_literal, reduced_skolem_literal];
        results.push(QuantifierInstance::Skolemization { clause: skolem_imp });

        let mut add_clause = |mut clause: Vec<i32>, theory: Theory| {
            if push_literal_if_not_tautology(&mut clause, -reduced_skolem_literal) {
                proof_tracer.borrow_mut().add_theory_clause(&clause, theory);
                results.push(QuantifierInstance::Skolemization { clause })
            }
        };

        for clause in clauses {
            add_clause(clause.0, Theory::Boolean);
        }

        for clause in additional_constraints {
            add_clause(clause, Theory::Boolean);
        }
    }
    results
}

fn process_deferred_instantiations(
    deferred_instantiations: Vec<DeferredInstantiation>,
    solver_state: &mut SolverState,
    proof_tracer: &Rc<RefCell<SMTProofTracer>>,
    ddsmt: bool,
    lazy_dt: bool,
) -> Vec<QuantifierInstance> {
    let mut results = vec![];
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
            "We are adding the instantiation {} for quantifier {}",
            t.clone(),
            solver_state.get_term(quantifier_id),
        );

        let let_elim_term = t.let_elim(&mut solver_state.context);

        let nnf_term = let_elim_term.nnf(solver_state);

        debug_println!(26, 4, "(assert {})", nnf_term.clone());

        solver_state.insert_predecessor(&nnf_term, None, None, true);

        let cnf_term = nnf_term.cnf_tseitin(solver_state);

        let mut clauses: Vec<Vec<i32>> = cnf_term
            .into_iter()
            .map(|x| x.into_iter().collect::<Vec<i32>>())
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
            results.push(QuantifierInstance::Instantiation { clause });
        }
    }
    results
}
