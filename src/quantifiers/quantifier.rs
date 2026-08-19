// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Instantiation of quantifiers

use std::cell::RefCell;
use std::collections::VecDeque;
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
use yaspar_ir::ast::{LetElim, Local, Sort, Str, Substitute, Substitution, Term, TermAllocator};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct QiInstanceId {
    pub(crate) quantifier_id: u64,
    pub(crate) instance_term_id: u64,
}

#[derive(Debug, Clone)]
pub(crate) struct CachedInstantiation {
    pub(crate) clauses: Vec<Vec<i32>>,
    pub(crate) egraph_terms: Vec<u32>,
}

#[derive(Debug, Clone)]
pub(crate) enum QuantifierInstance {
    Instantiation {
        id: QiInstanceId,
        clauses: Vec<Vec<i32>>,
    },
    Skolemization {
        clauses: Vec<Vec<i32>>,
    },
}

struct DeferredInstantiation {
    id: QiInstanceId,
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

pub(crate) struct PendingInstantiations {
    deferred_instantiations: VecDeque<DeferredInstantiation>,
    deferred_skolemizations: VecDeque<DeferredSkolemization>,
    skolemized_quantifier_idxs: Vec<usize>,
}

impl PendingInstantiations {
    pub(crate) fn is_empty(&self) -> bool {
        self.deferred_instantiations.is_empty() && self.deferred_skolemizations.is_empty()
    }

    pub(crate) fn skolemized_quantifier_idxs(&self) -> &[usize] {
        &self.skolemized_quantifier_idxs
    }
}

/// Computes trigger matches and substitutions, returning deferred items
/// that can be materialized one at a time.
pub(crate) fn instantiate_quantifiers(
    solver_state: &mut SolverState,
    assignments: &[i32],
    allow_skolemization: bool,
    generation: Option<u64>,
) -> PendingInstantiations {
    let eager_skolem = solver_state.eager_skolem;
    debug_println!(24, 0, "Starting a matching round");
    let quantifiers = &solver_state.quantifiers.clone();
    let mut skolemized_quantifier_idxs = vec![];
    let mut deferred_skolemizations: VecDeque<DeferredSkolemization> = VecDeque::new();
    let mut deferred_instantiations: VecDeque<DeferredInstantiation> = VecDeque::new();

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
        let quantifier_assignment = assignments
            .get(quantifier_literal.unsigned_abs() as usize)
            .copied()
            .unwrap_or(0);

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
        if allow_skolemization && (quantifier_polarity || eager_skolem) && !quantifier.skolemized {
            skolemized_quantifier_idxs.push(i);

            let term = solver_state.get_term(quantifier.id);
            let (skolem, skolem_vars) =
                skolemize(&term, &mut solver_state.context, quantifier_is_exists);

            deferred_skolemizations.push_back(DeferredSkolemization {
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
        if triggers.is_empty() {
            debug_println!(
                "Warning: quantifier {} reached instantiation with no triggers",
                quantifier.id
            );
            continue;
        }
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
                // Convert the (Local -> egraph id) map into a (Local -> Term) map for substitution
                let subs: DeterministicHashMap<Local, Term> = subs_ids
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
                let substitution = Substitution::new(subs);
                let substituted_term = term.subst(&substitution, &mut solver_state.context);
                let id = QiInstanceId {
                    quantifier_id: quantifier.id,
                    instance_term_id: substituted_term.uid(),
                };
                if generation.is_some() && !solver_state.active_qi_instances.insert(id) {
                    continue;
                }
                deferred_instantiations.push_back(DeferredInstantiation {
                    id,
                    substituted_term,
                    is_exists: quantifier_is_exists,
                    literal: quantifier_literal,
                    quantifier_id: quantifier.id,
                });
            }
        }
    }

    PendingInstantiations {
        deferred_instantiations,
        deferred_skolemizations,
        skolemized_quantifier_idxs,
    }
}

/// Materializes the next pending instantiation or skolemization.
/// This does the expensive work: insert_predecessor, cnf_tseitin, proof steps.
/// Returns None if there's nothing left to materialize.
pub(crate) fn materialize_next(
    pending: &mut PendingInstantiations,
    solver_state: &mut SolverState,
    proof_tracer: &Rc<RefCell<SMTProofTracer>>,
    generation: Option<u64>,
) -> Option<Vec<QuantifierInstance>> {
    let ddsmt = solver_state.ddsmt;
    let lazy_dt = solver_state.lazy_dt;

    // Skolemizations first
    if let Some(deferred) = pending.deferred_skolemizations.pop_front() {
        let results = process_deferred_skolemizations(
            vec![deferred],
            solver_state,
            proof_tracer,
            ddsmt,
            lazy_dt,
        );
        return Some(results);
    }

    // Then instantiations
    if let Some(deferred) = pending.deferred_instantiations.pop_front() {
        let results = process_deferred_instantiations(
            vec![deferred],
            solver_state,
            proof_tracer,
            ddsmt,
            lazy_dt,
            generation,
        );
        return Some(results);
    }

    None
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
        let mut skolem_clauses = vec![skolem_imp];

        for clause in clauses {
            let mut c = clause.0;
            if push_literal_if_not_tautology(&mut c, -reduced_skolem_literal) {
                proof_tracer
                    .borrow_mut()
                    .add_theory_clause(&c, Theory::Boolean);
                skolem_clauses.push(c);
            }
        }

        for clause in additional_constraints {
            let mut c = clause;
            if push_literal_if_not_tautology(&mut c, -reduced_skolem_literal) {
                proof_tracer
                    .borrow_mut()
                    .add_theory_clause(&c, Theory::Boolean);
                skolem_clauses.push(c);
            }
        }

        results.push(QuantifierInstance::Skolemization {
            clauses: skolem_clauses,
        });
    }
    results
}

fn process_deferred_instantiations(
    deferred_instantiations: Vec<DeferredInstantiation>,
    solver_state: &mut SolverState,
    proof_tracer: &Rc<RefCell<SMTProofTracer>>,
    ddsmt: bool,
    lazy_dt: bool,
    generation: Option<u64>,
) -> Vec<QuantifierInstance> {
    let mut results = vec![];
    for DeferredInstantiation {
        id,
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

        if generation.is_some()
            && let Some(cached) = solver_state.qi_instance_cache.get(&id).cloned()
        {
            solver_state.reactivate_cached_qi_terms(&cached.egraph_terms, generation);
            results.push(QuantifierInstance::Instantiation {
                id,
                clauses: cached.clauses,
            });
            continue;
        }

        let proof_checkpoint = generation.map(|_| proof_tracer.borrow().proof_checkpoint());
        if generation.is_some() {
            solver_state.begin_qi_term_capture(generation);
        }
        solver_state.insert_predecessor(&nnf_term, None, None, true);

        let cnf_term = nnf_term.cnf_tseitin(solver_state);

        let mut raw_clauses: Vec<Vec<i32>> = cnf_term
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

        // Assert the body only when the quantifier holds (`quantifier => body`).
        // `cnf_tseitin` appends, as its final clause, a unit clause asserting the
        // top literal unconditionally; guarding just that clause (turning it into
        // the implication `-quantifier \/ top`) is enough for soundness. The
        // remaining clauses only define fresh Tseitin variables and are valid
        // regardless of the quantifier, so they stay ungated. Gating every clause
        // instead (as the skolemization path does) suppresses all propagation of
        // the body's structure until the top literal is decided, which badly
        // hurts search.
        let top = raw_clauses
            .pop()
            .expect("cnf_tseitin always emits the top-level clause");
        debug_assert_eq!(top, vec![nnf_term_literal]);
        raw_clauses.push(vec![-quantifier_dimacs_literal, nnf_term_literal]);

        proof_tracer
            .borrow_mut()
            .push_steps(&raw_clauses, ProofStepType::TheoryClause(Theory::Boolean));

        let additional_constraints =
            check_for_function_bool(&nnf_term, solver_state, true, ddsmt, lazy_dt);
        proof_tracer.borrow_mut().push_steps(
            &additional_constraints,
            ProofStepType::TheoryClause(Theory::Background),
        );

        let mut clauses = raw_clauses;
        clauses.extend(additional_constraints);

        if let Some(proof_checkpoint) = proof_checkpoint {
            let egraph_terms = solver_state.finish_qi_term_capture();
            let proof_steps = proof_tracer
                .borrow_mut()
                .take_proof_steps_since(proof_checkpoint);
            proof_tracer
                .borrow_mut()
                .register_qi_proof_bundle(id, proof_steps);
            solver_state.qi_instance_cache.insert(
                id,
                CachedInstantiation {
                    clauses: clauses.clone(),
                    egraph_terms,
                },
            );
        }

        results.push(QuantifierInstance::Instantiation { id, clauses });
    }
    results
}
