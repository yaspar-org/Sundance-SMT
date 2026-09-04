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
use crate::qi_gc::QiInstantiationKey;
use crate::quantifiers::skolem::skolemize;
use crate::relevancy::{RelevancyTrait, relevancy_trace_enabled};
use crate::solver_state::SolverState;
use crate::solver_types::Polarity;
use crate::utils::{DeterministicHashMap, DeterministicHashSet};

use crate::debug_println;
use yaspar_ir::ast::{LetElim, Local, Sort, Str, Substitute, Substitution, Term, TermAllocator};

#[derive(Debug, Clone)]
pub(crate) enum QuantifierInstance {
    /// `pre_nnf_body` is the instance body after let-elim but before NNF/
    /// Tseitin — used by relevancy filtering so structural rules see the
    /// original connectives (Iff, ITE, Implies) that NNF destroys.
    Instantiation {
        clauses: Vec<Vec<i32>>,
        pre_nnf_body: Term,
        key: QiInstantiationKey,
        /// Solver terms first registered while materializing this instance.
        /// These are candidates for reclamation if the complete instance is
        /// discarded at a QI-GC epoch transition.
        created_terms: DeterministicHashSet<u64>,
        /// Registered-term closure of this instance's SAT clauses. If the
        /// clauses survive a transition, these are the solver terms that must
        /// remain live even when another instance originally created them.
        clause_terms: DeterministicHashSet<u64>,
    },
    Skolemization {
        clauses: Vec<Vec<i32>>,
        pre_nnf_body: Term,
    },
}

struct DeferredInstantiation {
    substituted_term: Term,
    substitution: DeterministicHashMap<Local, Term>,
    is_exists: bool,
    literal: i32,
    quantifier_id: u64,
    generation: u32,
}

struct DeferredSkolemization {
    skolem: Term,
    skolem_vars: Vec<(Str, Sort)>,
    is_exists: bool,
    literal: i32,
    generation: u32,
}

pub(crate) struct PendingInstantiations {
    deferred_instantiations: VecDeque<DeferredInstantiation>,
    deferred_skolemizations: VecDeque<DeferredSkolemization>,
    skolemized_quantifier_idxs: Vec<usize>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum TriggerMatchScope {
    RelevantClasses,
    AllClasses,
}

impl PendingInstantiations {
    pub(crate) fn is_empty(&self) -> bool {
        self.deferred_instantiations.is_empty() && self.deferred_skolemizations.is_empty()
    }

    pub(crate) fn len(&self) -> usize {
        self.deferred_instantiations.len() + self.deferred_skolemizations.len()
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
    require_quantifier_relevance: bool,
    trigger_match_scope: TriggerMatchScope,
    generation_limit: Option<u32>,
    instantiation_limit: Option<usize>,
) -> PendingInstantiations {
    let eager_skolem = solver_state.eager_skolem;
    debug_println!(24, 0, "Starting a matching round");
    let quantifiers = &solver_state.quantifiers.clone();
    let mut skolemized_quantifier_idxs = vec![];
    let mut deferred_skolemizations: VecDeque<DeferredSkolemization> = VecDeque::new();
    let mut deferred_instantiations: VecDeque<DeferredInstantiation> = VecDeque::new();

    // We `enumerate()` so we can update quantifiers[i].skolemized after the loop
    'quantifiers: for (i, quantifier) in quantifiers.iter().enumerate() {
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
        if require_quantifier_relevance && !solver_state.is_lit_relevant(quantifier_literal) {
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
                generation: solver_state.generation_of(quantifier.id).saturating_add(1),
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

            // Eager matching considers only ground terms whose class was marked
            // relevant. Complete-model checks widen the search to every class
            // so filtered progress cannot indefinitely postpone a refutation.
            let relevant_only = solver_state.relevancy.is_enabled()
                && trigger_match_scope == TriggerMatchScope::RelevantClasses;
            let list_assignments = solver_state
                .egraph
                .match_triggers(&trigger_term_pairs, relevant_only);

            if relevancy_trace_enabled() {
                eprintln!(
                    "[relevancy] quantifier {} produced {} trigger matches",
                    quantifier.id,
                    list_assignments.len()
                );
            }
            if list_assignments.is_empty() {
                continue;
            }

            for subs_ids in list_assignments.iter() {
                if instantiation_limit.is_some_and(|limit| deferred_instantiations.len() >= limit) {
                    break 'quantifiers;
                }
                let candidate_generation = subs_ids
                    .iter()
                    .map(|(_, id)| solver_state.generation_of(solver_state.to_solver_uid(*id)))
                    .max()
                    .unwrap_or(0)
                    .saturating_add(1);
                if generation_limit.is_some_and(|limit| candidate_generation > limit) {
                    continue;
                }

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
                    if relevancy_trace_enabled() {
                        eprintln!(
                            "[relevancy] quantifier {} skipping duplicate substitution {:?}",
                            quantifier.id, subs
                        );
                    }
                    continue;
                }
                if relevancy_trace_enabled() {
                    eprintln!(
                        "[relevancy] quantifier {} accepting substitution {:?}",
                        quantifier.id, subs
                    );
                }
                let rediscovered_after_gc =
                    solver_state.remember_added_instantiation(quantifier.id, &subs);
                if rediscovered_after_gc && relevancy_trace_enabled() {
                    eprintln!(
                        "[relevancy] quantifier {} rediscovered collected substitution {:?}",
                        quantifier.id, subs
                    );
                }

                let term = solver_state.get_term(body);
                let substitution_key = subs.clone();
                let substitution = Substitution::new(subs);
                let substituted_term = term.subst(&substitution, &mut solver_state.context);
                deferred_instantiations.push_back(DeferredInstantiation {
                    substituted_term,
                    substitution: substitution_key,
                    is_exists: quantifier_is_exists,
                    literal: quantifier_literal,
                    quantifier_id: quantifier.id,
                    generation: candidate_generation,
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
        );
        return Some(results);
    }

    None
}

/// Rebuild an exact previously collected instantiation from its quantifier
/// identity and substitution. The old CNF/e-graph closure may already have
/// been reclaimed; the retained AST terms are registered again as needed.
pub(crate) fn rematerialize_instantiation(
    key: &QiInstantiationKey,
    solver_state: &mut SolverState,
    proof_tracer: &Rc<RefCell<SMTProofTracer>>,
) -> Vec<QuantifierInstance> {
    let quantifier = solver_state
        .quantifiers
        .iter()
        .find(|quantifier| quantifier.id == key.quantifier_id)
        .cloned()
        .expect("collected quantifier instance lost its source quantifier");
    let literal = solver_state.get_lit_from_u64(quantifier.id);
    assert_ne!(
        literal, 0,
        "collected quantifier instance lost its source literal"
    );

    let body = solver_state.get_term(quantifier.body);
    let substitution = Substitution::new(key.substitution.clone());
    let substituted_term = body.subst(&substitution, &mut solver_state.context);
    let generation = key
        .substitution
        .values()
        .map(|term| solver_state.generation_of(term.uid()))
        .max()
        .unwrap_or(0)
        .saturating_add(1);
    let ddsmt = solver_state.ddsmt;
    let lazy_dt = solver_state.lazy_dt;

    process_deferred_instantiations(
        vec![DeferredInstantiation {
            substituted_term,
            substitution: key.substitution.clone(),
            is_exists: quantifier.polarity == Polarity::Existential,
            literal,
            quantifier_id: quantifier.id,
            generation,
        }],
        solver_state,
        proof_tracer,
        ddsmt,
        lazy_dt,
    )
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
        generation,
    } in deferred_skolemizations
    {
        let previous_generation = solver_state.current_instantiation_generation;
        solver_state.current_instantiation_generation = previous_generation.max(generation);
        let reduced_skolem: Term = skolem.let_elim(&mut solver_state.context);
        let pre_nnf_body = reduced_skolem.clone();
        let reduced_skolem = reduced_skolem.nnf(solver_state);
        solver_state.set_generation(skolem.uid(), generation);
        solver_state.set_generation(reduced_skolem.uid(), generation);
        let additional_constraints =
            check_for_function_bool(&reduced_skolem, solver_state, true, ddsmt, lazy_dt);

        solver_state.insert_predecessor(&reduced_skolem, None, None, true);
        solver_state.current_instantiation_generation = previous_generation;

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
            pre_nnf_body,
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
) -> Vec<QuantifierInstance> {
    let mut results = vec![];
    for DeferredInstantiation {
        substituted_term,
        substitution,
        is_exists,
        literal,
        quantifier_id,
        generation,
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

        // Wrap the body in `quantifier => body` and NNF+Tseitin the whole
        // thing. This gives the wrapper implication its own SAT literal
        // (needed by relevancy — a bare-body registration has no lit for
        // the implication as a whole). NNF distributes over Implies as
        // `Or(¬quantifier, nnf(body))`, so the body's Tseitin clauses are
        // still emitted separately and remain ungated (preserving the
        // propagation behavior the previous manual encoding was chosen
        // for). Tseitinizing adds one fresh var and two extra backward
        // clauses per instance — cheap.
        let quantifier_term = solver_state.get_term(quantifier_id);
        let quantifier_side = if is_exists {
            solver_state.context.not(quantifier_term)
        } else {
            quantifier_term
        };
        let pre_nnf_body = solver_state.implies(vec![quantifier_side], let_elim_term.clone());

        let nnf_term = pre_nnf_body.nnf(solver_state);

        debug_println!(26, 4, "(assert {})", nnf_term.clone());

        solver_state.begin_qi_term_capture();
        let previous_generation = solver_state.current_instantiation_generation;
        solver_state.current_instantiation_generation = previous_generation.max(generation);
        solver_state.set_generation(t.uid(), generation);
        solver_state.set_generation(pre_nnf_body.uid(), generation);
        solver_state.set_generation(nnf_term.uid(), generation);
        solver_state.insert_predecessor(&nnf_term, None, None, true);

        let cnf_term = nnf_term.cnf_tseitin(solver_state);

        let raw_clauses: Vec<Vec<i32>> = cnf_term
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
            .push_steps(&raw_clauses, ProofStepType::TheoryClause(Theory::Boolean));

        let additional_constraints =
            check_for_function_bool(&nnf_term, solver_state, true, ddsmt, lazy_dt);
        solver_state.current_instantiation_generation = previous_generation;
        proof_tracer.borrow_mut().push_steps(
            &additional_constraints,
            ProofStepType::TheoryClause(Theory::Background),
        );

        let mut clauses = raw_clauses;
        clauses.extend(additional_constraints);
        let created_terms = solver_state.finish_qi_term_capture();
        let mut clause_terms = DeterministicHashSet::default();
        solver_state.collect_clause_term_closure(&clauses, &mut clause_terms);
        for term in substitution.values() {
            solver_state.collect_registered_term_closure(term, &mut clause_terms);
        }

        results.push(QuantifierInstance::Instantiation {
            clauses,
            pre_nnf_body,
            key: QiInstantiationKey {
                quantifier_id,
                substitution,
            },
            created_terms,
            clause_terms,
        });
    }
    results
}
