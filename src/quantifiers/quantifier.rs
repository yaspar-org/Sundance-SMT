// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Instantiation of quantifiers

use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::{BinaryHeap, VecDeque};
use std::rc::Rc;

use crate::cnf::{CNFConversion, push_literal_if_not_tautology};
use crate::config::CostWeights;
use crate::egraphs::EgraphTrait;
use crate::preprocess::check_for_function_bool;
use crate::proof::{ProofStepType, SMTProofTracer, Theory};
use crate::quantifiers::skolem::skolemize;
use crate::solver_state::SolverState;
use crate::solver_types::Polarity;
use crate::utils::DeterministicHashMap;

use crate::debug_println;
use yaspar_ir::ast::{LetElim, Local, Sort, Str, Substitute, Substitution, Term, TermAllocator};

#[derive(Debug, Clone)]
pub(crate) enum QuantifierInstance {
    Instantiation { clauses: Vec<Vec<i32>> },
    Skolemization { clauses: Vec<Vec<i32>> },
}

struct DeferredInstantiation {
    substituted_term: Term,
    is_exists: bool,
    literal: i32,
    quantifier_id: u64,
    /// Instantiation depth of this candidate (see `SolverState::generation`).
    generation: u32,
}

struct DeferredSkolemization {
    skolem: Term,
    skolem_vars: Vec<(Str, Sort)>,
    is_exists: bool,
    literal: i32,
}

/// Inputs to the instantiation cost function. Mirrors the variables Z3 exposes
/// in `smt.qi.cost` (generation, weight, size, depth, vars, pattern_width,
/// instances, total_instances, scope, cs_factor).
#[derive(Debug, Clone, Copy)]
pub(crate) struct CostInputs {
    pub generation: u32,
    pub weight: u32,
    pub size: u32,
    pub depth: u32,
    pub vars: u32,
    pub pattern_width: u32,
    pub instances: u32,
    pub total_instances: u32,
    pub scope: u32,
    pub cs_factor: u32,
}

/// Estimated cost of an instantiation. Cheaper candidates are materialized
/// first. Weighted linear combination of the cost inputs; `size` is compressed
/// with log2 so a large body does not dominate purely by size.
pub(crate) fn instantiation_cost(inputs: &CostInputs, w: &CostWeights) -> f64 {
    let size_term = ((1 + inputs.size) as f64).log2();
    w.generation * inputs.generation as f64
        + w.weight * inputs.weight as f64
        + w.size * size_term
        + w.depth * inputs.depth as f64
        + w.vars * inputs.vars as f64
        + w.pattern_width * inputs.pattern_width as f64
        + w.instances * (inputs.instances + inputs.total_instances) as f64
        + w.scope * inputs.scope as f64
        + w.cs_factor * inputs.cs_factor as f64
}

/// A deferred instantiation paired with its cost and a FIFO tie-break sequence.
/// Ordered so a `BinaryHeap` (a max-heap) yields the *cheapest* candidate first,
/// breaking ties by insertion order (stable, and keeps `Ord` total over f64).
struct PrioritizedInstantiation {
    cost: f64,
    seq: u64,
    inst: DeferredInstantiation,
}

impl PartialEq for PrioritizedInstantiation {
    fn eq(&self, other: &Self) -> bool {
        self.cost == other.cost && self.seq == other.seq
    }
}
impl Eq for PrioritizedInstantiation {}

impl Ord for PrioritizedInstantiation {
    fn cmp(&self, other: &Self) -> Ordering {
        // Reverse cost so the max-heap pops the smallest cost first; on equal
        // cost, smaller seq (inserted earlier) should pop first, so reverse seq.
        other
            .cost
            .partial_cmp(&self.cost)
            .unwrap_or(Ordering::Equal)
            .then_with(|| other.seq.cmp(&self.seq))
    }
}
impl PartialOrd for PrioritizedInstantiation {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

pub(crate) struct PendingInstantiations {
    deferred_instantiations: BinaryHeap<PrioritizedInstantiation>,
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
/// that can be materialized one at a time. Instantiation candidates are ranked
/// by an estimated cost (cheapest first) using `weights`; `scope` is the current
/// decision level, one of the cost inputs.
pub(crate) fn instantiate_quantifiers(
    solver_state: &mut SolverState,
    assignments: &[i32],
    weights: &CostWeights,
    scope: usize,
) -> PendingInstantiations {
    let eager_skolem = solver_state.eager_skolem;
    debug_println!(24, 0, "Starting a matching round");
    let quantifiers = &solver_state.quantifiers.clone();
    let mut skolemized_quantifier_idxs = vec![];
    let mut deferred_skolemizations: VecDeque<DeferredSkolemization> = VecDeque::new();
    let mut deferred_instantiations: BinaryHeap<PrioritizedInstantiation> = BinaryHeap::new();
    // Monotonic sequence for FIFO tie-breaking among equal-cost candidates.
    let mut seq: u64 = 0;

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

            // INSTRUMENTATION: count total vs new (non-dup) matches per quantifier
            if std::env::var("SUNDANCE_MATCH_STATS").is_ok() {
                let total = list_assignments.len();
                let mut newc = 0;
                for subs_ids in list_assignments.iter() {
                    let subs: DeterministicHashMap<Local, Term> = subs_ids
                        .iter()
                        .map(|(k, v)| (k.clone(), solver_state.get_term(solver_state.to_solver_uid(*v))))
                        .collect();
                    let dup = solver_state
                        .added_instantiations
                        .get(&quantifier.id)
                        .map(|s| s.contains(&subs))
                        .unwrap_or(false);
                    if !dup { newc += 1; }
                }
                eprintln!("MATCH qid={} total={} new={}", quantifier.id, total, newc);
            }

            let pattern_width = multipattern.len() as u32;

            for subs_ids in list_assignments.iter() {
                // Generation of this candidate: one deeper than the deepest term
                // bound by the trigger match (ground/original terms are gen 0).
                let match_generation = subs_ids
                    .iter()
                    .map(|(_, v)| solver_state.generation_of(solver_state.to_solver_uid(*v)))
                    .max()
                    .unwrap_or(0);
                let candidate_generation = match_generation.saturating_add(1);

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

                // Stamp the produced term's generation so any future matches
                // rooted at it inherit the increased depth.
                solver_state.set_generation(substituted_term.uid(), candidate_generation);

                let cost = instantiation_cost(
                    &CostInputs {
                        generation: candidate_generation,
                        weight: quantifier.weight,
                        size: quantifier.body_size,
                        depth: quantifier.body_depth,
                        vars: quantifier.variables.len() as u32,
                        pattern_width,
                        instances: solver_state.branch_instances_of(quantifier.id),
                        total_instances: solver_state
                            .added_instantiations
                            .get(&quantifier.id)
                            .map(|s| s.len() as u32)
                            .unwrap_or(0),
                        scope: scope as u32,
                        cs_factor: quantifier.cs_factor,
                    },
                    weights,
                );

                deferred_instantiations.push(PrioritizedInstantiation {
                    cost,
                    seq,
                    inst: DeferredInstantiation {
                        substituted_term,
                        is_exists: quantifier_is_exists,
                        literal: quantifier_literal,
                        quantifier_id: quantifier.id,
                        generation: candidate_generation,
                    },
                });
                seq += 1;
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
    level: usize,
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

    // Then instantiations, cheapest cost first.
    if let Some(prioritized) = pending.deferred_instantiations.pop() {
        let results = process_deferred_instantiations(
            vec![prioritized.inst],
            solver_state,
            proof_tracer,
            ddsmt,
            lazy_dt,
            level,
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
    level: usize,
) -> Vec<QuantifierInstance> {
    let mut results = vec![];
    for DeferredInstantiation {
        substituted_term,
        is_exists,
        literal,
        quantifier_id,
        generation,
    } in deferred_instantiations
    {
        // Count this instantiation against the current branch (rolled back on
        // backtrack) so runaway self-instantiation is penalized in the cost.
        solver_state.record_branch_instance(quantifier_id, level);

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

        // INSTRUMENTATION: dump instantiations for analysis (env SUNDANCE_DUMP_INSTS)
        if std::env::var("SUNDANCE_DUMP_INSTS").is_ok() {
            eprintln!("INST qid={} gen={} :: {}", quantifier_id, generation, t);
        }

        let let_elim_term = t.let_elim(&mut solver_state.context);

        let nnf_term = let_elim_term.nnf(solver_state);

        // Propagate generation onto the materialized terms so terms created here
        // seed future matches at the correct depth.
        solver_state.set_generation(t.uid(), generation);
        solver_state.set_generation(nnf_term.uid(), generation);

        debug_println!(26, 4, "(assert {})", nnf_term.clone());

        solver_state.insert_predecessor(&nnf_term, None, None, true);

        let cnf_term = nnf_term.cnf_tseitin(solver_state);

        let mut clauses: Vec<_> = cnf_term
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

        results.push(QuantifierInstance::Instantiation { clauses });
    }
    results
}

#[cfg(test)]
mod tests {
    use super::*;

    fn base_inputs() -> CostInputs {
        CostInputs {
            generation: 0,
            weight: 1,
            size: 4,
            depth: 2,
            vars: 1,
            pattern_width: 1,
            instances: 0,
            total_instances: 0,
            scope: 0,
            cs_factor: 1,
        }
    }

    #[test]
    fn deeper_generation_costs_more() {
        let w = CostWeights::default();
        let shallow = base_inputs();
        let deep = CostInputs {
            generation: 5,
            ..base_inputs()
        };
        assert!(instantiation_cost(&deep, &w) > instantiation_cost(&shallow, &w));
    }

    #[test]
    fn more_instances_costs_more() {
        let w = CostWeights::default();
        let few = base_inputs();
        let many = CostInputs {
            instances: 3,
            total_instances: 10,
            ..base_inputs()
        };
        assert!(instantiation_cost(&many, &w) > instantiation_cost(&few, &w));
    }

    #[test]
    fn higher_weight_costs_more() {
        let w = CostWeights::default();
        let light = base_inputs();
        let heavy = CostInputs {
            weight: 100,
            ..base_inputs()
        };
        assert!(instantiation_cost(&heavy, &w) > instantiation_cost(&light, &w));
    }

    #[test]
    fn zero_weights_ignore_inputs() {
        let w = CostWeights {
            generation: 0.0,
            weight: 0.0,
            size: 0.0,
            depth: 0.0,
            vars: 0.0,
            pattern_width: 0.0,
            instances: 0.0,
            scope: 0.0,
            cs_factor: 0.0,
        };
        let a = base_inputs();
        let b = CostInputs {
            generation: 99,
            weight: 99,
            instances: 99,
            ..base_inputs()
        };
        assert_eq!(instantiation_cost(&a, &w), instantiation_cost(&b, &w));
    }

    #[test]
    fn heap_pops_cheapest_first() {
        use yaspar_ir::ast::{Context, ObjectAllocatorExt};
        // A max-heap of PrioritizedInstantiation must yield ascending cost,
        // with insertion order (seq) breaking ties.
        let mut context = Context::new();
        let t = context.get_true();
        let mk = |cost: f64, seq: u64| PrioritizedInstantiation {
            cost,
            seq,
            inst: DeferredInstantiation {
                substituted_term: t.clone(),
                is_exists: false,
                literal: 1,
                quantifier_id: 0,
                generation: 0,
            },
        };
        let mut heap = BinaryHeap::new();
        heap.push(mk(3.0, 0));
        heap.push(mk(1.0, 1));
        heap.push(mk(2.0, 2));
        heap.push(mk(1.0, 3)); // same cost as seq 1, but later => pops after it
        let order: Vec<(f64, u64)> =
            std::iter::from_fn(|| heap.pop().map(|p| (p.cost, p.seq))).collect();
        assert_eq!(order, vec![(1.0, 1), (1.0, 3), (2.0, 2), (3.0, 0)]);
    }
}
