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
use crate::utils::{DeterministicHashMap, DeterministicHashSet};

use crate::debug_println;
use yaspar_ir::ast::{
    ATerm, LetElim, Local, Repr, Sort, Str, Substitute, Substitution, Term, TermAllocator,
};

/// Instance trajectory trace (`SUNDANCE_INST_TRACE=1`): one `INST` line on
/// stderr per instance created, with the matching round, the quantifier's
/// id, the matcher that produced the bindings (native or top-down), the
/// substitution, and the fully substituted body; one `INST-DUP` line per
/// match rejected by the instance dedup; one `INST-Q` line the first time a
/// quantifier instantiates, carrying its full term. Two traces, one per
/// matcher, diff round by round to show where the instance sets diverge.
fn inst_trace() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("SUNDANCE_INST_TRACE").is_some())
}
static INST_ROUND: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
static INST_SEEN_Q: std::sync::Mutex<Vec<u64>> = std::sync::Mutex::new(Vec::new());

/// Instantiation bound by generation (`SUNDANCE_QI_MAX_GEN=<n>`, or
/// `--max-generation`): a match whose instance would have a generation
/// above `n` is not instantiated in a bounded round. Z3 bounds the same
/// quantity through `qi.eager_threshold` / `qi.lazy_threshold` with the
/// default cost `(+ weight generation)`. The complete-model round retries
/// unbounded when the bounded round yields nothing, so a proof that needs a
/// deep instance is still found; the bound changes the order, not the set.
pub(crate) fn qi_max_generation() -> Option<u32> {
    static V: std::sync::OnceLock<Option<u32>> = std::sync::OnceLock::new();
    *V.get_or_init(|| {
        std::env::var("SUNDANCE_QI_MAX_GEN")
            .ok()
            .and_then(|s| s.parse().ok())
            .filter(|&n| n > 0)
    })
}
/// Matches skipped by the generation bound, over the run (counted once per
/// round they are skipped in).
pub(crate) static INST_GEN_SKIPPED: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);

/// Generation of the term bound to a variable: 0 for an input term.
fn term_generation(solver_state: &SolverState, t: &Term) -> u32 {
    solver_state
        .term_generation
        .get(&t.uid())
        .copied()
        .unwrap_or(0)
}

/// Give every subterm of `term` that has no generation yet the generation
/// `g` (a term created earlier keeps its own, as Z3's enodes do).
fn tag_generation(solver_state: &mut SolverState, term: &Term, g: u32) {
    let mut stack = vec![term.clone()];
    while let Some(t) = stack.pop() {
        if solver_state.term_generation.contains_key(&t.uid()) {
            continue;
        }
        solver_state.term_generation.insert(t.uid(), g);
        stack.extend(t.repr().sub_terms().cloned());
    }
}

fn fmt_subs(subs: &DeterministicHashMap<Local, Term>) -> String {
    let mut kv: Vec<String> = subs
        .iter()
        .map(|(k, v)| format!("{}->{v}", k.symbol))
        .collect();
    kv.sort();
    kv.join(", ")
}

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
    /// One more than the largest generation among the bindings.
    generation: u32,
    /// Usefulness under the assignment the round saw (`qi_priority`): 0 the
    /// body is already false (a conflict), 1 unit (one atom undetermined),
    /// 2 otherwise. Orders materialization unless `SUNDANCE_QI_TRIAGE=0`.
    priority: u8,
}

/// Materialize a round's instances in generation order (shallowest first),
/// so a `--batch-cap` is breadth-first too. On by default;
/// `SUNDANCE_QI_SORT=0` turns it off.
pub(crate) fn qi_sort() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("SUNDANCE_QI_SORT").map_or(true, |v| v != "0"))
}
/// Conflicting instances first, unit next, the rest by generation (cvc5's
/// conflict-based instantiation as an ordering). On by default;
/// `SUNDANCE_QI_TRIAGE=0` turns it off.
pub(crate) fn qi_triage() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("SUNDANCE_QI_TRIAGE").map_or(true, |v| v != "0"))
}
/// On by default (`SUNDANCE_QI_DEEPEN=0` turns it off): when nothing at or
/// below the generation bound is
/// left, the complete-model round raises the bound to the smallest held
/// generation instead of dropping it (iterative deepening of the instance
/// chain), so a matching loop at depth 300 does not re-enter the moment the
/// shallow instances are exhausted.
pub(crate) fn qi_deepen() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("SUNDANCE_QI_DEEPEN").map_or(true, |v| v != "0"))
}

/// Three-valued value of `t` under the current assignment and e-graph, and
/// the number of undetermined atoms. An atom is determined by its SAT
/// literal when it has one and it is assigned; an equality of two terms the
/// e-graph knows is true when they are in one class; everything else,
/// including every term the instance creates, is undetermined.
fn eval3(t: &Term, solver_state: &SolverState, assignments: &[i32]) -> (Option<bool>, u32) {
    use yaspar_ir::ast::{AConstant, ATerm};
    use yaspar_ir::traits::Repr;
    let lit_val = |t: &Term| -> Option<bool> {
        let l = solver_state.get_lit_from_term_safe(t)?;
        let v = *assignments.get(l.unsigned_abs() as usize)?;
        if v == 0 {
            None
        } else {
            Some((v > 0) == (l > 0))
        }
    };
    match t.repr() {
        ATerm::Constant(AConstant::Bool(b), _) => (Some(*b), 0),
        ATerm::Not(x) => {
            let (v, u) = eval3(x, solver_state, assignments);
            (v.map(|b| !b), u)
        }
        ATerm::And(ts) | ATerm::Or(ts) => {
            let is_and = matches!(t.repr(), ATerm::And(_));
            let mut unknown = 0;
            let mut decided = None;
            for x in ts.iter() {
                let (v, u) = eval3(x, solver_state, assignments);
                match v {
                    Some(b) if b != is_and => decided = Some(b),
                    Some(_) => {}
                    None => unknown += u.max(1),
                }
            }
            match (decided, unknown) {
                (Some(b), _) => (Some(b), 0),
                (None, 0) => (Some(is_and), 0),
                (None, u) => (None, u),
            }
        }
        ATerm::Implies(ts, b) => {
            let mut unknown = 0;
            let mut decided = None;
            for x in ts.iter() {
                let (v, u) = eval3(x, solver_state, assignments);
                match v {
                    Some(false) => decided = Some(true),
                    Some(true) => {}
                    None => unknown += u.max(1),
                }
            }
            let (vb, ub) = eval3(b, solver_state, assignments);
            match vb {
                Some(true) => decided = Some(true),
                Some(false) => {}
                None => unknown += ub.max(1),
            }
            match (decided, unknown) {
                (Some(v), _) => (Some(v), 0),
                (None, 0) => (Some(false), 0),
                (None, u) => (None, u),
            }
        }
        ATerm::Ite(c, a, b) => match eval3(c, solver_state, assignments).0 {
            Some(true) => eval3(a, solver_state, assignments),
            Some(false) => eval3(b, solver_state, assignments),
            None => (None, 1),
        },
        ATerm::Eq(a, b) => {
            if let (Some(&ea), Some(&eb)) = (
                solver_state.id_map.get_by_left(&a.uid()),
                solver_state.id_map.get_by_left(&b.uid()),
            ) && solver_state.egraph.are_equal(ea, eb)
            {
                return (Some(true), 0);
            }
            match lit_val(t) {
                Some(v) => (Some(v), 0),
                None => (None, 1),
            }
        }
        _ => match lit_val(t) {
            Some(v) => (Some(v), 0),
            None => (None, 1),
        },
    }
}

fn qi_priority(t: &Term, solver_state: &SolverState, assignments: &[i32]) -> u8 {
    if !qi_triage() {
        return 2;
    }
    match eval3(t, solver_state, assignments) {
        (Some(false), _) => 0,
        (None, 1) => 1,
        _ => 2,
    }
}

/// A match the generation bound left uninstantiated (Z3's delayed `qi_queue`
/// entries): re-examined at the start of every round against that round's
/// bound, so a match found when its class changed is not lost to the
/// incremental matcher's filter once the bound rises.
pub struct GenDeferred {
    pub quantifier_id: u64,
    pub body: u64,
    pub subs: DeterministicHashMap<Local, Term>,
    pub generation: u32,
    pub is_exists: bool,
    pub literal: i32,
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

/// All locals occurring anywhere in `term`. Over-approximates the free
/// variables (locals bound by nested binders are included), which only makes
/// instantiation de-duplication more conservative.
pub(crate) fn collect_locals(term: &Term) -> DeterministicHashSet<Local> {
    let mut locals = DeterministicHashSet::new();
    let mut visited = std::collections::HashSet::new();
    let mut stack = vec![term.clone()];
    while let Some(t) = stack.pop() {
        if !visited.insert(t.uid()) {
            continue;
        }
        if let ATerm::Local(local) = t.repr() {
            locals.insert(local.clone());
        }
        stack.extend(t.repr().sub_terms().cloned());
    }
    locals
}

/// Computes trigger matches and substitutions, returning deferred items
/// that can be materialized one at a time.
pub(crate) fn instantiate_quantifiers(
    solver_state: &mut SolverState,
    assignments: &[i32],
    allow_skolemization: bool,
    max_generation: Option<u32>,
) -> PendingInstantiations {
    let eager_skolem = solver_state.eager_skolem;
    debug_println!(24, 0, "Starting a matching round");
    let round = INST_ROUND.fetch_add(1, std::sync::atomic::Ordering::Relaxed) + 1;
    if inst_trace() {
        eprintln!(
            "INST-ROUND r={round} complete_model={allow_skolemization} assigned_lits={} max_gen={}",
            assignments.iter().filter(|&&a| a != 0).count(),
            max_generation.map_or("none".to_string(), |g| g.to_string())
        );
    }
    let quantifiers = &solver_state.quantifiers.clone();
    let mut skolemized_quantifier_idxs = vec![];
    let mut deferred_skolemizations: VecDeque<DeferredSkolemization> = VecDeque::new();
    let mut deferred_instantiations: VecDeque<DeferredInstantiation> = VecDeque::new();

    // Matches an earlier bounded round left: those within this round's
    // bound are instantiated now (an instance clause is implied by its
    // quantifier whatever the current assignment), the rest wait.
    let held = std::mem::take(&mut solver_state.gen_deferred);
    for d in held {
        if max_generation.is_some_and(|b| d.generation > b) {
            solver_state.gen_deferred.push(d);
            continue;
        }
        solver_state
            .gen_deferred_keys
            .get_mut(&d.quantifier_id)
            .map(|set| set.remove(&d.subs));
        if solver_state
            .added_instantiations
            .get(&d.quantifier_id)
            .is_some_and(|set| set.contains(&d.subs))
        {
            continue;
        }
        solver_state
            .added_instantiations
            .entry(d.quantifier_id)
            .or_default()
            .insert(d.subs.clone());
        let term = solver_state.get_term(d.body);
        let substitution = Substitution::new(d.subs);
        let substituted_term = term.subst(&substitution, &mut solver_state.context);
        if inst_trace() {
            eprintln!(
                "INST r={round} q={} src=deferred gen={} inst={substituted_term}",
                d.quantifier_id, d.generation
            );
        }
        let priority = qi_priority(&substituted_term, solver_state, assignments);
        deferred_instantiations.push_back(DeferredInstantiation {
            substituted_term,
            is_exists: d.is_exists,
            literal: d.literal,
            quantifier_id: d.quantifier_id,
            generation: d.generation,
            priority,
        });
    }

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
            if inst_trace() {
                // The ground check (`instance_check.py`) declares these
                // constants and asserts the clause sundance adds:
                // exists: (=> Q skolem); forall: (=> (not Q) skolem).
                let decls: Vec<String> = skolem_vars
                    .iter()
                    .map(|(n, s)| format!("{n}:{s}"))
                    .collect();
                eprintln!(
                    "INST-SK q={} exists={} decls=[{}] qterm={} skolem={}",
                    quantifier.id,
                    quantifier_is_exists,
                    decls.join(";"),
                    term,
                    skolem
                );
            }

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

        // Z3 instantiates a quantifier only once its atom is relevant
        // (`context::propagate_relevancy` queues a quantifier atom for the
        // quantifier manager only when it is marked). The backend answers
        // true outside relevancy-filtered rounds, so the complete-model round
        // is never gated.
        if let Some(&qeid) = solver_state.id_map.get_by_left(&quantifier.id)
            && !solver_state.egraph.is_term_relevant(qeid)
        {
            if inst_trace() {
                eprintln!("INST-QSKIP r={round} q={} eid={qeid}", quantifier.id);
            }
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
            // Under incremental matching the backend filters the first
            // pattern's candidates to the classes changed since the previous
            // round, so each pattern of a multipattern takes the first
            // position in turn (the dedup below absorbs the repeats); one
            // order otherwise.
            let rotations = if solver_state.egraph.incremental_matching() {
                multipattern.len()
            } else {
                1
            };
            let mut list_assignments = Vec::new();
            for k in 0..rotations {
                let first = multipattern[k];
                let rest: Vec<(usize, Option<u32>)> = multipattern[k + 1..]
                    .iter()
                    .chain(multipattern[..k].iter())
                    .map(|t| (*t, None))
                    .collect();
                // The first pattern of the multipattern is rooted at each
                // triggering term the backend offers (one per e-class with the
                // root operator); the remaining patterns join unrooted. A backend
                // with no hints gets the single unrooted call.
                match solver_state.egraph.trigger_root_candidates(first) {
                    None => {
                        let mut pairs = Vec::with_capacity(rest.len() + 1);
                        pairs.push((first, None));
                        pairs.extend(rest.iter().copied());
                        list_assignments.extend(solver_state.egraph.match_triggers(pairs));
                    }
                    Some(roots) => {
                        for root in roots {
                            let mut pairs = Vec::with_capacity(rest.len() + 1);
                            pairs.push((first, Some(root)));
                            pairs.extend(rest.iter().copied());
                            list_assignments.extend(solver_state.egraph.match_triggers(pairs));
                        }
                    }
                }
            }

            if list_assignments.is_empty() {
                continue;
            }
            let src = if solver_state.egraph.last_match_native() {
                "native"
            } else {
                "top-down"
            };
            if inst_trace() {
                let mut seen = INST_SEEN_Q.lock().expect("trace lock");
                if !seen.contains(&quantifier.id) {
                    seen.push(quantifier.id);
                    eprintln!(
                        "INST-Q q={} term={}",
                        quantifier.id,
                        solver_state.get_term(quantifier.id)
                    );
                }
                eprintln!(
                    "INST-MATCHES r={round} q={} src={src} matches={}",
                    quantifier.id,
                    list_assignments.len()
                );
            }

            for subs_ids in list_assignments.iter() {
                // Convert the (Local -> egraph id) map into a (Local -> Term) map for substitution.
                // Bound variables that do not occur in the body are dropped, so matches that
                // differ only in them (e.g. every match of a ground body) share one instance.
                let subs: DeterministicHashMap<Local, Term> = subs_ids
                    .iter()
                    .filter(|(k, _)| quantifier.body_locals.contains(*k))
                    .map(|(k, v)| {
                        (
                            k.clone(),
                            solver_state.get_term(solver_state.to_solver_uid(*v)),
                        )
                    })
                    .collect();

                // Checked before the dedup records the match, so a bounded
                // round leaves the match for a later round at a higher bound.
                let generation = 1 + subs
                    .values()
                    .map(|t| term_generation(solver_state, t))
                    .max()
                    .unwrap_or(0);
                if let Some(bound) = max_generation
                    && generation > bound
                {
                    INST_GEN_SKIPPED.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    if inst_trace() {
                        eprintln!(
                            "INST-GENSKIP r={round} q={} gen={generation} subs=[{}]",
                            quantifier.id,
                            fmt_subs(&subs)
                        );
                    }
                    let fresh = solver_state
                        .gen_deferred_keys
                        .entry(quantifier.id)
                        .or_default()
                        .insert(subs.clone());
                    if fresh
                        && !solver_state
                            .added_instantiations
                            .get(&quantifier.id)
                            .is_some_and(|set| set.contains(&subs))
                    {
                        solver_state.gen_deferred.push(GenDeferred {
                            quantifier_id: quantifier.id,
                            body,
                            subs,
                            generation,
                            is_exists: quantifier_is_exists,
                            literal: quantifier_literal,
                        });
                    }
                    continue;
                }

                if let Some(set) = solver_state.added_instantiations.get(&quantifier.id)
                    && set.contains(&subs)
                {
                    if inst_trace() {
                        eprintln!(
                            "INST-DUP r={round} q={} src={src} subs=[{}]",
                            quantifier.id,
                            fmt_subs(&subs)
                        );
                    }
                    continue;
                }
                solver_state
                    .added_instantiations
                    .entry(quantifier.id)
                    .or_default()
                    .insert(subs.clone());

                let term = solver_state.get_term(body);
                let subs_text = inst_trace().then(|| fmt_subs(&subs));
                let substitution = Substitution::new(subs);
                let substituted_term = term.subst(&substitution, &mut solver_state.context);
                if let Some(subs_text) = subs_text {
                    eprintln!(
                        "INST r={round} q={} src={src} gen={generation} subs=[{subs_text}] inst={substituted_term}",
                        quantifier.id
                    );
                }
                let priority = qi_priority(&substituted_term, solver_state, assignments);
                deferred_instantiations.push_back(DeferredInstantiation {
                    substituted_term,
                    is_exists: quantifier_is_exists,
                    literal: quantifier_literal,
                    quantifier_id: quantifier.id,
                    generation,
                    priority,
                });
            }
        }
    }

    if qi_triage() || qi_sort() {
        // Stable: ties keep the matcher's order.
        let triage = qi_triage();
        let sort = qi_sort();
        deferred_instantiations.make_contiguous().sort_by_key(|d| {
            (
                if triage { d.priority } else { 0 },
                if sort { d.generation } else { 0 },
            )
        });
        if inst_trace() {
            let c = deferred_instantiations
                .iter()
                .filter(|d| d.priority == 0)
                .count();
            let u = deferred_instantiations
                .iter()
                .filter(|d| d.priority == 1)
                .count();
            eprintln!(
                "INST-TRIAGE r={round} conflicting={c} unit={u} other={}",
                deferred_instantiations.len() - c - u
            );
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
        // A skolemization body is a relevancy root exactly as an instance body
        // is: Z3 asserts the witness formula as part of a root clause, so its
        // terms are relevant once it is true. Without the seed, the terms of
        // a witness (`(apply f sk)` of a false `forall`) stayed irrelevant and
        // the instances refuting it were never matched (Utils_v.5).
        if std::env::var_os("SUNDANCE_REL_NO_SEED_SKOLEM").is_none()
            && let Some(&eid) = solver_state.id_map.get_by_left(&reduced_skolem.uid())
        {
            solver_state.egraph.note_instance_root(eid);
        }

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
) -> Vec<QuantifierInstance> {
    let mut results = vec![];
    for DeferredInstantiation {
        substituted_term,
        is_exists,
        literal,
        quantifier_id,
        generation,
        priority: _,
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

        // The terms this instance creates carry its generation; the NNF is
        // what the e-graph registers and what later matches bind.
        tag_generation(solver_state, &nnf_term, generation);

        solver_state.insert_predecessor(&nnf_term, None, None, true);
        // The instance body is a relevancy root in Z3 (asserted as a root
        // clause with relevancy watches); tell the backend which term it is.
        if let Some(&eid) = solver_state.id_map.get_by_left(&nnf_term.uid()) {
            solver_state.egraph.note_instance_root(eid);
        }

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

        results.push(QuantifierInstance::Instantiation { clauses });
    }
    results
}
