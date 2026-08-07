// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Automatic trigger (pattern) inference for quantifiers that carry no
//! `:pattern` annotation.
//!
//! Boogie/Dafny and F* emit many quantified axioms without explicit triggers
//! and rely on the solver to infer them (Z3/Simplify) or to fall back to MBQI.
//! Sundance only does pattern-based (e-matching) instantiation, so without a
//! trigger such a quantifier cannot be instantiated at all — historically we
//! `panic!`ed on it.
//!
//! This module implements the classic Simplify/Z3 auto-trigger algorithm
//! (Detlefs, Nelson & Saxe 2005, §5; see also Leino & Pit-Claudel, CAV 2016):
//!
//!   1. Collect *candidate* subterms of the body: applications whose head is an
//!      **uninterpreted** function/predicate and that contain at least one bound
//!      variable. Interpreted symbols (`=`, `and`, `+`, `<`, `ite`, …) are never
//!      admissible pattern heads — the theory solvers already reason about them,
//!      and e-matching on them explodes.
//!   2. If any candidates jointly with the *fewest* function symbols cover all
//!      bound variables on their own, emit them as **single-term triggers**
//!      (preferring shallow/minimal terms).
//!   3. Otherwise greedily assemble a **multi-pattern**: a minimal set of
//!      candidates whose covered-variable sets union to all bound variables.
//!   4. If some bound variable never appears under any uninterpreted symbol, no
//!      valid trigger exists; we return `None` and the caller decides the
//!      fallback (skip the quantifier — sound for unsat, incomplete otherwise).

use std::collections::BTreeSet;

use yaspar_ir::ast::ATerm::*;
use yaspar_ir::ast::{Repr, Term};

/// A candidate trigger term together with the set of bound-variable names it
/// covers and a rough size (number of nested applications), used to prefer
/// shallow triggers.
struct Candidate {
    term: Term,
    vars: BTreeSet<String>,
    depth: usize,
}

/// Returns `true` if `name` is an interpreted/theory symbol that must never be
/// used as a pattern head. Uninterpreted-function heads (everything else) are
/// admissible. Arithmetic operators appear as `App(name)` in this IR, so they
/// are rejected here by name.
fn is_interpreted_head(name: &str) -> bool {
    matches!(
        name,
        "=" | "distinct"
            | "and"
            | "or"
            | "not"
            | "=>"
            | "xor"
            | "ite"
            | "+"
            | "-"
            | "*"
            | "/"
            | "div"
            | "mod"
            | "rem"
            | "abs"
            | "<"
            | "<="
            | ">"
            | ">="
            | "true"
            | "false"
    )
}

/// Recursively collect candidate trigger subterms of `body`.
///
/// `bound` is the set of bound-variable names of the quantifier. A subterm is a
/// candidate iff it is an application with an uninterpreted head and it contains
/// at least one bound variable. We collect candidates from every level so that
/// step 2/3 can prefer the shallowest covering terms.
fn collect_candidates(term: &Term, bound: &BTreeSet<String>, out: &mut Vec<Candidate>) {
    // Compute the bound variables occurring in `term` and recurse into children.
    let vars = free_bound_vars(term, bound);

    match term.repr() {
        App(func, args, _) => {
            let name = func.id_str().get().clone();
            // Recurse into arguments first (collect nested candidates too).
            for a in args.iter() {
                collect_candidates(a, bound, out);
            }
            if !is_interpreted_head(&name) && !vars.is_empty() {
                out.push(Candidate {
                    term: term.clone(),
                    vars,
                    depth: term_depth(term),
                });
            }
        }
        // Interpreted logical/relational connectives: never candidates
        // themselves, but their subterms can be.
        Eq(l, r) => {
            collect_candidates(l, bound, out);
            collect_candidates(r, bound, out);
        }
        Not(t) => collect_candidates(t, bound, out),
        Ite(c, t, e) => {
            collect_candidates(c, bound, out);
            collect_candidates(t, bound, out);
            collect_candidates(e, bound, out);
        }
        And(items) | Or(items) | Distinct(items) | Xor(items) => {
            for it in items.iter() {
                collect_candidates(it, bound, out);
            }
        }
        Implies(ante, cons) => {
            for a in ante.iter() {
                collect_candidates(a, bound, out);
            }
            collect_candidates(cons, bound, out);
        }
        // Do not descend into nested quantifiers: their bound variables shadow
        // ours and their triggers are handled when they are registered.
        Forall(..) | Exists(..) => {}
        Annotated(inner, _) => collect_candidates(inner, bound, out),
        Let(..) => {} // Lets are inlined before registration.
        _ => {}
    }
}

/// The subset of `bound` variable names that occur free in `term`
/// (i.e. not shadowed by a nested binder).
fn free_bound_vars(term: &Term, bound: &BTreeSet<String>) -> BTreeSet<String> {
    let mut set = BTreeSet::new();
    collect_bound_vars(term, bound, &mut set);
    set
}

fn collect_bound_vars(term: &Term, bound: &BTreeSet<String>, out: &mut BTreeSet<String>) {
    match term.repr() {
        Local(local) => {
            let name = local.symbol.get().clone();
            if bound.contains(&name) {
                out.insert(name);
            }
        }
        App(_, args, _) => {
            for a in args.iter() {
                collect_bound_vars(a, bound, out);
            }
        }
        Eq(l, r) => {
            collect_bound_vars(l, bound, out);
            collect_bound_vars(r, bound, out);
        }
        Not(t) => collect_bound_vars(t, bound, out),
        Ite(c, t, e) => {
            collect_bound_vars(c, bound, out);
            collect_bound_vars(t, bound, out);
            collect_bound_vars(e, bound, out);
        }
        And(items) | Or(items) | Distinct(items) | Xor(items) => {
            for it in items.iter() {
                collect_bound_vars(it, bound, out);
            }
        }
        Implies(ante, cons) => {
            for a in ante.iter() {
                collect_bound_vars(a, bound, out);
            }
            collect_bound_vars(cons, bound, out);
        }
        Annotated(inner, _) => collect_bound_vars(inner, bound, out),
        // Nested binders shadow; conservatively don't descend (their inner
        // variables are not ours, and any of our variables used inside would
        // still be covered by an enclosing candidate).
        Forall(..) | Exists(..) => {}
        _ => {}
    }
}

/// Rough structural depth of a term (max nesting of applications), used to
/// prefer shallow triggers.
fn term_depth(term: &Term) -> usize {
    match term.repr() {
        App(_, args, _) => 1 + args.iter().map(term_depth).max().unwrap_or(0),
        Annotated(inner, _) => term_depth(inner),
        _ => 0,
    }
}

/// Infer a set of triggers (multi-patterns) for a quantifier body.
///
/// `body` is the (de-annotated) body term; `bound_names` are the names of the
/// quantifier's bound variables. Returns a list of multi-patterns, where each
/// multi-pattern is a conjunctive list of trigger terms (matching the
/// `Vec<Vec<_>>` shape used by the rest of the solver): the outer list is
/// disjunctive (any multi-pattern may fire), the inner list conjunctive.
///
/// Returns `None` if no admissible trigger set covers all bound variables.
pub fn infer_triggers(body: &Term, bound_names: &[String]) -> Option<Vec<Vec<Term>>> {
    let bound: BTreeSet<String> = bound_names.iter().cloned().collect();
    if bound.is_empty() {
        // Ground body under a (degenerate) quantifier: nothing to instantiate on.
        return None;
    }

    let mut candidates: Vec<Candidate> = Vec::new();
    collect_candidates(body, &bound, &mut candidates);

    if candidates.is_empty() {
        return None;
    }

    // Deduplicate candidates by printed form, keeping the shallowest.
    candidates.sort_by(|a, b| {
        a.depth
            .cmp(&b.depth)
            .then(a.term.to_string().cmp(&b.term.to_string()))
    });
    let mut seen = BTreeSet::new();
    candidates.retain(|c| seen.insert(c.term.to_string()));

    // Step 2: single-term triggers that cover ALL bound variables on their own.
    // Prefer the shallowest; emit each as its own (disjunctive) single trigger.
    let full_singletons: Vec<&Candidate> = candidates.iter().filter(|c| c.vars == bound).collect();
    if !full_singletons.is_empty() {
        // Use the shallowest single trigger. (Emitting just one keeps the search
        // space small; additional ones rarely help and can cause redundant
        // instantiations.)
        let best = full_singletons[0];
        return Some(vec![vec![best.term.clone()]]);
    }

    // Step 3: greedy minimal multi-pattern. Repeatedly pick the candidate that
    // covers the most still-uncovered bound variables (ties broken by shallower
    // depth), until all are covered or no progress can be made.
    let mut uncovered: BTreeSet<String> = bound.clone();
    let mut chosen: Vec<Term> = Vec::new();
    while !uncovered.is_empty() {
        let best = candidates
            .iter()
            .map(|c| (c.vars.intersection(&uncovered).count(), c))
            .filter(|(gain, _)| *gain > 0)
            .max_by(|(g1, c1), (g2, c2)| g1.cmp(g2).then(c2.depth.cmp(&c1.depth)));

        match best {
            Some((_, cand)) => {
                for v in &cand.vars {
                    uncovered.remove(v);
                }
                chosen.push(cand.term.clone());
            }
            // No candidate covers any remaining variable: uncoverable.
            None => return None,
        }
    }

    Some(vec![chosen])
}
