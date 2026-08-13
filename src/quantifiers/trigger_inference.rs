// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Automatic trigger (pattern) inference for quantifiers with no `:pattern`.
//!
//! Sundance only instantiates by e-matching, so an untriggered `forall` needs
//! an inferred trigger. This implements the Simplify/Z3 auto-trigger algorithm
//! (Detlefs, Nelson & Saxe 2005, §5):
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
//!      valid trigger exists and we return `None`.

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

/// Recursively collect candidate trigger subterms of `term` (the quantifier
/// body at the top-level call).
///
/// `bound` is the set of bound-variable names of the quantifier. A subterm is a
/// candidate iff it is an application with an uninterpreted head, contains at
/// least one bound variable, and is safe to compile as a pattern (see
/// [`is_pattern_safe`]). We collect candidates from every level so that step
/// 2/3 can prefer the shallowest covering terms.
fn collect_candidates(term: &Term, bound: &BTreeSet<String>, out: &mut Vec<Candidate>) {
    match term.repr() {
        App(func, args, _) => {
            let name = func.id_str().get().clone();
            // Recurse into arguments first (collect nested candidates too).
            for a in args.iter() {
                collect_candidates(a, bound, out);
            }
            // Only uninterpreted heads are admissible; compute coverage lazily
            // (only here, not for every node) and skip terms that pattern
            // compilation cannot handle.
            if !is_interpreted_head(&name) {
                let vars = free_bound_vars(term, bound);
                if !vars.is_empty() && is_pattern_safe(term) {
                    out.push(Candidate {
                        term: term.clone(),
                        vars,
                        depth: term_depth(term),
                    });
                }
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

/// Whether `term` can be compiled into an e-matching pattern without panicking.
///
/// Pattern compilation (`SolverState::build_pattern`/`extract_op`) only handles
/// applications, equality, boolean connectives, `ite`, constants, and variables.
/// A candidate whose subtree contains a binder, `let`, `match`, annotation, or
/// `xor` would panic during compilation, so such candidates are rejected here.
fn is_pattern_safe(term: &Term) -> bool {
    match term.repr() {
        Constant(..) | Global(..) | Local(..) => true,
        App(_, args, _) => args.iter().all(is_pattern_safe),
        Eq(l, r) => is_pattern_safe(l) && is_pattern_safe(r),
        Not(t) => is_pattern_safe(t),
        Ite(a, b, c) => is_pattern_safe(a) && is_pattern_safe(b) && is_pattern_safe(c),
        And(items) | Or(items) | Distinct(items) => items.iter().all(is_pattern_safe),
        Implies(ante, cons) => ante.iter().all(is_pattern_safe) && is_pattern_safe(cons),
        // Xor, Forall, Exists, Let, Matching, Annotated: unsupported by extract_op.
        _ => false,
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
/// quantifier's bound variables. `excluded` holds the terms named by any
/// `:no-pattern` annotations — anti-trigger hints that must never be used as a
/// trigger. Returns a list of multi-patterns, where each multi-pattern is a
/// conjunctive list of trigger terms (matching the `Vec<Vec<_>>` shape used by
/// the rest of the solver): the outer list is disjunctive (any multi-pattern
/// may fire), the inner list conjunctive.
///
/// Returns `None` if no admissible trigger set covers all bound variables.
pub fn infer_triggers(
    body: &Term,
    bound_names: &[String],
    excluded: &[Term],
) -> Option<Vec<Vec<Term>>> {
    let bound: BTreeSet<String> = bound_names.iter().cloned().collect();
    if bound.is_empty() {
        // Ground body under a (degenerate) quantifier: nothing to instantiate on.
        return None;
    }

    let mut candidates: Vec<Candidate> = Vec::new();
    collect_candidates(body, &bound, &mut candidates);

    // Drop `:no-pattern` terms: they are explicitly forbidden as triggers.
    if !excluded.is_empty() {
        let excluded: BTreeSet<String> = excluded.iter().map(|t| t.to_string()).collect();
        candidates.retain(|c| !excluded.contains(&c.term.to_string()));
    }

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
