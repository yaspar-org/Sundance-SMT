// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Destructive equality resolution (DER).
//!
//! `(forall (x y) (=> (= x t) P))` is equivalent to `(forall (y) P[x := t])` when `x` does not
//! occur in `t`, and dually `(exists (x y) (and (= x t) P))` is equivalent to
//! `(exists (y) P[x := t])`. Z3 does this rewrite in preprocessing. It matters most for quantifiers
//! that have no trigger (for example ones whose body is pure arithmetic): when every bound variable
//! is eliminated, the quantifier becomes ground and needs no instantiation.
//!
//! Only quantifiers without explicit `:pattern`s are rewritten. Their patterns tell us how the
//! front end wants them instantiated, and rewriting changes that: partial elimination substitutes
//! `t` into the patterns (`(P (+ y 1) y)` matches less often than `(P x y)`), and eliminating the
//! variable of a patterned `exists` (e.g. in Verus' `choose` axioms) replaces its skolemization by
//! the instantiated body, which was measured to slow down some Verus queries.

use crate::utils::FastDeterministicHashMap as HashMap;
use yaspar_ir::ast::alg::VarBinding;
use yaspar_ir::ast::fv::FreeLocalVars;
use yaspar_ir::ast::subst::{Substitute, Substitution};
use yaspar_ir::ast::{ATerm, Attribute, Context, Local, Sort, Str, Term, TermAllocator};
use yaspar_ir::traits::Repr;

/// Apply destructive equality resolution to every quantifier in `term` that is reachable through
/// Boolean connectives (including quantifiers nested in quantifier bodies).
pub fn der(term: &Term, context: &mut Context) -> Term {
    Der::default().rewrite(term, context)
}

#[derive(Default)]
struct Der {
    cache: HashMap<Term, Term>,
}

impl Der {
    fn rewrite(&mut self, term: &Term, context: &mut Context) -> Term {
        if let Some(r) = self.cache.get(term) {
            return r.clone();
        }
        // Terms are hash-consed, so rebuilding a term whose children did not change gives back
        // the same term.
        let r = match term.repr() {
            ATerm::And(ts) => {
                let ts = self.rewrite_all(ts, context);
                context.and(ts)
            }
            ATerm::Or(ts) => {
                let ts = self.rewrite_all(ts, context);
                context.or(ts)
            }
            ATerm::Not(t) => {
                let t = self.rewrite(t, context);
                context.not(t)
            }
            ATerm::Implies(hs, c) => {
                let hs = self.rewrite_all(hs, context);
                let c = self.rewrite(c, context);
                context.implies(hs, c)
            }
            ATerm::Annotated(t, attrs) => {
                let t = self.rewrite(t, context);
                context.annotated(t, attrs.clone())
            }
            ATerm::Forall(vars, body) => {
                let body = self.rewrite(body, context);
                eliminate(true, vars, body, context)
            }
            ATerm::Exists(vars, body) => {
                let body = self.rewrite(body, context);
                eliminate(false, vars, body, context)
            }
            _ => term.clone(),
        };
        self.cache.insert(term.clone(), r.clone());
        r
    }

    fn rewrite_all(&mut self, ts: &[Term], context: &mut Context) -> Vec<Term> {
        ts.iter().map(|t| self.rewrite(t, context)).collect()
    }
}

/// Split an annotated quantifier body into the body proper and its attributes.
fn split(body: &Term) -> (Term, Vec<Attribute>) {
    match body.repr() {
        ATerm::Annotated(inner, attrs) => (inner.clone(), attrs.clone()),
        _ => (body.clone(), vec![]),
    }
}

/// Rebuild the quantifier with variables `vars` and the already rewritten `body`, eliminating the
/// variables that are defined by an equality.
fn eliminate(
    is_forall: bool,
    vars: &[VarBinding<Str, Sort>],
    body: Term,
    context: &mut Context,
) -> Term {
    let (_, attrs) = split(&body);
    if attrs.iter().any(|a| matches!(a, Attribute::Pattern(_))) {
        return if is_forall {
            context.forall(vars.to_vec(), body)
        } else {
            context.exists(vars.to_vec(), body)
        };
    }
    let mut remaining = vars.to_vec();
    let mut new_body = body.clone();
    loop {
        let (inner, _) = split(&new_body);
        let Some((i, t)) = find_definition(&inner, &remaining, is_forall) else {
            break;
        };
        let x: Local = remaining.remove(i).into();
        new_body = new_body.subst(&Substitution::new([(x, t)]), context);
    }

    if remaining.is_empty() {
        // The quantifier is now ground; its attributes (e.g. `:qid`) no longer apply.
        return split(&new_body).0;
    }
    if is_forall {
        context.forall(remaining, new_body)
    } else {
        context.exists(remaining, new_body)
    }
}

/// Find an equality `x = t` that defines one of `vars`, at a position where it can be eliminated.
///
/// In a `forall` body we look for a disjunct `(not (= x t))`; in an `exists` body for a conjunct
/// `(= x t)`. `disjunct` says which of the two we are looking for in `t`. We only descend
/// through `or`, `and`, `not`, and `=>`, never through binders, so `t` cannot capture variables.
fn find_definition(
    term: &Term,
    vars: &[VarBinding<Str, Sort>],
    disjunct: bool,
) -> Option<(usize, Term)> {
    match term.repr() {
        ATerm::Or(ts) if disjunct => ts.iter().find_map(|t| find_definition(t, vars, true)),
        ATerm::And(ts) if !disjunct => ts.iter().find_map(|t| find_definition(t, vars, false)),
        // `(=> h1 ... hn c)` is `(or (not h1) ... (not hn) c)`
        ATerm::Implies(hs, c) if disjunct => hs
            .iter()
            .find_map(|h| find_definition(h, vars, false))
            .or_else(|| find_definition(c, vars, true)),
        ATerm::Not(t) => find_definition(t, vars, !disjunct),
        ATerm::Eq(a, b) if !disjunct => definition(a, b, vars).or_else(|| definition(b, a, vars)),
        _ => None,
    }
}

/// If `x` is one of `vars` and does not occur in `t`, return its index and `t`.
fn definition(x: &Term, t: &Term, vars: &[VarBinding<Str, Sort>]) -> Option<(usize, Term)> {
    let ATerm::Local(local) = x.repr() else {
        return None;
    };
    let i = vars.iter().position(|v| v.1 == local.id)?;
    if t.free_loc_vars().iter().any(|(_, id)| *id == local.id) {
        return None;
    }
    Some((i, t.clone()))
}
