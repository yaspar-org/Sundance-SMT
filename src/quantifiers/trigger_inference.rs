// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Automatic trigger (pattern) inference for quantifiers with no `:pattern`.
//!
//! Sundance only instantiates by e-matching, so an untriggered `forall` needs
//! an inferred trigger. This follows Z3's pattern inference
//! (`ast/pattern/pattern_inference.cpp`, after Simplify; Detlefs, Nelson &
//! Saxe 2005, §5):
//!
//!   1. Collect *candidate* subterms of the body: applications whose head is an
//!      **uninterpreted** function/predicate and that contain at least one bound
//!      variable. Interpreted symbols (`=`, `and`, `+`, `<`, `ite`, …) are never
//!      admissible pattern heads — the theory solvers already reason about them,
//!      and e-matching on them explodes. Like Z3, collection descends into
//!      nested quantifiers; a candidate found there must not mention the nested
//!      quantifier's own variables.
//!   2. Drop the `:no-pattern` terms.
//!   3. Drop *looping* candidates: a candidate is looping if another candidate
//!      with the same variables is a proper instance of it, e.g. `(f x)` next to
//!      `(f (g x))`. Each instance would create a new match for it.
//!   4. Drop *bigger* candidates: those with a proper subterm that is a
//!      candidate with the same variables.
//!   5. Every remaining candidate that covers all bound variables is a
//!      **single-term trigger**; all of them are returned, as alternatives.
//!   6. Otherwise assemble one **multi-pattern**: go through the candidates with
//!      the most variables first, smallest first among equals, and take each
//!      one that adds a variable. Then drop members that the others make
//!      redundant.
//!   7. If nothing is found and step 2 dropped something, retry without the
//!      `:no-pattern` terms: Z3 then ignores the annotation.
//!
//! If some bound variable never appears under an uninterpreted symbol, no valid
//! trigger exists and inference returns `None`.

use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, BTreeSet};

use yaspar_ir::ast::ATerm::*;
use yaspar_ir::ast::alg::CheckIdentifier;
use yaspar_ir::ast::{Repr, Term};

/// A candidate trigger term together with the set of bound-variable names it
/// covers and its size (see [`pattern_size`]), used to prefer small triggers.
struct Candidate {
    term: Term,
    vars: BTreeSet<String>,
    size: usize,
}

/// Recursively collect candidate trigger subterms of `term` (the quantifier
/// body at the top-level call), in post-order.
///
/// `bound` holds the names of the quantifier's bound variables that are in
/// scope, and `shadowed` the names bound by the nested quantifiers on the way
/// down. A subterm is a candidate iff it is an application with an
/// uninterpreted head, contains at least one variable of `bound`, contains no
/// variable of `shadowed`, and is safe to compile as a pattern (see
/// [`is_pattern_safe`]).
fn collect_candidates(
    term: &Term,
    bound: &BTreeSet<String>,
    shadowed: &BTreeSet<String>,
    out: &mut Vec<Candidate>,
) {
    match term.repr() {
        App(func, args, _) => {
            // Recurse into arguments first (collect nested candidates too).
            for a in args.iter() {
                collect_candidates(a, bound, shadowed, out);
            }
            // Built-in/theory identifiers have an IR kind; user-declared
            // functions do not. Use that metadata rather than the symbol's
            // spelling, since names such as `rem` are valid user functions.
            if func.get_kind().is_none() {
                let vars = free_bound_vars(term, bound);
                if !vars.is_empty()
                    && is_pattern_safe(term)
                    && (shadowed.is_empty() || free_bound_vars(term, shadowed).is_empty())
                {
                    out.push(Candidate {
                        term: term.clone(),
                        vars,
                        size: pattern_size(term, bound).0,
                    });
                }
            }
        }
        // Interpreted logical/relational connectives: never candidates
        // themselves, but their subterms can be.
        Eq(l, r) => {
            collect_candidates(l, bound, shadowed, out);
            collect_candidates(r, bound, shadowed, out);
        }
        Not(t) => collect_candidates(t, bound, shadowed, out),
        Ite(c, t, e) => {
            collect_candidates(c, bound, shadowed, out);
            collect_candidates(t, bound, shadowed, out);
            collect_candidates(e, bound, shadowed, out);
        }
        And(items) | Or(items) | Distinct(items) | Xor(items) => {
            for it in items.iter() {
                collect_candidates(it, bound, shadowed, out);
            }
        }
        Implies(ante, cons) => {
            for a in ante.iter() {
                collect_candidates(a, bound, shadowed, out);
            }
            collect_candidates(cons, bound, shadowed, out);
        }
        // Look inside nested quantifiers, as Z3 does: a variable of ours may
        // occur under an uninterpreted head only there. The nested variables
        // shadow ours, and a term mentioning one cannot match a ground term.
        Forall(vars, inner) | Exists(vars, inner) => {
            let names: BTreeSet<String> = vars.iter().map(|v| v.0.get().clone()).collect();
            let bound: BTreeSet<String> = bound.difference(&names).cloned().collect();
            if !bound.is_empty() {
                let shadowed: BTreeSet<String> = shadowed.union(&names).cloned().collect();
                collect_candidates(inner, &bound, &shadowed, out);
            }
        }
        Annotated(inner, _) => collect_candidates(inner, bound, shadowed, out),
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

/// The immediate subterms of a pattern-safe term (see [`is_pattern_safe`]).
fn subterms(term: &Term) -> Vec<&Term> {
    match term.repr() {
        App(_, args, _) => args.iter().collect(),
        Eq(l, r) => vec![l, r],
        Not(t) => vec![t],
        Ite(a, b, c) => vec![a, b, c],
        And(items) | Or(items) | Distinct(items) => items.iter().collect(),
        Implies(ante, cons) => ante.iter().chain(std::iter::once(cons)).collect(),
        _ => vec![],
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

/// Size of a pattern-safe term, and whether it contains a variable of `bound`.
///
/// Every application, variable and constant counts once (Z3's pattern size),
/// except that a subterm with no bound variable counts as one node in total:
/// e-matching checks it with a single e-class lookup. This also keeps the
/// choice the same for every instance of a nested quantifier. Those instances
/// are registered with the outer variables replaced by ground terms, whereas
/// Z3 infers patterns once, before instantiation, when they are still
/// variables.
fn pattern_size(term: &Term, bound: &BTreeSet<String>) -> (usize, bool) {
    if let Local(local) = term.repr() {
        return (1, bound.contains(local.symbol.get()));
    }
    let (size, has_var) = subterms(term)
        .into_iter()
        .map(|t| pattern_size(t, bound))
        .fold((1, false), |(size, has_var), (s, h)| {
            (size + s, has_var || h)
        });
    (if has_var { size } else { 1 }, has_var)
}

/// Whether `term` is an instance of `pattern`, reading the variables of `bound`
/// in `pattern` as pattern variables (Z3's `smaller_pattern`). `bindings` maps
/// each pattern variable to the uid of the subterm it is bound to.
fn is_instance(
    pattern: &Term,
    term: &Term,
    bound: &BTreeSet<String>,
    bindings: &mut BTreeMap<String, u64>,
) -> bool {
    if let Local(local) = pattern.repr()
        && bound.contains(local.symbol.get())
    {
        return match bindings.entry(local.symbol.get().clone()) {
            Entry::Occupied(e) => *e.get() == term.uid(),
            Entry::Vacant(e) => {
                e.insert(term.uid());
                true
            }
        };
    }
    match (pattern.repr(), term.repr()) {
        (App(f, _, sf), App(g, _, sg)) if f != g || sf != sg => return false,
        (App(..), App(..))
        | (Eq(..), Eq(..))
        | (Not(..), Not(..))
        | (Ite(..), Ite(..))
        | (And(..), And(..))
        | (Or(..), Or(..))
        | (Distinct(..), Distinct(..))
        | (Implies(..), Implies(..)) => {}
        _ => return pattern.uid() == term.uid(),
    }
    let (ps, ts) = (subterms(pattern), subterms(term));
    ps.len() == ts.len()
        && ps
            .into_iter()
            .zip(ts)
            .all(|(p, t)| is_instance(p, t, bound, bindings))
}

/// Drop looping candidates (Z3's `filter_looping_patterns`): those of which
/// another candidate with the same variables is a proper instance. For `(f x)`
/// and `(f (g x))` in `f(x) = f(g(x))`, matching `(f x)` on `f(a)` yields the
/// new term `f(g(a))`, which matches again, and so on forever.
fn drop_looping<'a>(
    candidates: Vec<&'a Candidate>,
    bound: &BTreeSet<String>,
) -> Vec<&'a Candidate> {
    let instance =
        |p: &Candidate, t: &Candidate| is_instance(&p.term, &t.term, bound, &mut BTreeMap::new());
    candidates
        .iter()
        .filter(|c1| {
            !candidates.iter().any(|c2| {
                c2.term.uid() != c1.term.uid()
                    && c2.vars == c1.vars
                    && instance(c1, c2)
                    && !instance(c2, c1)
            })
        })
        .copied()
        .collect()
}

/// Drop bigger candidates (Z3's `filter_bigger_patterns`): those with a proper
/// subterm that is itself a candidate with the same variables. Such a subterm
/// matches whenever the bigger term does.
fn drop_bigger(candidates: Vec<&Candidate>) -> Vec<&Candidate> {
    let vars_of: BTreeMap<u64, &BTreeSet<String>> =
        candidates.iter().map(|c| (c.term.uid(), &c.vars)).collect();
    let has_sub_candidate = |c: &Candidate| {
        let mut seen = BTreeSet::new();
        let mut todo = subterms(&c.term);
        while let Some(t) = todo.pop() {
            if !seen.insert(t.uid()) {
                continue;
            }
            if vars_of.get(&t.uid()) == Some(&&c.vars) {
                return true;
            }
            todo.extend(subterms(t));
        }
        false
    };
    candidates
        .into_iter()
        .filter(|c| !has_sub_candidate(c))
        .collect()
}

/// Steps 3-6 of the module documentation, on the given candidates.
fn select_triggers(
    candidates: Vec<&Candidate>,
    bound: &BTreeSet<String>,
) -> Option<Vec<Vec<Term>>> {
    if candidates.is_empty() {
        return None;
    }
    let candidates = drop_bigger(drop_looping(candidates, bound));

    // Step 5: every candidate that covers all bound variables on its own is a
    // trigger. They are alternatives; the ground terms may contain only one of
    // the heads.
    let unary: Vec<Vec<Term>> = candidates
        .iter()
        .filter(|c| c.vars == *bound)
        .map(|c| vec![c.term.clone()])
        .collect();
    if !unary.is_empty() {
        return Some(unary);
    }

    // Step 6: one multi-pattern. Visit candidates with more variables first and
    // smaller ones first among those (a stable sort keeps the collection order
    // for ties), taking each one that covers a new variable.
    let mut ordered = candidates;
    ordered.sort_by(|a, b| b.vars.len().cmp(&a.vars.len()).then(a.size.cmp(&b.size)));
    let mut covered: BTreeSet<String> = BTreeSet::new();
    let mut chosen: Vec<&Candidate> = Vec::new();
    for candidate in ordered {
        if !candidate.vars.is_subset(&covered) {
            covered.extend(candidate.vars.iter().cloned());
            chosen.push(candidate);
            if covered == *bound {
                break;
            }
        }
    }
    if covered != *bound {
        // Some bound variable never occurs in a candidate: uncoverable.
        return None;
    }

    // Remove redundant members so the multi-pattern is inclusion-minimal.
    let mut idx = 0;
    while idx < chosen.len() {
        let covered_without_candidate: BTreeSet<String> = chosen
            .iter()
            .enumerate()
            .filter(|(other_idx, _)| *other_idx != idx)
            .flat_map(|(_, candidate)| candidate.vars.iter().cloned())
            .collect();
        if covered_without_candidate == *bound {
            chosen.remove(idx);
        } else {
            idx += 1;
        }
    }

    Some(vec![
        chosen
            .into_iter()
            .map(|candidate| candidate.term.clone())
            .collect(),
    ])
}

/// Infer a set of triggers (multi-patterns) for a quantifier body.
///
/// `body` is the (de-annotated) body term; `bound_names` are the names of the
/// quantifier's bound variables. `excluded` holds the terms named by any
/// `:no-pattern` annotations — anti-trigger hints that are only used when no
/// trigger exists without them (as in Z3). Returns a list of multi-patterns,
/// where each multi-pattern is a conjunctive list of trigger terms (matching
/// the `Vec<Vec<_>>` shape used by the rest of the solver): the outer list is
/// disjunctive (any multi-pattern may fire), the inner list conjunctive.
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
    collect_candidates(body, &bound, &BTreeSet::new(), &mut candidates);
    // Terms are hash-consed: keep the first occurrence of each.
    let mut seen = BTreeSet::new();
    candidates.retain(|c| seen.insert(c.term.uid()));

    // Step 2: `:no-pattern` terms are not used as triggers...
    let excluded: BTreeSet<String> = excluded.iter().map(|t| t.to_string()).collect();
    let allowed: Vec<&Candidate> = candidates
        .iter()
        .filter(|c| excluded.is_empty() || !excluded.contains(&c.term.to_string()))
        .collect();
    let some_excluded = allowed.len() < candidates.len();
    select_triggers(allowed, &bound).or_else(|| {
        // ...unless they are the only way to instantiate the quantifier. Z3 then
        // warns "ignoring nopats annotation because Z3 couldn't find any other
        // pattern" and uses them.
        if some_excluded {
            select_triggers(candidates.iter().collect(), &bound)
        } else {
            None
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use yaspar_ir::ast::{Context, Typecheck, alg};
    use yaspar_ir::untyped::UntypedAst;

    /// Parse `script`, take its last assertion (a quantifier), and return the
    /// printed triggers inferred for it, one string per multi-pattern.
    fn triggers_of(script: &str) -> Option<Vec<String>> {
        let commands = UntypedAst.parse_script_str(script).expect("parse failed");
        let mut context = Context::new();
        let typed = commands.type_check(&mut context).expect("typecheck failed");
        let quantifier = typed
            .iter()
            .rev()
            .find_map(|c| match c.repr() {
                alg::Command::Assert(t) => Some(t.clone()),
                _ => None,
            })
            .expect("no assertion");
        let (Forall(vars, body) | Exists(vars, body)) = quantifier.repr() else {
            panic!("last assertion is not a quantifier: {quantifier}");
        };
        let (body, excluded) = match body.repr() {
            Annotated(inner, attrs) => (
                inner.clone(),
                attrs
                    .iter()
                    .filter_map(|a| match a {
                        yaspar_ir::ast::Attribute::NoPattern(t) => Some(t.clone()),
                        _ => None,
                    })
                    .collect(),
            ),
            _ => (body.clone(), vec![]),
        };
        let names: Vec<String> = vars.iter().map(|v| v.0.get().clone()).collect();
        infer_triggers(&body, &names, &excluded).map(|mps| {
            mps.iter()
                .map(|mp| {
                    mp.iter()
                        .map(|t| t.to_string())
                        .collect::<Vec<_>>()
                        .join(" ")
                })
                .collect()
        })
    }

    #[test]
    fn every_minimal_single_trigger_is_kept() {
        let triggers = triggers_of(
            "(declare-sort T 0) (declare-fun P (T) Bool) (declare-fun Q (T) Bool)
             (assert (forall ((x T)) (and (P x) (Q x))))",
        );
        assert_eq!(triggers, Some(vec!["(P x)".into(), "(Q x)".into()]));
    }

    #[test]
    fn bigger_candidate_with_the_same_variables_is_dropped() {
        // (f (g x)) contains the candidate (g x), which has the same variables.
        let triggers = triggers_of(
            "(declare-fun f (Int) Int) (declare-fun g (Int) Int)
             (assert (forall ((x Int)) (> (f (g x)) 0)))",
        );
        assert_eq!(triggers, Some(vec!["(g x)".into()]));
    }

    #[test]
    fn looping_candidate_is_dropped() {
        // (f x) matches its own instance (f (g x)); Z3 keeps (g x) only.
        let triggers = triggers_of(
            "(declare-fun f (Int) Int) (declare-fun g (Int) Int)
             (assert (forall ((x Int)) (= (f x) (f (g x)))))",
        );
        assert_eq!(triggers, Some(vec!["(g x)".into()]));
    }

    #[test]
    fn multi_pattern_prefers_more_variables_then_smaller_terms() {
        // No single candidate covers {x, y}. (g x) comes first and (h y) adds y;
        // (k x) is never needed.
        let triggers = triggers_of(
            "(declare-sort T 0) (declare-fun g (T) Int) (declare-fun h (T) Int)
             (declare-fun k (T) Int)
             (assert (forall ((x T) (y T)) (= (+ (g x) (h y) (* 0 (k x))) 0)))",
        );
        assert_eq!(triggers, Some(vec!["(g x) (h y)".into()]));
    }

    #[test]
    fn ground_subterms_count_as_one_node() {
        // (Q (f (f (f c))) x) has size 3, not 6, so it is preferred over the
        // size-4 (P x d e).
        let triggers = triggers_of(
            "(declare-sort T 0) (declare-fun P (T T T) Bool) (declare-fun Q (T T) T)
             (declare-fun f (T) T) (declare-const c T) (declare-const d T) (declare-const e T)
             (assert (forall ((x T) (y T))
                (=> (and (P x d e) (P y d e)) (= (Q (f (f (f c))) x) (Q (f (f (f c))) y)))))",
        );
        assert_eq!(
            triggers,
            Some(vec!["(Q (f (f (f c))) x) (Q (f (f (f c))) y)".into()])
        );
    }

    #[test]
    fn candidates_are_collected_inside_nested_quantifiers() {
        // i occurs under an uninterpreted head only inside the nested forall.
        // (R o (h i)) mentions the nested variable o and is not a candidate.
        let triggers = triggers_of(
            "(declare-sort T 0) (declare-fun h (Int) T) (declare-fun R (T T) Bool)
             (assert (forall ((i Int)) (=> (<= 0 i)
                (forall ((o T)) (! (R o (h i)) :pattern ((R o (h i))))))))",
        );
        assert_eq!(triggers, Some(vec!["(h i)".into()]));
    }

    #[test]
    fn nested_variable_with_the_same_name_shadows_ours() {
        // Inside the nested forall, x is the nested variable: (p x) there is not
        // a candidate for the outer x, which has no trigger.
        let triggers = triggers_of(
            "(declare-fun p (Int) Bool)
             (assert (forall ((x Int)) (or (> x 0) (forall ((x Int)) (p x)))))",
        );
        assert_eq!(triggers, None);
    }

    #[test]
    fn no_pattern_terms_are_avoided_when_possible() {
        let triggers = triggers_of(
            "(declare-fun le (Int Int) Bool) (declare-fun q (Int) Bool)
             (assert (forall ((l Int)) (! (=> (le 0 l) (q l)) :no-pattern (le 0 l))))",
        );
        assert_eq!(triggers, Some(vec!["(q l)".into()]));
    }

    #[test]
    fn no_pattern_is_ignored_when_it_leaves_no_trigger() {
        let triggers = triggers_of(
            "(declare-fun le (Int Int) Bool) (declare-const c Bool)
             (assert (forall ((l Int)) (! (=> (le 0 l) c) :no-pattern (le 0 l))))",
        );
        assert_eq!(triggers, Some(vec!["(le 0 l)".into()]));
    }

    #[test]
    fn uncoverable_variable_has_no_trigger() {
        let triggers = triggers_of(
            "(declare-fun p (Int) Bool)
             (assert (forall ((x Int) (y Int)) (or (p x) (> y 0))))",
        );
        assert_eq!(triggers, None);
    }
}
