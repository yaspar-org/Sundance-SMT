// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Rewrites proof terms so that repeated subterms are printed once, through `let`.
//!
//! Terms are hash-consed, so a subterm that occurs many times is stored once, but `Display`
//! prints it at every occurrence. On some inputs the printed tree is orders of magnitude larger
//! than the term: F* queries let-bind subterms and use them several times, and let-elimination
//! turns that into a DAG that prints exponentially. [`LetSharer`] rebuilds a term so that every
//! compound subterm referenced more than once is bound by a `let` and printed once.
//!
//! Bindings are introduced per *region*: the term itself, and the body of every binder in it
//! (quantifiers and `match` arms). A region does not look inside the binders it contains, so a
//! binding never leaves the scope of the variables it mentions. A quantifier's annotation stays
//! directly under the quantifier, with the bindings inside it, and its attributes (patterns) are
//! printed as they are. Bindings are grouped in levels, so a `let` only refers to bindings of
//! earlier, enclosing levels.

use std::collections::{HashMap, HashSet};
use yaspar_ir::ast::alg::VarBinding;
use yaspar_ir::ast::{
    ATerm, Context, FetchSort, FreshVar, HasArena, Local, LocalVarAllocator, PatternArm, Repr,
    Term, TermAllocator,
};

/// Subterms smaller than this many nodes are printed in place even when repeated, since a
/// binding and its references would not be shorter.
const MIN_SHARED_SIZE: u64 = 3;

/// Introduces `let` bindings for repeated subterms. Results are cached by term, so the same
/// subterm is rewritten once across all the literals of a proof.
#[derive(Default)]
pub(crate) struct LetSharer {
    regions: HashMap<u64, Term>,
}

/// The children of `t` that belong to the same region as `t`. Binder bodies start regions of
/// their own, and attributes are printed unchanged.
fn region_children(t: &Term) -> Vec<&Term> {
    match t.repr() {
        ATerm::Constant(..)
        | ATerm::Global(..)
        | ATerm::Local(..)
        | ATerm::Let(..)
        | ATerm::Exists(..)
        | ATerm::Forall(..) => vec![],
        ATerm::App(_, ts, _)
        | ATerm::Distinct(ts)
        | ATerm::And(ts)
        | ATerm::Or(ts)
        | ATerm::Xor(ts) => ts.iter().collect(),
        ATerm::Eq(a, b) => vec![a, b],
        ATerm::Not(a) | ATerm::Annotated(a, _) | ATerm::Matching(a, _) => vec![a],
        ATerm::Implies(ts, t) => ts.iter().chain(std::iter::once(t)).collect(),
        ATerm::Ite(b, t, e) => vec![b, t, e],
    }
}

fn is_compound(t: &Term) -> bool {
    !matches!(
        t.repr(),
        ATerm::Constant(..) | ATerm::Global(..) | ATerm::Local(..)
    )
}

impl LetSharer {
    /// Returns `term` with `let` bindings for its repeated compound subterms.
    pub fn share(&mut self, term: &Term, context: &mut Context) -> Term {
        self.region(term, context)
    }

    /// Rewrites the region rooted at `root`.
    fn region(&mut self, root: &Term, context: &mut Context) -> Term {
        if let Some(done) = self.regions.get(&root.uid()) {
            return done.clone();
        }

        // Post-order over the region, counting how often each subterm is referenced in it
        let mut order: Vec<Term> = vec![];
        let mut refs: HashMap<u64, usize> = HashMap::new();
        let mut visited: HashSet<u64> = HashSet::new();
        let mut stack: Vec<(Term, bool)> = vec![(root.clone(), false)];
        while let Some((t, expanded)) = stack.pop() {
            if expanded {
                order.push(t);
                continue;
            }
            if !visited.insert(t.uid()) {
                continue;
            }
            stack.push((t.clone(), true));
            for c in region_children(&t) {
                *refs.entry(c.uid()).or_default() += 1;
                if !visited.contains(&c.uid()) {
                    stack.push((c.clone(), false));
                }
            }
        }

        // Tree size (capped), whether a subterm is shared, and the binding level it needs:
        // one more than the deepest shared subterm it mentions
        let mut size: HashMap<u64, u64> = HashMap::new();
        let mut level: HashMap<u64, usize> = HashMap::new();
        let mut shared: HashSet<u64> = HashSet::new();
        for t in &order {
            let children = region_children(t);
            let s = children
                .iter()
                .fold(1u64, |acc, c| acc.saturating_add(size[&c.uid()]));
            size.insert(t.uid(), s);
            let need = children
                .iter()
                .map(|c| level[&c.uid()] + usize::from(shared.contains(&c.uid())))
                .max()
                .unwrap_or(0);
            level.insert(t.uid(), need);
            if t.uid() != root.uid()
                && refs.get(&t.uid()).copied().unwrap_or(0) > 1
                && is_compound(t)
                && s >= MIN_SHARED_SIZE
            {
                shared.insert(t.uid());
            }
        }

        // Rebuild bottom-up; a shared subterm is replaced by its variable where it is used
        let mut uses: HashMap<u64, Term> = HashMap::new();
        let mut levels: Vec<Vec<VarBinding<_, Term>>> = vec![];
        let mut body = None;
        for t in &order {
            let rebuilt = self.rebuild(t, &uses, context);
            if t.uid() == root.uid() {
                body = Some(rebuilt);
            } else if shared.contains(&t.uid()) {
                let sort = t.get_sort(context);
                let id = context.arena().new_local();
                let symbol = context.arena().fresh_x();
                let lvl = level[&t.uid()];
                if levels.len() <= lvl {
                    levels.resize_with(lvl + 1, Vec::new);
                }
                levels[lvl].push(VarBinding(symbol.clone(), id, rebuilt));
                let var = context.arena().local(Local { id, symbol, sort });
                uses.insert(t.uid(), var);
            } else {
                uses.insert(t.uid(), rebuilt);
            }
        }
        let mut result = body.expect("the root is part of its region");
        for bindings in levels.into_iter().rev() {
            if !bindings.is_empty() {
                result = context.arena().let_term(bindings, result);
            }
        }
        self.regions.insert(root.uid(), result.clone());
        result
    }

    /// The body of a binder: its own region, inside the annotation if it has one.
    fn binder_body(&mut self, body: &Term, context: &mut Context) -> Term {
        if let ATerm::Annotated(inner, attributes) = body.repr() {
            let inner = self.region(inner, context);
            context.arena().annotated(inner, attributes.clone())
        } else {
            self.region(body, context)
        }
    }

    /// Rebuilds `t` from the rewritten versions of its region children in `uses`.
    fn rebuild(&mut self, t: &Term, uses: &HashMap<u64, Term>, context: &mut Context) -> Term {
        let u = |c: &Term| uses[&c.uid()].clone();
        let us = |cs: &[Term]| cs.iter().map(u).collect::<Vec<_>>();
        match t.repr() {
            ATerm::Constant(..) | ATerm::Global(..) | ATerm::Local(..) | ATerm::Let(..) => {
                t.clone()
            }
            ATerm::App(id, ts, sort) => context.arena().app(id.clone(), us(ts), sort.clone()),
            ATerm::Distinct(ts) => context.arena().distinct(us(ts)),
            ATerm::And(ts) => context.arena().and(us(ts)),
            ATerm::Or(ts) => context.arena().or(us(ts)),
            ATerm::Xor(ts) => context.arena().xor(us(ts)),
            ATerm::Eq(a, b) => context.arena().eq(u(a), u(b)),
            ATerm::Not(a) => context.arena().not(u(a)),
            ATerm::Implies(ts, b) => context.arena().implies(us(ts), u(b)),
            ATerm::Ite(b, x, y) => context.arena().ite(u(b), u(x), u(y)),
            ATerm::Annotated(a, attributes) => context.arena().annotated(u(a), attributes.clone()),
            ATerm::Matching(scrutinee, arms) => {
                let scrutinee = u(scrutinee);
                let arms = arms
                    .iter()
                    .map(|arm| PatternArm {
                        pattern: arm.pattern.clone(),
                        body: self.region(&arm.body, context),
                    })
                    .collect();
                context.arena().matching(scrutinee, arms)
            }
            ATerm::Exists(vs, body) => {
                let body = self.binder_body(body, context);
                context.arena().exists(vs.clone(), body)
            }
            ATerm::Forall(vs, body) => {
                let body = self.binder_body(body, context);
                context.arena().forall(vs.clone(), body)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use yaspar_ir::ast::{ACommand, LetElim, Typecheck};
    use yaspar_ir::untyped::UntypedAst;

    /// Parses `script` and returns its context and its last assertion, let-eliminated as the
    /// solver sees it.
    fn last_assertion(script: &str) -> (Context, Term) {
        let mut context = Context::new();
        let commands = UntypedAst
            .parse_script_str(script)
            .unwrap()
            .type_check(&mut context)
            .unwrap();
        let term = commands
            .iter()
            .filter_map(|c| match c.repr() {
                ACommand::Assert(t) => Some(t.clone()),
                _ => None,
            })
            .next_back()
            .unwrap();
        let term = term.let_elim(&mut context);
        (context, term)
    }

    fn shared(script: &str) -> (String, Term, Term, Context) {
        let (mut context, term) = last_assertion(script);
        let out = LetSharer::default().share(&term, &mut context);
        (out.to_string(), term, out, context)
    }

    const DECLS: &str = "(declare-sort S 0) (declare-fun f (S S) S) (declare-fun p (S) Bool) \
                         (declare-const a S) (declare-const b S)";

    #[test]
    fn binds_repeated_subterms_once() {
        let (printed, ..) = shared(&format!("{DECLS} (assert (p (f (f a b) (f a b))))"));
        assert_eq!(printed, "(let ((x-0 (f a b))) (p (f x-0 x-0)))");
    }

    #[test]
    fn leaves_small_and_single_subterms_in_place() {
        let (printed, ..) = shared(&format!("{DECLS} (assert (and (p a) (p a) (p (f a b))))"));
        assert_eq!(printed, "(and (p a) (p a) (p (f a b)))");
    }

    #[test]
    fn levels_bindings_by_dependency() {
        let (printed, ..) = shared(&format!(
            "{DECLS} (assert (let ((u (f a b))) (let ((v (f u u))) (= (f v v) (f v a)))))"
        ));
        assert_eq!(
            printed,
            "(let ((x-0 (f a b))) (let ((x-1 (f x-0 x-0))) (= (f x-1 x-1) (f x-1 a))))"
        );
    }

    #[test]
    fn binds_inside_quantifiers_and_keeps_patterns_on_top() {
        let (printed, ..) = shared(&format!(
            "{DECLS} (assert (forall ((x S)) (! (p (f (f x a) (f x a))) :pattern ((p x)))))"
        ));
        assert_eq!(
            printed,
            "(forall ((x S)) (! (let ((x-0 (f x a))) (p (f x-0 x-0))) :pattern ((p x))))"
        );
    }

    #[test]
    fn expanding_the_lets_gives_back_the_term() {
        for body in [
            "(p (f (f a b) (f a b)))",
            "(let ((u (f a b))) (let ((v (f u u))) (= (f v v) (f v a))))",
            "(forall ((x S)) (! (and (p (f (f x a) (f x a))) (p (f a b)) (p (f a b))) \
             :pattern ((p x))))",
            "(exists ((x S)) (or (p (f x x)) (forall ((y S)) (= (f (f x y) (f x y)) (f x y)))))",
        ] {
            let (_, term, out, mut context) = shared(&format!("{DECLS} (assert {body})"));
            assert_eq!(out.let_elim(&mut context), term, "{body}");
        }
    }
}
