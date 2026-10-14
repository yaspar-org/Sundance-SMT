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
pub(crate) struct LetSharer<'a> {
    context: &'a mut Context,
    regions: HashMap<u64, Term>,
}

/// The children of `t` that belong to the same region as `t`. Binder bodies start regions of
/// their own, and attributes are printed unchanged.
fn region_children(t: &Term) -> Vec<&Term> {
    match t.repr() {
        ATerm::Let(..) | ATerm::Exists(..) | ATerm::Forall(..) => vec![],
        ATerm::Annotated(a, _) | ATerm::Matching(a, _) => vec![a],
        r => r.sub_terms().collect(),
    }
}

impl<'a> LetSharer<'a> {
    pub fn new(context: &'a mut Context) -> Self {
        Self {
            context,
            regions: HashMap::new(),
        }
    }

    /// Returns `root` with `let` bindings for the repeated compound subterms of its region.
    pub fn share(&mut self, root: &Term) -> Term {
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

        // Rebuild bottom-up. A shared subterm (referenced more than once, and not smaller than
        // MIN_SHARED_SIZE nodes, which leaves out atoms) is bound one level above the deepest
        // binding it mentions, and replaced by its variable where it is used.
        let mut size: HashMap<u64, u64> = HashMap::new();
        let mut depth: HashMap<u64, usize> = HashMap::new();
        let mut uses: HashMap<u64, Term> = HashMap::new();
        let mut levels: Vec<Vec<VarBinding<_, Term>>> = vec![];
        for t in &order {
            let children = region_children(t);
            let s = children
                .iter()
                .fold(1u64, |acc, c| acc.saturating_add(size[&c.uid()]));
            let level = children.iter().map(|c| depth[&c.uid()]).max().unwrap_or(0);
            let shared = t.uid() != root.uid() && s >= MIN_SHARED_SIZE && refs[&t.uid()] > 1;
            size.insert(t.uid(), s);
            depth.insert(t.uid(), level + usize::from(shared));
            // A term is rebuilt only when one of its children changed, or when it is a binder,
            // whose body is a region of its own
            let changed = matches!(
                t.repr(),
                ATerm::Exists(..) | ATerm::Forall(..) | ATerm::Matching(..)
            ) || children.iter().any(|c| uses[&c.uid()].uid() != c.uid());
            let mut rebuilt = if changed {
                self.rebuild(t, &uses)
            } else {
                t.clone()
            };
            if shared {
                let sort = t.get_sort(self.context);
                let id = self.context.arena().new_local();
                let symbol = self.context.arena().fresh_x();
                if levels.len() <= level {
                    levels.resize_with(level + 1, Vec::new);
                }
                levels[level].push(VarBinding(symbol.clone(), id, rebuilt));
                rebuilt = self.context.arena().local(Local { id, symbol, sort });
            }
            uses.insert(t.uid(), rebuilt);
        }
        // The root comes last in post-order, and every level below the top one is non-empty
        let body = uses
            .remove(&root.uid())
            .expect("the root is part of its region");
        let result = levels.into_iter().rev().fold(body, |body, bindings| {
            self.context.arena().let_term(bindings, body)
        });
        self.regions.insert(root.uid(), result.clone());
        result
    }

    /// The body of a binder: its own region, inside the annotation if it has one.
    fn binder_body(&mut self, body: &Term) -> Term {
        if let ATerm::Annotated(inner, attributes) = body.repr() {
            let inner = self.share(inner);
            self.context.arena().annotated(inner, attributes.clone())
        } else {
            self.share(body)
        }
    }

    /// Rebuilds `t` from the rewritten versions of its region children in `uses`.
    fn rebuild(&mut self, t: &Term, uses: &HashMap<u64, Term>) -> Term {
        let u = |c: &Term| uses[&c.uid()].clone();
        let us = |cs: &[Term]| cs.iter().map(u).collect::<Vec<_>>();
        match t.repr() {
            ATerm::Constant(..) | ATerm::Global(..) | ATerm::Local(..) | ATerm::Let(..) => {
                t.clone()
            }
            ATerm::App(id, ts, sort) => self.context.arena().app(id.clone(), us(ts), sort.clone()),
            ATerm::Distinct(ts) => self.context.arena().distinct(us(ts)),
            ATerm::And(ts) => self.context.arena().and(us(ts)),
            ATerm::Or(ts) => self.context.arena().or(us(ts)),
            ATerm::Xor(ts) => self.context.arena().xor(us(ts)),
            ATerm::Eq(a, b) => self.context.arena().eq(u(a), u(b)),
            ATerm::Not(a) => self.context.arena().not(u(a)),
            ATerm::Implies(ts, b) => self.context.arena().implies(us(ts), u(b)),
            ATerm::Ite(b, x, y) => self.context.arena().ite(u(b), u(x), u(y)),
            ATerm::Annotated(a, attributes) => {
                self.context.arena().annotated(u(a), attributes.clone())
            }
            ATerm::Matching(scrutinee, arms) => {
                let scrutinee = u(scrutinee);
                let arms = arms
                    .iter()
                    .map(|arm| PatternArm {
                        pattern: arm.pattern.clone(),
                        body: self.share(&arm.body),
                    })
                    .collect();
                self.context.arena().matching(scrutinee, arms)
            }
            ATerm::Exists(vs, body) => {
                let body = self.binder_body(body);
                self.context.arena().exists(vs.clone(), body)
            }
            ATerm::Forall(vs, body) => {
                let body = self.binder_body(body);
                self.context.arena().forall(vs.clone(), body)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use yaspar_ir::ast::{ACommand, LetElim, Typecheck};
    use yaspar_ir::untyped::UntypedAst;

    const DECLS: &str = "(declare-sort S 0) (declare-fun f (S S) S) (declare-fun p (S) Bool) \
                         (declare-const a S) (declare-const b S)";

    /// Asserts `body` after `DECLS` and returns the context, the assertion let-eliminated as the
    /// solver sees it, and that term with its repeated subterms shared.
    fn share(body: &str) -> (Context, Term, Term) {
        let mut context = Context::new();
        let commands = UntypedAst
            .parse_script_str(&format!("{DECLS} (assert {body})"))
            .unwrap()
            .type_check(&mut context)
            .unwrap();
        let ACommand::Assert(term) = commands.last().unwrap().repr() else {
            panic!("the script ends with its assertion");
        };
        let term = term.let_elim(&mut context);
        let shared = LetSharer::new(&mut context).share(&term);
        (context, term, shared)
    }

    fn printed(body: &str) -> String {
        share(body).2.to_string()
    }

    #[test]
    fn binds_repeated_subterms_once() {
        assert_eq!(
            printed("(p (f (f a b) (f a b)))"),
            "(let ((x-0 (f a b))) (p (f x-0 x-0)))"
        );
    }

    #[test]
    fn leaves_small_and_single_subterms_in_place() {
        assert_eq!(
            printed("(and (p a) (p a) (p (f a b)))"),
            "(and (p a) (p a) (p (f a b)))"
        );
    }

    #[test]
    fn levels_bindings_by_dependency() {
        assert_eq!(
            printed("(let ((u (f a b))) (let ((v (f u u))) (= (f v v) (f v a))))"),
            "(let ((x-0 (f a b))) (let ((x-1 (f x-0 x-0))) (= (f x-1 x-1) (f x-1 a))))"
        );
    }

    #[test]
    fn binds_inside_quantifiers_and_keeps_patterns_on_top() {
        assert_eq!(
            printed("(forall ((x S)) (! (p (f (f x a) (f x a))) :pattern ((p x))))"),
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
            let (mut context, term, shared) = share(body);
            assert_eq!(shared.let_elim(&mut context), term, "{body}");
        }
    }
}
