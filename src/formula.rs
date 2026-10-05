// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Boolean structure of the input assertions, for the formula tableau.
//!
//! The builder runs on the let-eliminated assertions (no NNF, no CNF) and
//! only in formula positions. Connectives become nodes; everything else is an
//! atom with a SAT literal, registered with the egraph exactly as the CNF path
//! registers it.

use crate::solver_state::SolverState;
use std::collections::HashMap;
use yaspar_ir::ast::alg::CheckIdentifier;
use yaspar_ir::ast::{
    AConstant, ATerm, FetchSort, IdentifierKind, ObjectAllocatorExt, Term, TermAllocator,
};
use yaspar_ir::traits::Repr;

pub type NodeId = u32;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Node {
    /// An atom's SAT literal
    Lit(i32),
    Not(NodeId),
    And(Vec<NodeId>),
    Or(Vec<NodeId>),
    Ite(NodeId, NodeId, NodeId),
    Iff(NodeId, NodeId),
}

/// Formula DAG of the assertions and of quantifier instance bodies.
/// Children precede their parents.
#[derive(Default)]
pub struct FormulaStore {
    pub nodes: Vec<Node>,
    /// Per node: its literal. Connectives own a fresh variable without a
    /// `var_map` entry, so the propagator never observes it.
    pub lits: Vec<i32>,
    /// Connective variable -> node
    pub node_of_var: HashMap<i32, NodeId>,
    pub roots: Vec<NodeId>,
    /// Atom terms in creation order, for theory preprocessing
    pub atoms: Vec<Term>,
    /// Unit clauses fixing the Boolean constants
    pub units: Vec<i32>,
    memo: HashMap<u64, NodeId>,
    /// Whether atoms being built come from a quantifier instance
    from_quantifier: bool,
}

impl FormulaStore {
    pub fn add_assertion(&mut self, term: &Term, s: &mut SolverState) {
        let root = self.build_formula(term, s, false);
        self.roots.push(root);
    }

    /// Build the formula `term`, sharing nodes with everything built before
    pub fn build_formula(
        &mut self,
        term: &Term,
        s: &mut SolverState,
        from_quantifier: bool,
    ) -> NodeId {
        self.from_quantifier = from_quantifier;
        self.build(term, s)
    }

    pub fn lit(&self, n: NodeId) -> i32 {
        self.lits[n as usize]
    }

    /// Append a node, taking a fresh variable for a connective
    pub fn add_node(&mut self, node: Node, next_var: &mut i32) -> NodeId {
        let lit = match &node {
            Node::Lit(l) => *l,
            Node::Not(c) => -self.lits[*c as usize],
            _ => {
                *next_var += 1;
                *next_var - 1
            }
        };
        let id = self.nodes.len() as NodeId;
        if !matches!(node, Node::Lit(_) | Node::Not(_)) {
            self.node_of_var.insert(lit, id);
        }
        self.nodes.push(node);
        self.lits.push(lit);
        id
    }

    fn push(&mut self, node: Node, s: &mut SolverState) -> NodeId {
        self.add_node(node, &mut s.cnf_cache.next_var)
    }

    fn not(&mut self, n: NodeId, s: &mut SolverState) -> NodeId {
        self.push(Node::Not(n), s)
    }

    fn constant(&mut self, b: bool, s: &mut SolverState) -> NodeId {
        let t = if b {
            s.context.get_true()
        } else {
            s.context.get_false()
        };
        self.build(&t, s)
    }

    fn is_bool(t: &Term, s: &mut SolverState) -> bool {
        let bool_sort = s.context.bool_sort();
        t.get_sort(&mut s.context) == bool_sort
    }

    fn build(&mut self, term: &Term, s: &mut SolverState) -> NodeId {
        if let Some(&n) = self.memo.get(&term.uid()) {
            return n;
        }
        let n = match term.repr() {
            ATerm::Annotated(t, _) => self.build(t, s),
            ATerm::Not(t) => {
                let c = self.build(t, s);
                self.not(c, s)
            }
            ATerm::And(ts) | ATerm::Or(ts) => {
                let is_and = matches!(term.repr(), ATerm::And(_));
                match ts.len() {
                    0 => self.constant(is_and, s),
                    1 => self.build(&ts[0], s),
                    _ => {
                        let cs = ts.iter().map(|t| self.build(t, s)).collect();
                        self.push(if is_and { Node::And(cs) } else { Node::Or(cs) }, s)
                    }
                }
            }
            ATerm::Implies(ts, b) => {
                // `(=> a1 ... an b)` is `(or (not a1) ... (not an) b)`
                let mut cs: Vec<NodeId> = ts
                    .iter()
                    .map(|t| {
                        let c = self.build(t, s);
                        self.not(c, s)
                    })
                    .collect();
                cs.push(self.build(b, s));
                self.push(Node::Or(cs), s)
            }
            ATerm::Ite(c, t, e) => {
                let (c, t, e) = (self.build(c, s), self.build(t, s), self.build(e, s));
                self.push(Node::Ite(c, t, e), s)
            }
            ATerm::Xor(ts) => {
                // `(xor a b)` is `(not (= a b))`, folded left
                let mut acc = self.build(&ts[0], s);
                for t in &ts[1..] {
                    let b = self.build(t, s);
                    let iff = self.push(Node::Iff(acc, b), s);
                    acc = self.not(iff, s);
                }
                acc
            }
            ATerm::Eq(a, b) if Self::is_bool(a, s) => {
                let (a, b) = (self.build(a, s), self.build(b, s));
                self.push(Node::Iff(a, b), s)
            }
            ATerm::Distinct(ts) if Self::is_bool(&ts[0], s) => match ts.len() {
                0 | 1 => self.constant(true, s),
                2 => {
                    let (a, b) = (self.build(&ts[0], s), self.build(&ts[1], s));
                    let iff = self.push(Node::Iff(a, b), s);
                    self.not(iff, s)
                }
                // more than two distinct Booleans are impossible
                _ => self.constant(false, s),
            },
            ATerm::App(f, args, _)
                if args.len() > 2
                    && matches!(
                        f.get_kind(),
                        Some(
                            IdentifierKind::Lt
                                | IdentifierKind::Le
                                | IdentifierKind::Gt
                                | IdentifierKind::Ge
                        )
                    ) =>
            {
                // The arithmetic frontends only understand binary comparisons.
                let bool_sort = s.context.bool_sort();
                let pairs: Vec<Term> = args
                    .windows(2)
                    .map(|w| {
                        s.context
                            .app(f.clone(), w.to_vec(), Some(bool_sort.clone()))
                    })
                    .collect();
                let cs = pairs.iter().map(|t| self.build(t, s)).collect();
                self.push(Node::And(cs), s)
            }
            ATerm::Constant(AConstant::Bool(b), _) => {
                let n = self.atom(term, s);
                let Node::Lit(lit) = self.nodes[n as usize] else {
                    unreachable!()
                };
                self.units.push(if *b { lit } else { -lit });
                n
            }
            _ => self.atom(term, s),
        };
        self.memo.insert(term.uid(), n);
        n
    }

    fn atom(&mut self, term: &Term, s: &mut SolverState) -> NodeId {
        s.insert_predecessor(term, None, None, self.from_quantifier);
        let lit = s.get_or_allocate_lit_for_term(term);
        self.atoms.push(term.clone());
        self.push(Node::Lit(lit), s)
    }
}
