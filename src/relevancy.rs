// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Relevancy propagation for gating theory solver work.
//!
//! Implements the technique from de Moura & Bjørner (2007) / Z3 internals §7.1.4:
//! atoms are only sent to theory solvers when they are both assigned AND relevant.
//! Relevancy propagates structurally through the original formula tree:
//!   - OR-true  → one true child relevant
//!   - OR-false → all children relevant
//!   - AND-true → all children relevant
//!   - AND-false → one false child relevant
//!   - NOT → child relevant
//!   - IFF → both sides relevant
//!   - ITE-true → condition + then-branch relevant (or else if condition false)
//!   - ITE-false (¬ite) → condition + else-branch relevant (or then if condition false)
//!   - Atom → immediate Boolean sub-expression literals relevant

use std::collections::VecDeque;
use yaspar_ir::ast::ATerm;
use yaspar_ir::traits::Repr;

use crate::solver_state::SolverState;

#[derive(Debug, Clone)]
enum NodeKind {
    Or(Vec<i32>),
    And(Vec<i32>),
    Not(i32),
    Iff(i32, i32),
    Ite { cond: i32, then_lit: i32, else_lit: i32 },
    /// An atom: sub-expression literals that need relevancy for theory processing.
    Atom(Vec<i32>),
}

pub struct RelevancyState {
    node_kinds: Vec<Option<NodeKind>>,
    relevant: Vec<bool>,
    watches_on_true: Vec<Vec<i32>>,
    watches_on_false: Vec<Vec<i32>>,
    queue: VecDeque<i32>,
    trail: Vec<(usize, i32)>,
    enabled: bool,
}

impl RelevancyState {
    pub fn new(enabled: bool) -> Self {
        RelevancyState {
            node_kinds: Vec::new(),
            relevant: Vec::new(),
            watches_on_true: Vec::new(),
            watches_on_false: Vec::new(),
            queue: VecDeque::new(),
            trail: Vec::new(),
            enabled,
        }
    }

    pub fn is_enabled(&self) -> bool {
        self.enabled
    }

    fn ensure_capacity(&mut self, lit: i32) {
        let idx = lit.unsigned_abs() as usize;
        if idx >= self.relevant.len() {
            let new_len = (idx + 1).max(self.relevant.len() * 2).max(64);
            self.relevant.resize(new_len, false);
            self.watches_on_true.resize_with(new_len, Vec::new);
            self.watches_on_false.resize_with(new_len, Vec::new);
            self.node_kinds.resize_with(new_len, || None);
        }
    }

    /// Collect immediate sub-expression literals: descend until hitting a var_map
    /// entry (which has its own NodeKind and will propagate further on its own).
    fn collect_subterm_lits(term: &yaspar_ir::ast::Term, solver_state: &SolverState) -> Vec<i32> {
        let mut lits = Vec::new();
        let mut stack: Vec<&yaspar_ir::ast::Term> = Vec::new();
        // Push immediate children of the root (not the root itself)
        match term.repr() {
            ATerm::App(_, args, _) => {
                for arg in args {
                    stack.push(arg);
                }
            }
            ATerm::Not(child) => stack.push(child),
            ATerm::Or(children) | ATerm::And(children) => {
                for c in children {
                    stack.push(c);
                }
            }
            ATerm::Eq(a, b) => {
                stack.push(a);
                stack.push(b);
            }
            ATerm::Ite(c, t, e) => {
                stack.push(c);
                stack.push(t);
                stack.push(e);
            }
            _ => {}
        }
        let mut visited = std::collections::HashSet::new();
        while let Some(t) = stack.pop() {
            let uid = t.uid();
            if !visited.insert(uid) {
                continue;
            }
            if let Some(&lit) = solver_state.cnf_cache.var_map.get(&uid) {
                // Found a var_map entry — add it, don't recurse further
                lits.push(lit);
                continue;
            }
            // No var_map entry — recurse into children
            match t.repr() {
                ATerm::App(_, args, _) => {
                    for arg in args {
                        stack.push(arg);
                    }
                }
                ATerm::Not(child) => stack.push(child),
                ATerm::Or(children) | ATerm::And(children) => {
                    for c in children {
                        stack.push(c);
                    }
                }
                ATerm::Eq(a, b) => {
                    stack.push(a);
                    stack.push(b);
                }
                ATerm::Ite(c, t, e) => {
                    stack.push(c);
                    stack.push(t);
                    stack.push(e);
                }
                _ => {}
            }
        }
        lits
    }

    /// Pre-compute the formula structure for all terms in the CNF cache.
    pub fn initialize_structure(&mut self, solver_state: &SolverState) {
        if !self.enabled {
            return;
        }
        for (&uid, &lit) in solver_state.cnf_cache.var_map.iter() {
            let abs_lit = lit.unsigned_abs() as usize;
            self.ensure_capacity(lit);

            let term = solver_state.get_term(uid);
            let kind = match term.repr() {
                ATerm::Or(children) => {
                    let child_lits: Vec<i32> = children
                        .iter()
                        .filter_map(|c| solver_state.cnf_cache.var_map.get(&c.uid()).copied())
                        .collect();
                    if child_lits.is_empty() {
                        NodeKind::Atom(Self::collect_subterm_lits(&term, solver_state))
                    } else {
                        NodeKind::Or(child_lits)
                    }
                }
                ATerm::And(children) => {
                    let child_lits: Vec<i32> = children
                        .iter()
                        .filter_map(|c| solver_state.cnf_cache.var_map.get(&c.uid()).copied())
                        .collect();
                    if child_lits.is_empty() {
                        NodeKind::Atom(Self::collect_subterm_lits(&term, solver_state))
                    } else {
                        NodeKind::And(child_lits)
                    }
                }
                ATerm::Not(child) => {
                    // Not is redundant: relevant[abs(-x)] == relevant[abs(x)].
                    // Skip — the child term's structure at the same index handles propagation.
                    // Only store Atom if the child doesn't have its own var_map entry.
                    if solver_state.cnf_cache.var_map.get(&child.uid()).is_some() {
                        continue; // child has the same abs index, it'll store its own kind
                    }
                    NodeKind::Atom(Self::collect_subterm_lits(&term, solver_state))
                }
                ATerm::Eq(a, b) => {
                    let a_lit = solver_state.cnf_cache.var_map.get(&a.uid()).copied();
                    let b_lit = solver_state.cnf_cache.var_map.get(&b.uid()).copied();
                    if let (Some(al), Some(bl)) = (a_lit, b_lit) {
                        NodeKind::Iff(al, bl)
                    } else {
                        NodeKind::Atom(Self::collect_subterm_lits(&term, solver_state))
                    }
                }
                ATerm::Ite(c, t, e) => {
                    let c_lit = solver_state.cnf_cache.var_map.get(&c.uid()).copied();
                    let t_lit = solver_state.cnf_cache.var_map.get(&t.uid()).copied();
                    let e_lit = solver_state.cnf_cache.var_map.get(&e.uid()).copied();
                    if let (Some(cl), Some(tl), Some(el)) = (c_lit, t_lit, e_lit) {
                        NodeKind::Ite { cond: cl, then_lit: tl, else_lit: el }
                    } else {
                        NodeKind::Atom(Self::collect_subterm_lits(&term, solver_state))
                    }
                }
                _ => NodeKind::Atom(Self::collect_subterm_lits(&term, solver_state)),
            };
            if std::env::var("SUNDANCE_RELEVANCY_TRACE").is_ok() {
                let kind_name = match &kind {
                    NodeKind::Or(c) => format!("Or({})", c.len()),
                    NodeKind::And(c) => format!("And({})", c.len()),
                    NodeKind::Not(c) => format!("Not({})", c),
                    NodeKind::Iff(a, b) => format!("Iff({},{})", a, b),
                    NodeKind::Ite { cond, .. } => format!("Ite(cond={})", cond),
                    NodeKind::Atom(s) => format!("Atom(subs={:?})", s),
                };
                eprintln!("[relevancy] lit={} kind={} term={}", lit, kind_name, term);
            }
            self.node_kinds[abs_lit] = Some(kind);
        }
    }

    /// Classify a term into a NodeKind (extracted for reuse in lazy init).
    fn classify_term(&self, term: &yaspar_ir::ast::Term, solver_state: &SolverState) -> NodeKind {
        match term.repr() {
            ATerm::Or(children) => {
                let child_lits: Vec<i32> = children
                    .iter()
                    .filter_map(|c| solver_state.cnf_cache.var_map.get(&c.uid()).copied())
                    .collect();
                if child_lits.is_empty() {
                    NodeKind::Atom(Self::collect_subterm_lits(term, solver_state))
                } else {
                    NodeKind::Or(child_lits)
                }
            }
            ATerm::And(children) => {
                let child_lits: Vec<i32> = children
                    .iter()
                    .filter_map(|c| solver_state.cnf_cache.var_map.get(&c.uid()).copied())
                    .collect();
                if child_lits.is_empty() {
                    NodeKind::Atom(Self::collect_subterm_lits(term, solver_state))
                } else {
                    NodeKind::And(child_lits)
                }
            }
            ATerm::Not(child) => {
                if solver_state.cnf_cache.var_map.get(&child.uid()).is_some() {
                    // Not is redundant (same abs index as child) — return child's classification
                    return self.classify_term(child, solver_state);
                }
                NodeKind::Atom(Self::collect_subterm_lits(term, solver_state))
            }
            ATerm::Eq(a, b) => {
                let a_lit = solver_state.cnf_cache.var_map.get(&a.uid()).copied();
                let b_lit = solver_state.cnf_cache.var_map.get(&b.uid()).copied();
                if let (Some(al), Some(bl)) = (a_lit, b_lit) {
                    NodeKind::Iff(al, bl)
                } else {
                    NodeKind::Atom(Self::collect_subterm_lits(term, solver_state))
                }
            }
            ATerm::Ite(c, t, e) => {
                let c_lit = solver_state.cnf_cache.var_map.get(&c.uid()).copied();
                let t_lit = solver_state.cnf_cache.var_map.get(&t.uid()).copied();
                let e_lit = solver_state.cnf_cache.var_map.get(&e.uid()).copied();
                if let (Some(cl), Some(tl), Some(el)) = (c_lit, t_lit, e_lit) {
                    NodeKind::Ite { cond: cl, then_lit: tl, else_lit: el }
                } else {
                    NodeKind::Atom(Self::collect_subterm_lits(term, solver_state))
                }
            }
            _ => NodeKind::Atom(Self::collect_subterm_lits(term, solver_state)),
        }
    }

    pub fn is_relevant(&self, lit: i32) -> bool {
        if !self.enabled {
            return true;
        }
        let idx = lit.unsigned_abs() as usize;
        if idx >= self.relevant.len() {
            return false;
        }
        self.relevant[idx]
    }

    /// Lazily initialize a new literal as a relevant root. Called for
    /// theory-generated literals (datatype axioms, QI) that didn't exist
    /// at initialization time.
    pub fn ensure_known(&mut self, lit: i32, solver_state: &SolverState, level: usize, assignments: &[i32]) {
        if !self.enabled {
            return;
        }
        self.ensure_capacity(lit);
        let idx = lit.unsigned_abs() as usize;
        if self.node_kinds[idx].is_some() {
            return; // already known
        }
        // Classify structure from the term registry
        if let Some(&uid) = solver_state.cnf_cache.var_map_reverse.get(&(lit.abs())) {
            if !matches!(solver_state.get_term_safe(uid), crate::solver_types::TermOption::None) {
                let term = solver_state.get_term(uid);
                let kind = self.classify_term(&term, solver_state);
                self.node_kinds[idx] = Some(kind);
            } else {
                self.node_kinds[idx] = Some(NodeKind::Atom(vec![]));
            }
        } else {
            self.node_kinds[idx] = Some(NodeKind::Atom(vec![]));
        }
        // Mark as relevant root and propagate
        self.mark_relevant(lit, level);
        self.propagate(level, assignments);
    }

    fn mark_relevant(&mut self, lit: i32, level: usize) -> bool {
        self.ensure_capacity(lit);
        let idx = lit.unsigned_abs() as usize;
        if self.relevant[idx] {
            return false;
        }
        self.relevant[idx] = true;
        self.trail.push((level, lit));
        self.queue.push_back(lit);
        true
    }

    /// Mark root assertions as relevant. Called once at setup.
    pub fn mark_roots_relevant(&mut self, root_lits: &[i32]) {
        if !self.enabled {
            return;
        }
        for &lit in root_lits {
            self.mark_relevant(lit, 0);
        }
        self.propagate(0, &[]);
    }

    /// Called when a literal is assigned. Fires watches and propagates relevancy.
    /// Returns whether the literal is relevant.
    pub fn notify_assignment(&mut self, lit: i32, level: usize, assignments: &[i32]) -> bool {
        if !self.enabled {
            return true;
        }
        self.ensure_capacity(lit);
        let idx = lit.unsigned_abs() as usize;

        // Fire watches for this assignment
        let positive = lit > 0;
        let targets: Vec<i32> = if positive {
            self.watches_on_true[idx].clone()
        } else {
            self.watches_on_false[idx].clone()
        };
        for target_lit in targets {
            self.mark_relevant(target_lit, level);
        }

        // If this literal is relevant and has structure, propagate
        if self.relevant[idx] {
            self.propagate_node(idx, level, assignments);
        }

        self.propagate(level, assignments);
        self.relevant[idx]
    }

    fn propagate(&mut self, level: usize, assignments: &[i32]) {
        while let Some(lit) = self.queue.pop_front() {
            let idx = lit.unsigned_abs() as usize;
            self.propagate_node(idx, level, assignments);
        }
    }

    fn propagate_node(&mut self, idx: usize, level: usize, assignments: &[i32]) {
        if idx >= self.node_kinds.len() {
            return;
        }
        let kind = match self.node_kinds[idx].clone() {
            Some(k) => k,
            None => return,
        };
        match kind {
            NodeKind::Or(ref child_lits) => {
                match self.get_assignment_by_idx(idx, assignments) {
                    Some(true) => {
                        // OR true: one true child relevant.
                        // Check if any child is already relevant (from a prior watch).
                        let already_has_relevant = child_lits.iter().any(|&cl| {
                            let ci = cl.unsigned_abs() as usize;
                            ci < self.relevant.len() && self.relevant[ci]
                        });
                        if already_has_relevant {
                            // Already picked a branch — skip
                        } else {
                            let mut found = false;
                            for &child_lit in child_lits {
                                if self.lit_is_true(child_lit, assignments) {
                                    self.mark_relevant(child_lit, level);
                                    found = true;
                                    break;
                                }
                            }
                            if !found {
                                // Install watches: when a child becomes true, mark it relevant.
                                // Use idx (the Or node) as target so we re-check and pick only one.
                                for &child_lit in child_lits {
                                    self.install_true_watch(child_lit, idx as i32);
                                }
                            }
                        }
                    }
                    Some(false) => {
                        // OR false: all children relevant
                        for &child_lit in child_lits {
                            self.mark_relevant(child_lit, level);
                        }
                    }
                    None => {}
                }
            }
            NodeKind::And(ref child_lits) => {
                match self.get_assignment_by_idx(idx, assignments) {
                    Some(true) => {
                        // AND true: all children relevant
                        for &child_lit in child_lits {
                            self.mark_relevant(child_lit, level);
                        }
                    }
                    Some(false) => {
                        // AND false: one false child relevant
                        let mut found = false;
                        for &child_lit in child_lits {
                            if self.lit_is_false(child_lit, assignments) {
                                self.mark_relevant(child_lit, level);
                                found = true;
                                break;
                            }
                        }
                        if !found {
                            for &child_lit in child_lits {
                                self.install_false_watch(child_lit, child_lit);
                            }
                        }
                    }
                    None => {}
                }
            }
            NodeKind::Not(child_lit) => {
                self.mark_relevant(child_lit, level);
            }
            NodeKind::Iff(a_lit, b_lit) => {
                // Both sides always relevant
                self.mark_relevant(a_lit, level);
                self.mark_relevant(b_lit, level);
            }
            NodeKind::Ite { cond, then_lit, else_lit } => {
                // Condition always relevant
                self.mark_relevant(cond, level);
                let ite_val = self.get_assignment_by_idx(idx, assignments);
                let cond_val = self.lit_is_true(cond, assignments);
                let cond_false = self.lit_is_false(cond, assignments);
                match ite_val {
                    Some(true) => {
                        // ite true: if cond=true → then relevant; if cond=false → else relevant
                        if cond_val {
                            self.mark_relevant(then_lit, level);
                        } else if cond_false {
                            self.mark_relevant(else_lit, level);
                        } else {
                            self.install_true_watch(cond, then_lit);
                            self.install_false_watch(cond, else_lit);
                        }
                    }
                    Some(false) => {
                        // ¬ite: if cond=true → else relevant; if cond=false → then relevant
                        if cond_val {
                            self.mark_relevant(else_lit, level);
                        } else if cond_false {
                            self.mark_relevant(then_lit, level);
                        } else {
                            self.install_true_watch(cond, else_lit);
                            self.install_false_watch(cond, then_lit);
                        }
                    }
                    None => {
                        // ITE relevant but unassigned — wait for assignment
                        // Install watches on self
                        self.install_true_watch(idx as i32, idx as i32);
                        self.install_false_watch(idx as i32, idx as i32);
                    }
                }
            }
            NodeKind::Atom(ref subterm_lits) => {
                for &sub_lit in subterm_lits {
                    self.mark_relevant(sub_lit, level);
                }
            }
        }
    }

    /// Install a watch: when `watched_lit` becomes true, mark `target` relevant.
    fn install_true_watch(&mut self, watched_lit: i32, target: i32) {
        self.ensure_capacity(watched_lit);
        let idx = watched_lit.unsigned_abs() as usize;
        if watched_lit > 0 {
            self.watches_on_true[idx].push(target);
        } else {
            self.watches_on_false[idx].push(target);
        }
    }

    /// Install a watch: when `watched_lit` becomes false, mark `target` relevant.
    fn install_false_watch(&mut self, watched_lit: i32, target: i32) {
        self.ensure_capacity(watched_lit);
        let idx = watched_lit.unsigned_abs() as usize;
        if watched_lit > 0 {
            self.watches_on_false[idx].push(target);
        } else {
            self.watches_on_true[idx].push(target);
        }
    }

    fn get_assignment_by_idx(&self, idx: usize, assignments: &[i32]) -> Option<bool> {
        if idx >= assignments.len() {
            return None;
        }
        let val = assignments[idx];
        if val == 0 { None } else { Some(val > 0) }
    }

    fn lit_is_true(&self, lit: i32, assignments: &[i32]) -> bool {
        let idx = lit.unsigned_abs() as usize;
        if idx >= assignments.len() { return false; }
        let val = assignments[idx];
        if val == 0 { return false; }
        (val > 0) == (lit > 0)
    }

    fn lit_is_false(&self, lit: i32, assignments: &[i32]) -> bool {
        let idx = lit.unsigned_abs() as usize;
        if idx >= assignments.len() { return false; }
        let val = assignments[idx];
        if val == 0 { return false; }
        (val > 0) != (lit > 0)
    }

    /// Backtrack: undo relevancy marks added above the given level.
    pub fn backtrack_to(&mut self, level: usize) {
        if !self.enabled {
            return;
        }
        while let Some(&(mark_level, lit)) = self.trail.last() {
            if mark_level <= level {
                break;
            }
            self.trail.pop();
            let idx = lit.unsigned_abs() as usize;
            self.relevant[idx] = false;
        }
        self.queue.clear();
    }
}
