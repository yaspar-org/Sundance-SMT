// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Relevancy propagation for gating theory solver work.
//!
//! Implements the technique from de Moura & Bjørner (2007) / Z3 internals §7.1.4:
//! atoms are only sent to theory solvers when they are both assigned AND relevant.
//! Relevancy propagates structurally through the ORIGINAL (pre-NNF) formula tree:
//!   - OR-true  → one true child relevant
//!   - OR-false → all children relevant
//!   - AND-true → all children relevant
//!   - AND-false → one false child relevant
//!   - NOT → child relevant
//!   - IFF (Eq on booleans) → both sides relevant
//!   - ITE-true → condition + then-branch relevant (or else if condition false)
//!   - ITE-false (¬ite) → condition + swapped branch
//!   - Atom → immediate Boolean sub-expression literals relevant

use std::collections::VecDeque;
use yaspar_ir::ast::{ATerm, Term};
use yaspar_ir::traits::Repr;

use crate::solver_state::SolverState;

#[derive(Debug, Clone)]
enum NodeKind {
    Or(Vec<i32>),
    And(Vec<i32>),
    Not(i32),
    Iff(i32, i32),
    Ite { cond: i32, then_lit: i32, else_lit: i32 },
    Atom(Vec<i32>),
}

pub struct RelevancyState {
    node_kinds: Vec<Option<NodeKind>>,
    relevant: Vec<bool>,
    /// Per-node flag: this Or/And has already chosen its single relevant branch.
    branch_chosen: Vec<bool>,
    watches_on_true: Vec<Vec<i32>>,
    watches_on_false: Vec<Vec<i32>>,
    cond_watches_on_true: Vec<Vec<usize>>,
    cond_watches_on_false: Vec<Vec<usize>>,
    queue: VecDeque<i32>,
    trail: Vec<(usize, i32)>,
    /// Records (level, node_idx) when branch_chosen[node_idx] was set.
    branch_trail: Vec<(usize, usize)>,
    enabled: bool,
}

impl RelevancyState {
    pub fn new(enabled: bool) -> Self {
        RelevancyState {
            node_kinds: Vec::new(),
            relevant: Vec::new(),
            branch_chosen: Vec::new(),
            watches_on_true: Vec::new(),
            watches_on_false: Vec::new(),
            cond_watches_on_true: Vec::new(),
            cond_watches_on_false: Vec::new(),
            queue: VecDeque::new(),
            trail: Vec::new(),
            branch_trail: Vec::new(),
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
            self.branch_chosen.resize(new_len, false);
            self.watches_on_true.resize_with(new_len, Vec::new);
            self.watches_on_false.resize_with(new_len, Vec::new);
            self.cond_watches_on_true.resize_with(new_len, Vec::new);
            self.cond_watches_on_false.resize_with(new_len, Vec::new);
            self.node_kinds.resize_with(new_len, || None);
        }
    }

    /// Find the SAT literal for a term. First checks var_map directly, then
    /// falls through to nnf_cache to find the NNF equivalent's var_map entry.
    fn lit_for_term(term: &Term, solver_state: &SolverState) -> Option<i32> {
        let uid = term.uid();
        if let Some(&lit) = solver_state.cnf_cache.var_map.get(&uid) {
            return Some(lit);
        }
        // Term not directly in var_map — look up its NNF equivalent
        if let Some(nnf_entry) = solver_state.cnf_cache.nnf_cache.get(&uid) {
            if let Some(ref nnf_term) = nnf_entry[1] {
                if let Some(&lit) = solver_state.cnf_cache.var_map.get(&nnf_term.uid()) {
                    return Some(lit);
                }
            }
        }
        None
    }

    /// Collect immediate sub-expression literals: descend until hitting a term
    /// that has a SAT literal (via var_map or nnf_cache).
    fn collect_subterm_lits(term: &Term, solver_state: &SolverState) -> Vec<i32> {
        let mut lits = Vec::new();
        let mut stack: Vec<&Term> = Vec::new();
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
            if let Some(lit) = Self::lit_for_term(t, solver_state) {
                lits.push(lit);
                continue;
            }
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

    /// Build relevancy structure from the pre-NNF assertion terms.
    /// This preserves Eq as Iff, ITE structure, etc. that NNF destroys.
    pub fn initialize_from_assertions(&mut self, solver_state: &SolverState) {
        if !self.enabled {
            return;
        }
        let assertions = solver_state.pre_nnf_assertions.clone();
        let mut visited = std::collections::HashSet::new();
        for assertion in &assertions {
            self.classify_recursive(assertion, solver_state, &mut visited);
        }
    }

    /// Recursively classify a pre-NNF term and all its sub-terms.
    fn classify_recursive(
        &mut self,
        term: &Term,
        solver_state: &SolverState,
        visited: &mut std::collections::HashSet<u64>,
    ) {
        let uid = term.uid();
        if !visited.insert(uid) {
            return;
        }

        let lit = match Self::lit_for_term(term, solver_state) {
            Some(l) => l,
            None => return,
        };
        let idx = lit.unsigned_abs() as usize;
        self.ensure_capacity(lit);

        if self.node_kinds[idx].is_some() {
            return;
        }

        let kind = match term.repr() {
            ATerm::Eq(a, b) => {
                // If the Eq uid is directly in var_map, NNF kept it as an atom
                // (non-boolean equality). Otherwise NNF expanded it → boolean Iff.
                if solver_state.cnf_cache.var_map.contains_key(&uid) {
                    NodeKind::Atom(Self::collect_subterm_lits(term, solver_state))
                } else {
                    let a_lit = Self::lit_for_term(a, solver_state);
                    let b_lit = Self::lit_for_term(b, solver_state);
                    if let (Some(al), Some(bl)) = (a_lit, b_lit) {
                        self.classify_recursive(a, solver_state, visited);
                        self.classify_recursive(b, solver_state, visited);
                        NodeKind::Iff(al, bl)
                    } else {
                        NodeKind::Atom(Self::collect_subterm_lits(term, solver_state))
                    }
                }
            }
            ATerm::Or(children) => {
                let child_lits: Vec<i32> = children
                    .iter()
                    .filter_map(|c| Self::lit_for_term(c, solver_state))
                    .collect();
                if child_lits.is_empty() {
                    NodeKind::Atom(Self::collect_subterm_lits(term, solver_state))
                } else {
                    for c in children {
                        self.classify_recursive(c, solver_state, visited);
                    }
                    NodeKind::Or(child_lits)
                }
            }
            ATerm::And(children) => {
                let child_lits: Vec<i32> = children
                    .iter()
                    .filter_map(|c| Self::lit_for_term(c, solver_state))
                    .collect();
                if child_lits.is_empty() {
                    NodeKind::Atom(Self::collect_subterm_lits(term, solver_state))
                } else {
                    for c in children {
                        self.classify_recursive(c, solver_state, visited);
                    }
                    NodeKind::And(child_lits)
                }
            }
            ATerm::Not(child) => {
                // Not shares abs index with child — just recurse, don't store
                self.classify_recursive(child, solver_state, visited);
                return;
            }
            ATerm::Ite(c, t, e) => {
                let c_lit = Self::lit_for_term(c, solver_state);
                let t_lit = Self::lit_for_term(t, solver_state);
                let e_lit = Self::lit_for_term(e, solver_state);
                if let (Some(cl), Some(tl), Some(el)) = (c_lit, t_lit, e_lit) {
                    self.classify_recursive(c, solver_state, visited);
                    self.classify_recursive(t, solver_state, visited);
                    self.classify_recursive(e, solver_state, visited);
                    NodeKind::Ite { cond: cl, then_lit: tl, else_lit: el }
                } else {
                    NodeKind::Atom(Self::collect_subterm_lits(term, solver_state))
                }
            }
            _ => NodeKind::Atom(Self::collect_subterm_lits(term, solver_state)),
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
        self.node_kinds[idx] = Some(kind);
    }

    /// Fallback: classify from var_map (for terms not covered by pre-NNF assertions,
    /// e.g. terms generated by boolean datatype preprocessing).
    pub fn initialize_structure(&mut self, solver_state: &SolverState) {
        if !self.enabled {
            return;
        }
        for (&uid, &lit) in solver_state.cnf_cache.var_map.iter() {
            let abs_lit = lit.unsigned_abs() as usize;
            self.ensure_capacity(lit);
            if self.node_kinds[abs_lit].is_some() {
                continue;
            }

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
                    if solver_state.cnf_cache.var_map.get(&child.uid()).is_some() {
                        continue;
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
            self.node_kinds[abs_lit] = Some(kind);
        }
    }

    /// Classify a term into a NodeKind (for lazy init of dynamic clauses).
    fn classify_term(&self, term: &Term, solver_state: &SolverState) -> NodeKind {
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
            return;
        }
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

        let positive = lit > 0;
        let targets: Vec<i32> = if positive {
            self.watches_on_true[idx].clone()
        } else {
            self.watches_on_false[idx].clone()
        };
        for target_lit in targets {
            self.mark_relevant(target_lit, level);
        }

        let cond_targets: Vec<usize> = if positive {
            self.cond_watches_on_true[idx].clone()
        } else {
            self.cond_watches_on_false[idx].clone()
        };
        for node_idx in cond_targets {
            self.queue.push_back(node_idx as i32);
        }

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
                        // OR true: one true child relevant (single-branch).
                        if self.branch_chosen[idx] {
                            return;
                        }
                        let mut found = false;
                        for &child_lit in child_lits {
                            if self.lit_is_true(child_lit, assignments) {
                                self.mark_relevant(child_lit, level);
                                self.branch_chosen[idx] = true;
                                self.branch_trail.push((level, idx));
                                found = true;
                                break;
                            }
                        }
                        if !found {
                            for &child_lit in child_lits {
                                self.install_cond_true_watch(child_lit, idx);
                            }
                        }
                    }
                    Some(false) => {
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
                        for &child_lit in child_lits {
                            self.mark_relevant(child_lit, level);
                        }
                    }
                    Some(false) => {
                        // AND false: one false child relevant (single-branch).
                        if self.branch_chosen[idx] {
                            return;
                        }
                        let mut found = false;
                        for &child_lit in child_lits {
                            if self.lit_is_false(child_lit, assignments) {
                                self.mark_relevant(child_lit, level);
                                self.branch_chosen[idx] = true;
                                self.branch_trail.push((level, idx));
                                found = true;
                                break;
                            }
                        }
                        if !found {
                            for &child_lit in child_lits {
                                self.install_cond_false_watch(child_lit, idx);
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
                self.mark_relevant(a_lit, level);
                self.mark_relevant(b_lit, level);
            }
            NodeKind::Ite { cond, then_lit, else_lit } => {
                self.mark_relevant(cond, level);
                let ite_val = self.get_assignment_by_idx(idx, assignments);
                let cond_val = self.lit_is_true(cond, assignments);
                let cond_false = self.lit_is_false(cond, assignments);
                match ite_val {
                    Some(true) => {
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
                    None => {}
                }
            }
            NodeKind::Atom(ref subterm_lits) => {
                for &sub_lit in subterm_lits {
                    self.mark_relevant(sub_lit, level);
                }
            }
        }
    }

    fn install_true_watch(&mut self, watched_lit: i32, target: i32) {
        self.ensure_capacity(watched_lit);
        let idx = watched_lit.unsigned_abs() as usize;
        if watched_lit > 0 {
            self.watches_on_true[idx].push(target);
        } else {
            self.watches_on_false[idx].push(target);
        }
    }

    fn install_false_watch(&mut self, watched_lit: i32, target: i32) {
        self.ensure_capacity(watched_lit);
        let idx = watched_lit.unsigned_abs() as usize;
        if watched_lit > 0 {
            self.watches_on_false[idx].push(target);
        } else {
            self.watches_on_true[idx].push(target);
        }
    }

    fn install_cond_true_watch(&mut self, watched_lit: i32, node_idx: usize) {
        self.ensure_capacity(watched_lit);
        let idx = watched_lit.unsigned_abs() as usize;
        if watched_lit > 0 {
            self.cond_watches_on_true[idx].push(node_idx);
        } else {
            self.cond_watches_on_false[idx].push(node_idx);
        }
    }

    fn install_cond_false_watch(&mut self, watched_lit: i32, node_idx: usize) {
        self.ensure_capacity(watched_lit);
        let idx = watched_lit.unsigned_abs() as usize;
        if watched_lit > 0 {
            self.cond_watches_on_false[idx].push(node_idx);
        } else {
            self.cond_watches_on_true[idx].push(node_idx);
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
        while let Some(&(mark_level, node_idx)) = self.branch_trail.last() {
            if mark_level <= level {
                break;
            }
            self.branch_trail.pop();
            self.branch_chosen[node_idx] = false;
        }
        self.queue.clear();
    }
}
