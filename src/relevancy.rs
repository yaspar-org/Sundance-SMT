// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Relevancy propagation engine for gating theory solver work.
//!
//! Implements the propagation rules from de Moura & Bjørner (2007) / Z3 internals §7.1.4.
//! The classification of terms into NodeKinds is done by SolverState; this module
//! only handles the propagation of relevancy through the registered structure.

use std::collections::VecDeque;
use std::sync::atomic::AtomicBool;

static RELEVANCY_TRACE: AtomicBool = AtomicBool::new(false);

pub fn init_relevancy_trace() {
    RELEVANCY_TRACE.store(
        std::env::var("SUNDANCE_RELEVANCY_TRACE").is_ok(),
        std::sync::atomic::Ordering::Relaxed,
    );
}

#[derive(Debug, Clone)]
pub(crate) enum NodeKind {
    Or(Vec<i32>),
    And(Vec<i32>),
    #[allow(dead_code)]
    Not(i32),
    Iff(i32, i32),
    Ite { cond: i32, then_lit: i32, else_lit: i32 },
    Atom(Vec<i32>),
}

pub(crate) trait RelevancyTrait {
    fn is_enabled(&self) -> bool;
    fn has_node(&self, lit: i32) -> bool;
    fn register_node(&mut self, lit: i32, kind: NodeKind);
    /// Mark `lit` as a relevant root. If `class_root` is provided, the
    /// egraph class it identifies is also marked relevant (all future
    /// lits whose term resolves to the same class are treated as relevant
    /// via `is_relevant_with_class`).
    fn mark_relevant_root(&mut self, lit: i32, class_root: Option<u32>, level: usize);
    fn is_relevant(&self, lit: i32) -> bool;
    /// Same as `is_relevant` but also returns true if the given class
    /// root has been marked relevant (by any prior `mark_relevant_root`
    /// or `propagate_class_relevancy` call).
    fn is_relevant_with_class(&self, lit: i32, class_root: Option<u32>) -> bool;
    fn notify_assignment(&mut self, lit: i32, level: usize) -> bool;
    /// After an egraph merge, propagate class relevancy: if either
    /// pre-merge root was relevant, mark `survivor` relevant.
    fn propagate_class_relevancy(&mut self, survivor: u32, demoted: u32, level: usize);
    fn backtrack_to(&mut self, level: usize);
}

pub struct RelevancyState {
    node_kinds: Vec<Option<NodeKind>>,
    relevant: Vec<bool>,
    branch_chosen: Vec<bool>,
    /// Per-variable polarity: 0=unassigned, 1=positive, -1=negative.
    assignments: Vec<i8>,
    /// Trail for undoing assignments on backtrack: (level, var_idx).
    assignment_trail: Vec<(usize, usize)>,
    watches_on_true: Vec<Vec<i32>>,
    watches_on_false: Vec<Vec<i32>>,
    cond_watches_on_true: Vec<Vec<usize>>,
    cond_watches_on_false: Vec<Vec<usize>>,
    queue: VecDeque<i32>,
    trail: Vec<(usize, i32)>,
    branch_trail: Vec<(usize, usize)>,
    /// Egraph class roots that contain at least one relevant lit. Callers
    /// pass the current root explicitly; this state doesn't do egraph
    /// lookups itself.
    class_relevant: std::collections::HashSet<u32>,
    /// Trail of `(level, root)` insertions into `class_relevant`.
    class_trail: Vec<(usize, u32)>,
    enabled: bool,
}

impl RelevancyState {
    pub fn new(enabled: bool) -> Self {
        RelevancyState {
            node_kinds: Vec::new(),
            relevant: Vec::new(),
            branch_chosen: Vec::new(),
            assignments: Vec::new(),
            assignment_trail: Vec::new(),
            watches_on_true: Vec::new(),
            watches_on_false: Vec::new(),
            cond_watches_on_true: Vec::new(),
            cond_watches_on_false: Vec::new(),
            queue: VecDeque::new(),
            trail: Vec::new(),
            branch_trail: Vec::new(),
            class_relevant: std::collections::HashSet::new(),
            class_trail: Vec::new(),
            enabled,
        }
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

    fn propagate(&mut self, level: usize) {
        while let Some(lit) = self.queue.pop_front() {
            let idx = lit.unsigned_abs() as usize;
            self.propagate_node(idx, level);
        }
    }

    fn ensure_capacity(&mut self, lit: i32) {
        let idx = lit.unsigned_abs() as usize;
        if idx >= self.relevant.len() {
            let new_len = (idx + 1).max(self.relevant.len() * 2).max(64);
            self.relevant.resize(new_len, false);
            self.branch_chosen.resize(new_len, false);
            self.assignments.resize(new_len, 0);
            self.watches_on_true.resize_with(new_len, Vec::new);
            self.watches_on_false.resize_with(new_len, Vec::new);
            self.cond_watches_on_true.resize_with(new_len, Vec::new);
            self.cond_watches_on_false.resize_with(new_len, Vec::new);
            self.node_kinds.resize_with(new_len, || None);
        }
    }

    fn propagate_node(&mut self, idx: usize, level: usize) {
        if idx >= self.node_kinds.len() {
            return;
        }
        let kind = match self.node_kinds[idx].clone() {
            Some(k) => k,
            None => return,
        };
        match kind {
            NodeKind::Or(ref child_lits) => {
                match self.get_assignment_by_idx(idx) {
                    Some(true) => {
                        if self.branch_chosen[idx] {
                            return;
                        }
                        let mut found = false;
                        for &child_lit in child_lits {
                            if self.lit_is_true(child_lit) {
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
                match self.get_assignment_by_idx(idx) {
                    Some(true) => {
                        for &child_lit in child_lits {
                            self.mark_relevant(child_lit, level);
                        }
                    }
                    Some(false) => {
                        if self.branch_chosen[idx] {
                            return;
                        }
                        let mut found = false;
                        for &child_lit in child_lits {
                            if self.lit_is_false(child_lit) {
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
                let ite_val = self.get_assignment_by_idx(idx);
                let cond_val = self.lit_is_true(cond);
                let cond_false = self.lit_is_false(cond);
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

    fn get_assignment_by_idx(&self, idx: usize) -> Option<bool> {
        if idx >= self.assignments.len() {
            return None;
        }
        let val = self.assignments[idx];
        if val == 0 { None } else { Some(val > 0) }
    }

    fn lit_is_true(&self, lit: i32) -> bool {
        let idx = lit.unsigned_abs() as usize;
        if idx >= self.assignments.len() { return false; }
        let val = self.assignments[idx];
        if val == 0 { return false; }
        (val > 0) == (lit > 0)
    }

    fn lit_is_false(&self, lit: i32) -> bool {
        let idx = lit.unsigned_abs() as usize;
        if idx >= self.assignments.len() { return false; }
        let val = self.assignments[idx];
        if val == 0 { return false; }
        (val > 0) != (lit > 0)
    }
}

impl RelevancyTrait for RelevancyState {
    fn is_enabled(&self) -> bool {
        self.enabled
    }

    fn has_node(&self, lit: i32) -> bool {
        let idx = lit.unsigned_abs() as usize;
        idx < self.node_kinds.len() && self.node_kinds[idx].is_some()
    }

    fn register_node(&mut self, lit: i32, kind: NodeKind) {
        self.ensure_capacity(lit);
        let idx = lit.unsigned_abs() as usize;
        if self.node_kinds[idx].is_none() {
            if RELEVANCY_TRACE.load(std::sync::atomic::Ordering::Relaxed)
                || std::env::var("SUNDANCE_RELEVANCY_TRACE").is_ok() {
                let kind_name = match &kind {
                    NodeKind::Or(c) => format!("Or({})", c.len()),
                    NodeKind::And(c) => format!("And({})", c.len()),
                    NodeKind::Not(c) => format!("Not({})", c),
                    NodeKind::Iff(a, b) => format!("Iff({},{})", a, b),
                    NodeKind::Ite { cond, .. } => format!("Ite(cond={})", cond),
                    NodeKind::Atom(s) => format!("Atom(subs={:?})", s),
                };
                eprintln!("[relevancy] register lit={} kind={}", lit, kind_name);
            }
            self.node_kinds[idx] = Some(kind);
        }
    }

    fn mark_relevant_root(&mut self, lit: i32, class_root: Option<u32>, level: usize) {
        self.mark_relevant(lit, level);
        if let Some(root) = class_root {
            if self.class_relevant.insert(root) {
                self.class_trail.push((level, root));
                if RELEVANCY_TRACE.load(std::sync::atomic::Ordering::Relaxed)
                    || std::env::var("SUNDANCE_RELEVANCY_TRACE").is_ok()
                {
                    eprintln!("[relevancy] class_root {} marked relevant (via lit={}, level={})", root, lit, level);
                }
            }
        }
        self.propagate(level);
    }

    fn is_relevant(&self, lit: i32) -> bool {
        if !self.enabled {
            return true;
        }
        let idx = lit.unsigned_abs() as usize;
        if idx >= self.relevant.len() {
            return false;
        }
        self.relevant[idx]
    }

    fn is_relevant_with_class(&self, lit: i32, class_root: Option<u32>) -> bool {
        if !self.enabled {
            return true;
        }
        if self.is_relevant(lit) {
            return true;
        }
        class_root.is_some_and(|r| self.class_relevant.contains(&r))
    }

    fn propagate_class_relevancy(&mut self, survivor: u32, demoted: u32, level: usize) {
        if !self.enabled {
            return;
        }
        let s_rel = self.class_relevant.contains(&survivor);
        let d_rel = self.class_relevant.contains(&demoted);
        if (s_rel || d_rel) && !s_rel {
            self.class_relevant.insert(survivor);
            self.class_trail.push((level, survivor));
            if RELEVANCY_TRACE.load(std::sync::atomic::Ordering::Relaxed)
                || std::env::var("SUNDANCE_RELEVANCY_TRACE").is_ok()
            {
                eprintln!("[relevancy] class_root {} promoted to relevant on merge with {} (level={})", survivor, demoted, level);
            }
        }
    }

    fn notify_assignment(&mut self, lit: i32, level: usize) -> bool {
        if !self.enabled {
            return true;
        }
        self.ensure_capacity(lit);
        let idx = lit.unsigned_abs() as usize;

        // Record the assignment internally
        self.assignments[idx] = if lit > 0 { 1 } else { -1 };
        self.assignment_trail.push((level, idx));

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
            self.propagate_node(idx, level);
        }

        self.propagate(level);
        self.relevant[idx]
    }

    fn backtrack_to(&mut self, level: usize) {
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
        while let Some(&(mark_level, var_idx)) = self.assignment_trail.last() {
            if mark_level <= level {
                break;
            }
            self.assignment_trail.pop();
            self.assignments[var_idx] = 0;
        }
        while let Some(&(mark_level, root)) = self.class_trail.last() {
            if mark_level <= level {
                break;
            }
            self.class_trail.pop();
            self.class_relevant.remove(&root);
        }
        self.queue.clear();
    }
}
