// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Relevancy propagation engine for gating theory solver work.
//!
//! Implements the propagation rules from de Moura & Bjørner (2007) / Z3 internals §7.1.4.
//! The classification of terms into NodeKinds is done by SolverState; this module
//! only handles the propagation of relevancy through the registered structure.

use std::collections::VecDeque;

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

pub trait RelevancyTrait {
    fn is_enabled(&self) -> bool;
    fn has_node(&self, lit: i32) -> bool;
    fn register_node(&mut self, lit: i32, kind: NodeKind);
    fn mark_relevant_root(&mut self, lit: i32, level: usize, assignments: &[i32]);
    fn mark_relevant_roots(&mut self, root_lits: &[i32], level: usize, assignments: &[i32]);
    fn is_relevant(&self, lit: i32) -> bool;
    fn notify_assignment(&mut self, lit: i32, level: usize, assignments: &[i32]) -> bool;
    fn backtrack_to(&mut self, level: usize);
}

pub struct RelevancyState {
    node_kinds: Vec<Option<NodeKind>>,
    relevant: Vec<bool>,
    branch_chosen: Vec<bool>,
    watches_on_true: Vec<Vec<i32>>,
    watches_on_false: Vec<Vec<i32>>,
    cond_watches_on_true: Vec<Vec<usize>>,
    cond_watches_on_false: Vec<Vec<usize>>,
    queue: VecDeque<i32>,
    trail: Vec<(usize, i32)>,
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

    fn propagate(&mut self, level: usize, assignments: &[i32]) {
        while let Some(lit) = self.queue.pop_front() {
            let idx = lit.unsigned_abs() as usize;
            self.propagate_node(idx, level, assignments);
        }
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
            self.node_kinds[idx] = Some(kind);
        }
    }

    fn mark_relevant_root(&mut self, lit: i32, level: usize, assignments: &[i32]) {
        self.mark_relevant(lit, level);
        self.propagate(level, assignments);
    }

    fn mark_relevant_roots(&mut self, root_lits: &[i32], level: usize, assignments: &[i32]) {
        if !self.enabled {
            return;
        }
        for &lit in root_lits {
            self.mark_relevant(lit, level);
        }
        self.propagate(level, assignments);
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

    fn notify_assignment(&mut self, lit: i32, level: usize, assignments: &[i32]) -> bool {
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
        self.queue.clear();
    }
}
