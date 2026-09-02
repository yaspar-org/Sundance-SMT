// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Relevancy propagation engine for gating theory solver work.
//!
//! Implements the propagation rules from de Moura & Bjørner (2007) / Z3 internals §7.1.4.
//! The classification of terms into NodeKinds is done by SolverState; this module
//! only handles the propagation of relevancy through the registered structure.

use std::collections::{HashMap, VecDeque};
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
    Ite {
        cond: i32,
        then_lit: i32,
        else_lit: i32,
    },
    Atom(Vec<i32>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct RelevantLitEvent {
    pub lit: i32,
    pub level: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct RelevantTermEvent {
    pub uid: u64,
    pub level: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct RelevantClassEvent {
    pub root: u32,
    pub level: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct LitWatch {
    parent_idx: usize,
    target: i32,
    level: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CondWatch {
    parent_idx: usize,
    level: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct TermIteWatch {
    parent_uid: u64,
    cond: i32,
    then_uid: u64,
    else_uid: u64,
    level: usize,
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
    /// Snapshot access to the set of egraph class roots currently marked
    /// relevant. Used by e-matching to filter candidate ground terms.
    fn class_relevant_set(&self) -> &std::collections::HashSet<u32>;
    /// Add `class_root` to the relevant class set (idempotent). Used by
    /// structural relevancy propagation to mark subterm classes reachable
    /// from a term whose lit was marked relevant.
    fn add_class_relevant(&mut self, class_root: u32, level: usize);
    fn mark_term_relevant(&mut self, uid: u64, level: usize);
    fn install_term_ite_watch(
        &mut self,
        parent_uid: u64,
        cond: i32,
        then_uid: u64,
        else_uid: u64,
        level: usize,
    );
    fn lit_truth(&self, lit: i32) -> Option<bool>;
    fn lit_assignment_level(&self, lit: i32) -> Option<usize>;
    fn drain_lits_for_term_propagation(&mut self) -> Vec<RelevantLitEvent>;
    fn drain_newly_relevant_lits(&mut self) -> Vec<RelevantLitEvent>;
    fn drain_newly_relevant_terms(&mut self) -> Vec<RelevantTermEvent>;
    fn drain_newly_relevant_classes(&mut self) -> Vec<RelevantClassEvent>;
    fn notify_assignment(&mut self, lit: i32, level: usize) -> bool;
    /// After an egraph merge, propagate class relevancy: if either
    /// pre-merge root was relevant, mark `survivor` relevant.
    fn propagate_class_relevancy(&mut self, survivor: u32, demoted: u32, level: usize);
    fn backtrack_to(&mut self, level: usize);
}

pub struct RelevancyState {
    node_kinds: Vec<Option<NodeKind>>,
    /// Sign of the lit passed to `register_node` for this idx. `+1` means the
    /// term is TRUE iff `assignments[idx] > 0`; `-1` means the term is TRUE
    /// iff `assignments[idx] < 0`. Needed because `relevancy_lit_for_term`
    /// can return a signed lit (e.g. when only the NNF-negation of the term
    /// is Tseitin-cached, as for an OR that appears only under top-level
    /// `not`). Without this, `propagate_node` fires the wrong branch
    /// (Or-TRUE when the OR is actually FALSE) and dependent lits never
    /// become relevant.
    node_polarity: Vec<i8>,
    relevant: Vec<bool>,
    relevance_levels: Vec<Option<usize>>,
    branch_choices: Vec<Option<i32>>,
    branch_levels: Vec<Option<usize>>,
    /// Per-variable polarity: 0=unassigned, 1=positive, -1=negative.
    assignments: Vec<i8>,
    assignment_levels: Vec<Option<usize>>,
    watches_on_true: Vec<Vec<LitWatch>>,
    watches_on_false: Vec<Vec<LitWatch>>,
    cond_watches_on_true: Vec<Vec<CondWatch>>,
    cond_watches_on_false: Vec<Vec<CondWatch>>,
    term_ite_watches: Vec<Vec<TermIteWatch>>,
    queue: VecDeque<(i32, usize)>,
    lits_for_term_propagation: VecDeque<RelevantLitEvent>,
    newly_relevant_lits: VecDeque<RelevantLitEvent>,
    relevant_term_levels: HashMap<u64, usize>,
    newly_relevant_terms: VecDeque<RelevantTermEvent>,
    /// Egraph class roots that contain at least one relevant lit. Callers
    /// pass the current root explicitly; this state doesn't do egraph
    /// lookups itself.
    class_relevant: std::collections::HashSet<u32>,
    class_relevance_levels: HashMap<u32, usize>,
    newly_relevant_classes: VecDeque<RelevantClassEvent>,
    enabled: bool,
}

impl RelevancyState {
    pub fn new(enabled: bool) -> Self {
        RelevancyState {
            node_kinds: Vec::new(),
            node_polarity: Vec::new(),
            relevant: Vec::new(),
            relevance_levels: Vec::new(),
            branch_choices: Vec::new(),
            branch_levels: Vec::new(),
            assignments: Vec::new(),
            assignment_levels: Vec::new(),
            watches_on_true: Vec::new(),
            watches_on_false: Vec::new(),
            cond_watches_on_true: Vec::new(),
            cond_watches_on_false: Vec::new(),
            term_ite_watches: Vec::new(),
            queue: VecDeque::new(),
            lits_for_term_propagation: VecDeque::new(),
            newly_relevant_lits: VecDeque::new(),
            relevant_term_levels: HashMap::new(),
            newly_relevant_terms: VecDeque::new(),
            class_relevant: std::collections::HashSet::new(),
            class_relevance_levels: HashMap::new(),
            newly_relevant_classes: VecDeque::new(),
            enabled,
        }
    }

    fn mark_relevant(&mut self, lit: i32, level: usize) -> bool {
        self.ensure_capacity(lit);
        let idx = lit.unsigned_abs() as usize;
        let old_level = self.relevance_levels[idx];
        if old_level.is_some_and(|old| old <= level) {
            if std::env::var("SUNDANCE_RELEVANCY_TRACE").is_ok() {
                eprintln!(
                    "[relevancy] mark_relevant(lit={}, level={}) — already relevant at {:?}, no-op",
                    lit, level, old_level
                );
            }
            return false;
        }
        self.relevant[idx] = true;
        self.relevance_levels[idx] = Some(level);
        self.queue.push_back((lit, level));
        let event = RelevantLitEvent { lit, level };
        self.lits_for_term_propagation.push_back(event);
        self.newly_relevant_lits.push_back(event);
        if std::env::var("SUNDANCE_RELEVANCY_TRACE").is_ok() {
            eprintln!(
                "[relevancy] mark_relevant(lit={}, level={}) — newly relevant or lowered from {:?}, queued",
                lit, level, old_level
            );
        }
        true
    }

    fn mark_term_relevant_internal(&mut self, uid: u64, level: usize) -> bool {
        if self
            .relevant_term_levels
            .get(&uid)
            .is_some_and(|old| *old <= level)
        {
            return false;
        }
        self.relevant_term_levels.insert(uid, level);
        self.newly_relevant_terms
            .push_back(RelevantTermEvent { uid, level });
        true
    }

    fn mark_class_relevant_internal(&mut self, root: u32, level: usize) -> bool {
        if self
            .class_relevance_levels
            .get(&root)
            .is_some_and(|old| *old <= level)
        {
            return false;
        }
        self.class_relevant.insert(root);
        self.class_relevance_levels.insert(root, level);
        self.newly_relevant_classes
            .push_back(RelevantClassEvent { root, level });
        true
    }

    fn mark_branch_chosen(&mut self, idx: usize, child_lit: i32, level: usize) {
        if self.branch_choices[idx] == Some(child_lit)
            && self.branch_levels[idx].is_some_and(|old| old <= level)
        {
            return;
        }
        debug_assert!(
            self.branch_choices[idx].is_none() || self.branch_choices[idx] == Some(child_lit),
            "a relevance branch cannot change without backtracking"
        );
        self.branch_choices[idx] = Some(child_lit);
        self.branch_levels[idx] = Some(level);
    }

    fn relevance_level(&self, idx: usize) -> Option<usize> {
        self.relevance_levels.get(idx).copied().flatten()
    }

    fn assignment_level(&self, idx: usize) -> Option<usize> {
        self.assignment_levels.get(idx).copied().flatten()
    }

    fn propagate(&mut self) {
        while let Some((lit, _level)) = self.queue.pop_front() {
            let idx = lit.unsigned_abs() as usize;
            self.propagate_node(idx);
        }
    }

    fn ensure_capacity(&mut self, lit: i32) {
        let idx = lit.unsigned_abs() as usize;
        if idx >= self.relevant.len() {
            let new_len = (idx + 1).max(self.relevant.len() * 2).max(64);
            self.relevant.resize(new_len, false);
            self.relevance_levels.resize(new_len, None);
            self.branch_choices.resize(new_len, None);
            self.branch_levels.resize(new_len, None);
            self.assignments.resize(new_len, 0);
            self.assignment_levels.resize(new_len, None);
            self.watches_on_true.resize_with(new_len, Vec::new);
            self.watches_on_false.resize_with(new_len, Vec::new);
            self.cond_watches_on_true.resize_with(new_len, Vec::new);
            self.cond_watches_on_false.resize_with(new_len, Vec::new);
            self.term_ite_watches.resize_with(new_len, Vec::new);
            self.node_kinds.resize_with(new_len, || None);
            self.node_polarity.resize(new_len, 1);
        }
    }

    /// Returns the assignment of the *term* at `idx`, adjusted for the
    /// registration polarity. `Some(true)` means the term is currently
    /// TRUE; `Some(false)` means FALSE; `None` means the SAT var is
    /// unassigned.
    fn get_term_truth(&self, idx: usize) -> Option<bool> {
        let raw = self.get_assignment_by_idx(idx)?;
        let pol = if idx < self.node_polarity.len() {
            self.node_polarity[idx]
        } else {
            1
        };
        Some(raw == (pol > 0))
    }

    fn propagate_node(&mut self, idx: usize) {
        if idx >= self.node_kinds.len() {
            return;
        }
        let Some(parent_level) = self.relevance_level(idx) else {
            return;
        };
        let kind = match self.node_kinds[idx].clone() {
            Some(k) => k,
            None => return,
        };
        match kind {
            NodeKind::Or(ref child_lits) => match self.get_term_truth(idx) {
                Some(true) => {
                    let base_level =
                        parent_level.max(self.assignment_level(idx).unwrap_or(parent_level));
                    if let Some(child_lit) = self.branch_choices[idx] {
                        if self.lit_is_true(child_lit) {
                            let child_idx = child_lit.unsigned_abs() as usize;
                            let level = base_level
                                .max(self.assignment_level(child_idx).unwrap_or(base_level));
                            self.mark_relevant(child_lit, level);
                            self.mark_branch_chosen(idx, child_lit, level);
                        }
                        return;
                    }
                    let mut found = false;
                    for &child_lit in child_lits {
                        if self.lit_is_true(child_lit) {
                            let child_idx = child_lit.unsigned_abs() as usize;
                            let level = base_level
                                .max(self.assignment_level(child_idx).unwrap_or(base_level));
                            if std::env::var("SUNDANCE_RELEVANCY_TRACE").is_ok() {
                                eprintln!(
                                    "[relevancy] Or-true idx={} picking child={} (level={})",
                                    idx, child_lit, level
                                );
                            }
                            self.mark_relevant(child_lit, level);
                            self.mark_branch_chosen(idx, child_lit, level);
                            found = true;
                            break;
                        }
                    }
                    if !found {
                        if std::env::var("SUNDANCE_RELEVANCY_TRACE").is_ok() {
                            let child_states: Vec<String> = child_lits
                                .iter()
                                .map(|&c| {
                                    let v = self.get_assignment_by_idx(c.unsigned_abs() as usize);
                                    format!("{}:{:?}", c, v)
                                })
                                .collect();
                            eprintln!(
                                "[relevancy] Or-true idx={} no true child, installing cond_watches on {:?} (level={})",
                                idx, child_states, base_level
                            );
                        }
                        for &child_lit in child_lits {
                            self.install_cond_true_watch(child_lit, idx, base_level);
                        }
                    }
                }
                Some(false) => {
                    let level =
                        parent_level.max(self.assignment_level(idx).unwrap_or(parent_level));
                    for &child_lit in child_lits {
                        self.mark_relevant(child_lit, level);
                    }
                }
                None => {}
            },
            NodeKind::And(ref child_lits) => match self.get_term_truth(idx) {
                Some(true) => {
                    let level =
                        parent_level.max(self.assignment_level(idx).unwrap_or(parent_level));
                    if std::env::var("SUNDANCE_RELEVANCY_TRACE").is_ok() {
                        eprintln!(
                            "[relevancy] And-true idx={} marking children {:?} relevant (level={})",
                            idx, child_lits, level
                        );
                    }
                    for &child_lit in child_lits {
                        self.mark_relevant(child_lit, level);
                    }
                }
                Some(false) => {
                    let base_level =
                        parent_level.max(self.assignment_level(idx).unwrap_or(parent_level));
                    if let Some(child_lit) = self.branch_choices[idx] {
                        if self.lit_is_false(child_lit) {
                            let child_idx = child_lit.unsigned_abs() as usize;
                            let level = base_level
                                .max(self.assignment_level(child_idx).unwrap_or(base_level));
                            self.mark_relevant(child_lit, level);
                            self.mark_branch_chosen(idx, child_lit, level);
                        }
                        return;
                    }
                    let mut found = false;
                    for &child_lit in child_lits {
                        if self.lit_is_false(child_lit) {
                            let child_idx = child_lit.unsigned_abs() as usize;
                            let level = base_level
                                .max(self.assignment_level(child_idx).unwrap_or(base_level));
                            self.mark_relevant(child_lit, level);
                            self.mark_branch_chosen(idx, child_lit, level);
                            found = true;
                            break;
                        }
                    }
                    if !found {
                        for &child_lit in child_lits {
                            self.install_cond_false_watch(child_lit, idx, base_level);
                        }
                    }
                }
                None => {}
            },
            NodeKind::Not(child_lit) => {
                self.mark_relevant(child_lit, parent_level);
            }
            NodeKind::Iff(a_lit, b_lit) => {
                self.mark_relevant(a_lit, parent_level);
                self.mark_relevant(b_lit, parent_level);
            }
            NodeKind::Ite {
                cond,
                then_lit,
                else_lit,
            } => {
                self.mark_relevant(cond, parent_level);
                let cond_idx = cond.unsigned_abs() as usize;
                let branch_level =
                    parent_level.max(self.assignment_level(cond_idx).unwrap_or(parent_level));
                if self.lit_is_true(cond) {
                    self.mark_relevant(then_lit, branch_level);
                } else if self.lit_is_false(cond) {
                    self.mark_relevant(else_lit, branch_level);
                } else {
                    self.install_true_watch(cond, idx, then_lit, parent_level);
                    self.install_false_watch(cond, idx, else_lit, parent_level);
                }
            }
            NodeKind::Atom(ref subterm_lits) => {
                for &sub_lit in subterm_lits {
                    self.mark_relevant(sub_lit, parent_level);
                }
            }
        }
    }

    fn install_true_watch(
        &mut self,
        watched_lit: i32,
        parent_idx: usize,
        target: i32,
        level: usize,
    ) {
        self.ensure_capacity(watched_lit);
        let idx = watched_lit.unsigned_abs() as usize;
        let watches = if watched_lit > 0 {
            &mut self.watches_on_true[idx]
        } else {
            &mut self.watches_on_false[idx]
        };
        Self::insert_lit_watch(watches, parent_idx, target, level);
    }

    fn install_false_watch(
        &mut self,
        watched_lit: i32,
        parent_idx: usize,
        target: i32,
        level: usize,
    ) {
        self.ensure_capacity(watched_lit);
        let idx = watched_lit.unsigned_abs() as usize;
        let watches = if watched_lit > 0 {
            &mut self.watches_on_false[idx]
        } else {
            &mut self.watches_on_true[idx]
        };
        Self::insert_lit_watch(watches, parent_idx, target, level);
    }

    fn insert_lit_watch(watches: &mut Vec<LitWatch>, parent_idx: usize, target: i32, level: usize) {
        if let Some(existing) = watches
            .iter_mut()
            .find(|watch| watch.parent_idx == parent_idx && watch.target == target)
        {
            existing.level = existing.level.min(level);
        } else {
            watches.push(LitWatch {
                parent_idx,
                target,
                level,
            });
        }
    }

    fn install_cond_true_watch(&mut self, watched_lit: i32, parent_idx: usize, level: usize) {
        self.ensure_capacity(watched_lit);
        let idx = watched_lit.unsigned_abs() as usize;
        let watches = if watched_lit > 0 {
            &mut self.cond_watches_on_true[idx]
        } else {
            &mut self.cond_watches_on_false[idx]
        };
        Self::insert_cond_watch(watches, parent_idx, level);
    }

    fn install_cond_false_watch(&mut self, watched_lit: i32, parent_idx: usize, level: usize) {
        self.ensure_capacity(watched_lit);
        let idx = watched_lit.unsigned_abs() as usize;
        let watches = if watched_lit > 0 {
            &mut self.cond_watches_on_false[idx]
        } else {
            &mut self.cond_watches_on_true[idx]
        };
        Self::insert_cond_watch(watches, parent_idx, level);
    }

    fn insert_cond_watch(watches: &mut Vec<CondWatch>, parent_idx: usize, level: usize) {
        if let Some(existing) = watches
            .iter_mut()
            .find(|watch| watch.parent_idx == parent_idx)
        {
            existing.level = existing.level.min(level);
        } else {
            watches.push(CondWatch { parent_idx, level });
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
        if idx >= self.assignments.len() {
            return false;
        }
        let val = self.assignments[idx];
        if val == 0 {
            return false;
        }
        (val > 0) == (lit > 0)
    }

    fn lit_is_false(&self, lit: i32) -> bool {
        let idx = lit.unsigned_abs() as usize;
        if idx >= self.assignments.len() {
            return false;
        }
        let val = self.assignments[idx];
        if val == 0 {
            return false;
        }
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
                || std::env::var("SUNDANCE_RELEVANCY_TRACE").is_ok()
            {
                let kind_name = match &kind {
                    NodeKind::Or(c) => format!("Or({}) children={:?}", c.len(), c),
                    NodeKind::And(c) => format!("And({}) children={:?}", c.len(), c),
                    NodeKind::Not(c) => format!("Not({})", c),
                    NodeKind::Iff(a, b) => format!("Iff({},{})", a, b),
                    NodeKind::Ite { cond, .. } => format!("Ite(cond={})", cond),
                    NodeKind::Atom(s) => format!("Atom(subs={:?})", s),
                };
                let asgn = if idx < self.assignments.len() {
                    self.assignments[idx]
                } else {
                    0
                };
                let rel = idx < self.relevant.len() && self.relevant[idx];
                eprintln!(
                    "[relevancy] register lit={} kind={} (already-assigned={} already-relevant={})",
                    lit, kind_name, asgn, rel
                );
            }
            self.node_kinds[idx] = Some(kind);
            self.node_polarity[idx] = if lit >= 0 { 1 } else { -1 };
        }
    }

    fn mark_relevant_root(&mut self, lit: i32, class_root: Option<u32>, level: usize) {
        self.mark_relevant(lit, level);
        if let Some(root) = class_root {
            if self.mark_class_relevant_internal(root, level) {
                if RELEVANCY_TRACE.load(std::sync::atomic::Ordering::Relaxed)
                    || std::env::var("SUNDANCE_RELEVANCY_TRACE").is_ok()
                {
                    eprintln!(
                        "[relevancy] class_root {} marked relevant (via lit={}, level={})",
                        root, lit, level
                    );
                }
            }
        }
        self.propagate();
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

    fn class_relevant_set(&self) -> &std::collections::HashSet<u32> {
        &self.class_relevant
    }

    fn add_class_relevant(&mut self, class_root: u32, level: usize) {
        if !self.enabled {
            return;
        }
        if self.mark_class_relevant_internal(class_root, level) {
            if std::env::var("SUNDANCE_RELEVANCY_TRACE").is_ok() {
                eprintln!(
                    "[relevancy] class_root {} became relevant (level={})",
                    class_root, level
                );
            }
        }
    }

    fn mark_term_relevant(&mut self, uid: u64, level: usize) {
        if self.enabled {
            self.mark_term_relevant_internal(uid, level);
        }
    }

    fn install_term_ite_watch(
        &mut self,
        parent_uid: u64,
        cond: i32,
        then_uid: u64,
        else_uid: u64,
        level: usize,
    ) {
        if !self.enabled {
            return;
        }
        self.ensure_capacity(cond);
        let idx = cond.unsigned_abs() as usize;
        if let Some(existing) = self.term_ite_watches[idx].iter_mut().find(|watch| {
            watch.parent_uid == parent_uid
                && watch.cond == cond
                && watch.then_uid == then_uid
                && watch.else_uid == else_uid
        }) {
            existing.level = existing.level.min(level);
        } else {
            self.term_ite_watches[idx].push(TermIteWatch {
                parent_uid,
                cond,
                then_uid,
                else_uid,
                level,
            });
        }
    }

    fn lit_truth(&self, lit: i32) -> Option<bool> {
        let idx = lit.unsigned_abs() as usize;
        self.get_assignment_by_idx(idx)
            .map(|positive| positive == (lit > 0))
    }

    fn lit_assignment_level(&self, lit: i32) -> Option<usize> {
        self.assignment_level(lit.unsigned_abs() as usize)
    }

    fn drain_lits_for_term_propagation(&mut self) -> Vec<RelevantLitEvent> {
        self.lits_for_term_propagation.drain(..).collect()
    }

    fn drain_newly_relevant_lits(&mut self) -> Vec<RelevantLitEvent> {
        self.newly_relevant_lits.drain(..).collect()
    }

    fn drain_newly_relevant_terms(&mut self) -> Vec<RelevantTermEvent> {
        self.newly_relevant_terms.drain(..).collect()
    }

    fn drain_newly_relevant_classes(&mut self) -> Vec<RelevantClassEvent> {
        self.newly_relevant_classes.drain(..).collect()
    }

    fn propagate_class_relevancy(&mut self, survivor: u32, demoted: u32, level: usize) {
        if !self.enabled {
            return;
        }
        let survivor_level = self.class_relevance_levels.get(&survivor).copied();
        let demoted_level = self
            .class_relevance_levels
            .get(&demoted)
            .copied()
            .map(|relevance_level| relevance_level.max(level));
        let propagated_level = match (survivor_level, demoted_level) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (Some(a), None) => Some(a),
            (None, Some(b)) => Some(b),
            (None, None) => None,
        };
        if let Some(propagated_level) = propagated_level
            && self.mark_class_relevant_internal(survivor, propagated_level)
        {
            if RELEVANCY_TRACE.load(std::sync::atomic::Ordering::Relaxed)
                || std::env::var("SUNDANCE_RELEVANCY_TRACE").is_ok()
            {
                eprintln!(
                    "[relevancy] class_root {} promoted to relevant on merge with {} (level={})",
                    survivor, demoted, propagated_level
                );
            }
        }
    }

    fn notify_assignment(&mut self, lit: i32, level: usize) -> bool {
        if !self.enabled {
            return true;
        }
        self.ensure_capacity(lit);
        let idx = lit.unsigned_abs() as usize;

        let polarity = if lit > 0 { 1 } else { -1 };
        debug_assert!(
            self.assignments[idx] == 0 || self.assignments[idx] == polarity,
            "SAT variable {} was assigned both polarities without a backtrack",
            idx
        );
        self.assignments[idx] = polarity;
        self.assignment_levels[idx] =
            Some(self.assignment_levels[idx].map_or(level, |old_level| old_level.min(level)));
        let assignment_level = self.assignment_levels[idx].unwrap_or(level);

        let positive = lit > 0;
        let targets: Vec<LitWatch> = if positive {
            self.watches_on_true[idx].clone()
        } else {
            self.watches_on_false[idx].clone()
        };
        for watch in targets {
            if let Some(parent_level) = self.relevance_level(watch.parent_idx) {
                self.mark_relevant(watch.target, parent_level.max(assignment_level));
            }
        }

        let cond_targets: Vec<CondWatch> = if positive {
            self.cond_watches_on_true[idx].clone()
        } else {
            self.cond_watches_on_false[idx].clone()
        };
        if !cond_targets.is_empty() && std::env::var("SUNDANCE_RELEVANCY_TRACE").is_ok() {
            eprintln!(
                "[relevancy] cond_watch fired: lit={} → re-evaluate nodes {:?} (level={})",
                lit, cond_targets, level
            );
        }
        for watch in cond_targets {
            if let Some(parent_level) = self.relevance_level(watch.parent_idx) {
                self.queue
                    .push_back((watch.parent_idx as i32, parent_level.max(assignment_level)));
            }
        }

        let term_watches = self.term_ite_watches[idx].clone();
        for watch in term_watches {
            if let Some(&parent_level) = self.relevant_term_levels.get(&watch.parent_uid) {
                let branch_uid = if self.lit_is_true(watch.cond) {
                    watch.then_uid
                } else {
                    watch.else_uid
                };
                self.mark_term_relevant_internal(branch_uid, parent_level.max(assignment_level));
            }
        }

        if self.relevant[idx] {
            self.propagate_node(idx);
        }

        self.propagate();
        self.relevant[idx]
    }

    fn backtrack_to(&mut self, level: usize) {
        if !self.enabled {
            return;
        }
        for idx in 0..self.relevance_levels.len() {
            if self.relevance_levels[idx].is_some_and(|mark_level| mark_level > level) {
                self.relevance_levels[idx] = None;
                self.relevant[idx] = false;
            }
            if self.branch_levels[idx].is_some_and(|mark_level| mark_level > level) {
                self.branch_levels[idx] = None;
                self.branch_choices[idx] = None;
            }
            if self.assignment_levels[idx].is_some_and(|mark_level| mark_level > level) {
                self.assignment_levels[idx] = None;
                self.assignments[idx] = 0;
            }
            self.watches_on_true[idx].retain(|watch| watch.level <= level);
            self.watches_on_false[idx].retain(|watch| watch.level <= level);
            self.cond_watches_on_true[idx].retain(|watch| watch.level <= level);
            self.cond_watches_on_false[idx].retain(|watch| watch.level <= level);
            self.term_ite_watches[idx].retain(|watch| watch.level <= level);
        }
        self.relevant_term_levels
            .retain(|_, mark_level| *mark_level <= level);
        self.class_relevance_levels
            .retain(|_, mark_level| *mark_level <= level);
        self.class_relevant
            .retain(|root| self.class_relevance_levels.contains_key(root));
        self.queue.clear();
        self.lits_for_term_propagation.clear();
        self.newly_relevant_lits.clear();
        self.newly_relevant_terms.clear();
        self.newly_relevant_classes.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::{NodeKind, RelevancyState, RelevancyTrait};

    #[test]
    fn ite_condition_selects_branch_independent_of_ite_value() {
        let mut state = RelevancyState::new(true);
        state.register_node(
            1,
            NodeKind::Ite {
                cond: 2,
                then_lit: 3,
                else_lit: 4,
            },
        );
        state.mark_relevant_root(1, None, 0);

        // The ITE itself is false, but a true condition still selects `then`.
        state.notify_assignment(-1, 1);
        state.notify_assignment(2, 1);

        assert!(state.is_relevant(3));
        assert!(!state.is_relevant(4));
    }

    #[test]
    fn ite_false_condition_selects_else_branch() {
        let mut state = RelevancyState::new(true);
        state.register_node(
            1,
            NodeKind::Ite {
                cond: 2,
                then_lit: 3,
                else_lit: 4,
            },
        );
        state.mark_relevant_root(1, None, 0);
        state.notify_assignment(1, 1);
        state.notify_assignment(-2, 1);

        assert!(!state.is_relevant(3));
        assert!(state.is_relevant(4));
    }

    #[test]
    fn lower_relevance_level_survives_backtrack() {
        let mut state = RelevancyState::new(true);
        state.mark_relevant_root(1, None, 3);
        state.mark_relevant_root(1, None, 0);

        state.backtrack_to(0);

        assert!(state.is_relevant(1));
    }

    #[test]
    fn assignment_keeps_earliest_level() {
        let mut state = RelevancyState::new(true);
        state.notify_assignment(1, 3);
        state.notify_assignment(1, 0);

        state.backtrack_to(0);

        assert_eq!(state.lit_truth(1), Some(true));
    }

    #[test]
    fn watches_are_deduplicated_lowered_and_trailed() {
        let mut state = RelevancyState::new(true);
        state.register_node(
            1,
            NodeKind::Ite {
                cond: 2,
                then_lit: 3,
                else_lit: 4,
            },
        );

        state.mark_relevant_root(1, None, 3);
        state.mark_relevant_root(1, None, 1);

        assert_eq!(state.watches_on_true[2].len(), 1);
        assert_eq!(state.watches_on_false[2].len(), 1);
        assert_eq!(state.watches_on_true[2][0].level, 1);
        assert_eq!(state.watches_on_false[2][0].level, 1);

        state.backtrack_to(1);
        assert_eq!(state.watches_on_true[2].len(), 1);
        assert_eq!(state.watches_on_false[2].len(), 1);

        state.backtrack_to(0);
        assert!(state.watches_on_true[2].is_empty());
        assert!(state.watches_on_false[2].is_empty());
        state.notify_assignment(2, 0);
        assert!(!state.is_relevant(3));
    }

    #[test]
    fn or_true_keeps_the_first_relevant_branch() {
        let mut state = RelevancyState::new(true);
        state.register_node(1, NodeKind::Or(vec![2, 3]));
        state.mark_relevant_root(1, None, 0);
        state.notify_assignment(1, 0);

        state.notify_assignment(2, 1);
        state.notify_assignment(3, 2);

        assert!(state.is_relevant(2));
        assert!(!state.is_relevant(3));
    }
}
