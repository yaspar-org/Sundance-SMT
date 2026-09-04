// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Relevancy propagation engine for gating theory solver work.
//!
//! Implements the propagation rules from de Moura & Bjørner (2007) / Z3 internals §7.1.4.
//! The classification of terms into NodeKinds is done by SolverState; this module
//! only handles the propagation of relevancy through the registered structure.

use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::atomic::{AtomicBool, Ordering};

static RELEVANCY_TRACE: AtomicBool = AtomicBool::new(false);

pub fn init_relevancy_trace() {
    RELEVANCY_TRACE.store(
        std::env::var("SUNDANCE_RELEVANCY_TRACE").is_ok(),
        Ordering::Relaxed,
    );
}

#[inline]
pub(crate) fn relevancy_trace_enabled() -> bool {
    RELEVANCY_TRACE.load(Ordering::Relaxed)
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
pub(crate) enum RelevantMergeMembers {
    Survivor,
    Demoted,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct RelevantMergePropagation {
    pub members: RelevantMergeMembers,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RelevancyTrailEntry {
    RelevantLit(usize),
    BranchChoice(usize),
    Assignment(usize),
    RelevantTerm(u64),
    RelevantClass(u32),
    LitWatch {
        idx: usize,
        on_true: bool,
        parent_idx: usize,
        target: i32,
    },
    CondWatch {
        idx: usize,
        on_true: bool,
        parent_idx: usize,
    },
    TermIteWatch {
        idx: usize,
        parent_uid: u64,
        cond: i32,
        then_uid: u64,
        else_uid: u64,
    },
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
    /// After an egraph merge, update class relevancy and identify the one
    /// pre-merge member range, if any, that has just become relevant.
    fn propagate_class_relevancy(
        &mut self,
        survivor: u32,
        demoted: u32,
        level: usize,
    ) -> Option<RelevantMergePropagation>;
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
    /// Changes grouped by their earliest justification level. Entries made at
    /// level zero never need undo records. Lowering a state to an earlier
    /// level appends a new record there; the stale later-level record is
    /// ignored because backtracking verifies the state's current level.
    trail_by_level: Vec<Vec<RelevancyTrailEntry>>,
    enabled: bool,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct RelevancyProfile {
    pub(crate) nodes: usize,
    pub(crate) relevant_literals: usize,
    pub(crate) relevant_terms: usize,
    pub(crate) relevant_classes: usize,
    pub(crate) literal_watches: usize,
    pub(crate) conditional_watches: usize,
    pub(crate) term_ite_watches: usize,
    pub(crate) queued_events: usize,
    pub(crate) trail_entries: usize,
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
            trail_by_level: vec![Vec::new()],
            enabled,
        }
    }

    pub(crate) fn profile(&self) -> RelevancyProfile {
        RelevancyProfile {
            nodes: self.node_kinds.iter().filter(|kind| kind.is_some()).count(),
            relevant_literals: self.relevant.iter().filter(|relevant| **relevant).count(),
            relevant_terms: self.relevant_term_levels.len(),
            relevant_classes: self.class_relevant.len(),
            literal_watches: self
                .watches_on_true
                .iter()
                .chain(self.watches_on_false.iter())
                .map(Vec::len)
                .sum(),
            conditional_watches: self
                .cond_watches_on_true
                .iter()
                .chain(self.cond_watches_on_false.iter())
                .map(Vec::len)
                .sum(),
            term_ite_watches: self.term_ite_watches.iter().map(Vec::len).sum(),
            queued_events: self.queue.len()
                + self.lits_for_term_propagation.len()
                + self.newly_relevant_lits.len()
                + self.newly_relevant_terms.len()
                + self.newly_relevant_classes.len(),
            trail_entries: self.trail_by_level.iter().map(Vec::len).sum(),
        }
    }

    pub(crate) fn retire_terms(
        &mut self,
        term_uids: &HashSet<u64>,
        sat_vars: &HashSet<usize>,
        egraph_ids: &HashSet<u32>,
    ) {
        for &idx in sat_vars {
            if idx >= self.node_kinds.len() {
                continue;
            }
            self.node_kinds[idx] = None;
            self.node_polarity[idx] = 1;
            self.relevant[idx] = false;
            self.relevance_levels[idx] = None;
            self.branch_choices[idx] = None;
            self.branch_levels[idx] = None;
            self.assignments[idx] = 0;
            self.assignment_levels[idx] = None;
            self.watches_on_true[idx].clear();
            self.watches_on_false[idx].clear();
            self.cond_watches_on_true[idx].clear();
            self.cond_watches_on_false[idx].clear();
            self.term_ite_watches[idx].clear();
        }

        for watches in self
            .watches_on_true
            .iter_mut()
            .chain(self.watches_on_false.iter_mut())
        {
            watches.retain(|watch| {
                !sat_vars.contains(&watch.parent_idx)
                    && !sat_vars.contains(&(watch.target.unsigned_abs() as usize))
            });
        }
        for watches in self
            .cond_watches_on_true
            .iter_mut()
            .chain(self.cond_watches_on_false.iter_mut())
        {
            watches.retain(|watch| !sat_vars.contains(&watch.parent_idx));
        }
        for watches in &mut self.term_ite_watches {
            watches.retain(|watch| {
                !term_uids.contains(&watch.parent_uid)
                    && !term_uids.contains(&watch.then_uid)
                    && !term_uids.contains(&watch.else_uid)
                    && !sat_vars.contains(&(watch.cond.unsigned_abs() as usize))
            });
        }

        self.queue
            .retain(|(lit, _)| !sat_vars.contains(&(lit.unsigned_abs() as usize)));
        self.lits_for_term_propagation
            .retain(|event| !sat_vars.contains(&(event.lit.unsigned_abs() as usize)));
        self.newly_relevant_lits
            .retain(|event| !sat_vars.contains(&(event.lit.unsigned_abs() as usize)));
        self.relevant_term_levels
            .retain(|uid, _| !term_uids.contains(uid));
        self.newly_relevant_terms
            .retain(|event| !term_uids.contains(&event.uid));
        self.class_relevant
            .retain(|root| !egraph_ids.contains(root));
        self.class_relevance_levels
            .retain(|root, _| !egraph_ids.contains(root));
        self.newly_relevant_classes
            .retain(|event| !egraph_ids.contains(&event.root));

        for trail in &mut self.trail_by_level {
            trail.retain(|entry| match entry {
                RelevancyTrailEntry::RelevantLit(idx)
                | RelevancyTrailEntry::BranchChoice(idx)
                | RelevancyTrailEntry::Assignment(idx) => !sat_vars.contains(idx),
                RelevancyTrailEntry::RelevantTerm(uid) => !term_uids.contains(uid),
                RelevancyTrailEntry::RelevantClass(root) => !egraph_ids.contains(root),
                RelevancyTrailEntry::LitWatch {
                    idx,
                    parent_idx,
                    target,
                    ..
                } => {
                    !sat_vars.contains(idx)
                        && !sat_vars.contains(parent_idx)
                        && !sat_vars.contains(&(target.unsigned_abs() as usize))
                }
                RelevancyTrailEntry::CondWatch {
                    idx, parent_idx, ..
                } => !sat_vars.contains(idx) && !sat_vars.contains(parent_idx),
                RelevancyTrailEntry::TermIteWatch {
                    idx,
                    parent_uid,
                    cond,
                    then_uid,
                    else_uid,
                } => {
                    !sat_vars.contains(idx)
                        && !sat_vars.contains(&(cond.unsigned_abs() as usize))
                        && !term_uids.contains(parent_uid)
                        && !term_uids.contains(then_uid)
                        && !term_uids.contains(else_uid)
                }
            });
        }
    }

    fn record_trail(&mut self, level: usize, entry: RelevancyTrailEntry) {
        if level == 0 {
            return;
        }
        if self.trail_by_level.len() <= level {
            self.trail_by_level.resize_with(level + 1, Vec::new);
        }
        self.trail_by_level[level].push(entry);
    }

    fn mark_relevant(&mut self, lit: i32, level: usize) -> bool {
        self.ensure_capacity(lit);
        let idx = lit.unsigned_abs() as usize;
        let old_level = self.relevance_levels[idx];
        if old_level.is_some_and(|old| old <= level) {
            if relevancy_trace_enabled() {
                eprintln!(
                    "[relevancy] mark_relevant(lit={}, level={}) — already relevant at {:?}, no-op",
                    lit, level, old_level
                );
            }
            return false;
        }
        self.relevant[idx] = true;
        self.relevance_levels[idx] = Some(level);
        self.record_trail(level, RelevancyTrailEntry::RelevantLit(idx));
        self.queue.push_back((lit, level));
        let event = RelevantLitEvent { lit, level };
        self.lits_for_term_propagation.push_back(event);
        self.newly_relevant_lits.push_back(event);
        if relevancy_trace_enabled() {
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
        self.record_trail(level, RelevancyTrailEntry::RelevantTerm(uid));
        self.newly_relevant_terms
            .push_back(RelevantTermEvent { uid, level });
        true
    }

    fn mark_class_relevant_internal(&mut self, root: u32, level: usize, emit_event: bool) -> bool {
        if self
            .class_relevance_levels
            .get(&root)
            .is_some_and(|old| *old <= level)
        {
            return false;
        }
        self.class_relevant.insert(root);
        self.class_relevance_levels.insert(root, level);
        self.record_trail(level, RelevancyTrailEntry::RelevantClass(root));
        if emit_event {
            self.newly_relevant_classes
                .push_back(RelevantClassEvent { root, level });
        }
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
        self.record_trail(level, RelevancyTrailEntry::BranchChoice(idx));
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
                            if relevancy_trace_enabled() {
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
                        if relevancy_trace_enabled() {
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
                    if relevancy_trace_enabled() {
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
        let on_true = watched_lit > 0;
        let changed = {
            let watches = if on_true {
                &mut self.watches_on_true[idx]
            } else {
                &mut self.watches_on_false[idx]
            };
            Self::insert_lit_watch(watches, parent_idx, target, level)
        };
        if changed {
            self.record_trail(
                level,
                RelevancyTrailEntry::LitWatch {
                    idx,
                    on_true,
                    parent_idx,
                    target,
                },
            );
        }
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
        let on_true = watched_lit <= 0;
        let changed = {
            let watches = if on_true {
                &mut self.watches_on_true[idx]
            } else {
                &mut self.watches_on_false[idx]
            };
            Self::insert_lit_watch(watches, parent_idx, target, level)
        };
        if changed {
            self.record_trail(
                level,
                RelevancyTrailEntry::LitWatch {
                    idx,
                    on_true,
                    parent_idx,
                    target,
                },
            );
        }
    }

    fn insert_lit_watch(
        watches: &mut Vec<LitWatch>,
        parent_idx: usize,
        target: i32,
        level: usize,
    ) -> bool {
        if let Some(existing) = watches
            .iter_mut()
            .find(|watch| watch.parent_idx == parent_idx && watch.target == target)
        {
            if level < existing.level {
                existing.level = level;
                true
            } else {
                false
            }
        } else {
            watches.push(LitWatch {
                parent_idx,
                target,
                level,
            });
            true
        }
    }

    fn install_cond_true_watch(&mut self, watched_lit: i32, parent_idx: usize, level: usize) {
        self.ensure_capacity(watched_lit);
        let idx = watched_lit.unsigned_abs() as usize;
        let on_true = watched_lit > 0;
        let changed = {
            let watches = if on_true {
                &mut self.cond_watches_on_true[idx]
            } else {
                &mut self.cond_watches_on_false[idx]
            };
            Self::insert_cond_watch(watches, parent_idx, level)
        };
        if changed {
            self.record_trail(
                level,
                RelevancyTrailEntry::CondWatch {
                    idx,
                    on_true,
                    parent_idx,
                },
            );
        }
    }

    fn install_cond_false_watch(&mut self, watched_lit: i32, parent_idx: usize, level: usize) {
        self.ensure_capacity(watched_lit);
        let idx = watched_lit.unsigned_abs() as usize;
        let on_true = watched_lit <= 0;
        let changed = {
            let watches = if on_true {
                &mut self.cond_watches_on_true[idx]
            } else {
                &mut self.cond_watches_on_false[idx]
            };
            Self::insert_cond_watch(watches, parent_idx, level)
        };
        if changed {
            self.record_trail(
                level,
                RelevancyTrailEntry::CondWatch {
                    idx,
                    on_true,
                    parent_idx,
                },
            );
        }
    }

    fn insert_cond_watch(watches: &mut Vec<CondWatch>, parent_idx: usize, level: usize) -> bool {
        if let Some(existing) = watches
            .iter_mut()
            .find(|watch| watch.parent_idx == parent_idx)
        {
            if level < existing.level {
                existing.level = level;
                true
            } else {
                false
            }
        } else {
            watches.push(CondWatch { parent_idx, level });
            true
        }
    }

    fn undo_trail_entry(&mut self, entry: RelevancyTrailEntry, mark_level: usize) {
        match entry {
            RelevancyTrailEntry::RelevantLit(idx) => {
                if self.relevance_levels[idx] == Some(mark_level) {
                    self.relevance_levels[idx] = None;
                    self.relevant[idx] = false;
                }
            }
            RelevancyTrailEntry::BranchChoice(idx) => {
                if self.branch_levels[idx] == Some(mark_level) {
                    self.branch_levels[idx] = None;
                    self.branch_choices[idx] = None;
                }
            }
            RelevancyTrailEntry::Assignment(idx) => {
                if self.assignment_levels[idx] == Some(mark_level) {
                    self.assignment_levels[idx] = None;
                    self.assignments[idx] = 0;
                }
            }
            RelevancyTrailEntry::RelevantTerm(uid) => {
                if self.relevant_term_levels.get(&uid) == Some(&mark_level) {
                    self.relevant_term_levels.remove(&uid);
                }
            }
            RelevancyTrailEntry::RelevantClass(root) => {
                if self.class_relevance_levels.get(&root) == Some(&mark_level) {
                    self.class_relevance_levels.remove(&root);
                    self.class_relevant.remove(&root);
                }
            }
            RelevancyTrailEntry::LitWatch {
                idx,
                on_true,
                parent_idx,
                target,
            } => {
                let watches = if on_true {
                    &mut self.watches_on_true[idx]
                } else {
                    &mut self.watches_on_false[idx]
                };
                if let Some(pos) = watches.iter().position(|watch| {
                    watch.parent_idx == parent_idx
                        && watch.target == target
                        && watch.level == mark_level
                }) {
                    watches.remove(pos);
                }
            }
            RelevancyTrailEntry::CondWatch {
                idx,
                on_true,
                parent_idx,
            } => {
                let watches = if on_true {
                    &mut self.cond_watches_on_true[idx]
                } else {
                    &mut self.cond_watches_on_false[idx]
                };
                if let Some(pos) = watches
                    .iter()
                    .position(|watch| watch.parent_idx == parent_idx && watch.level == mark_level)
                {
                    watches.remove(pos);
                }
            }
            RelevancyTrailEntry::TermIteWatch {
                idx,
                parent_uid,
                cond,
                then_uid,
                else_uid,
            } => {
                if let Some(pos) = self.term_ite_watches[idx].iter().position(|watch| {
                    watch.parent_uid == parent_uid
                        && watch.cond == cond
                        && watch.then_uid == then_uid
                        && watch.else_uid == else_uid
                        && watch.level == mark_level
                }) {
                    self.term_ite_watches[idx].remove(pos);
                }
            }
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
            if relevancy_trace_enabled() {
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
            if self.mark_class_relevant_internal(root, level, true) {
                if relevancy_trace_enabled() {
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

    fn add_class_relevant(&mut self, class_root: u32, level: usize) {
        if !self.enabled {
            return;
        }
        if self.mark_class_relevant_internal(class_root, level, true) {
            if relevancy_trace_enabled() {
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
        let changed = if let Some(existing) = self.term_ite_watches[idx].iter_mut().find(|watch| {
            watch.parent_uid == parent_uid
                && watch.cond == cond
                && watch.then_uid == then_uid
                && watch.else_uid == else_uid
        }) {
            if level < existing.level {
                existing.level = level;
                true
            } else {
                false
            }
        } else {
            self.term_ite_watches[idx].push(TermIteWatch {
                parent_uid,
                cond,
                then_uid,
                else_uid,
                level,
            });
            true
        };
        if changed {
            self.record_trail(
                level,
                RelevancyTrailEntry::TermIteWatch {
                    idx,
                    parent_uid,
                    cond,
                    then_uid,
                    else_uid,
                },
            );
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

    fn propagate_class_relevancy(
        &mut self,
        survivor: u32,
        demoted: u32,
        level: usize,
    ) -> Option<RelevantMergePropagation> {
        if !self.enabled {
            return None;
        }
        let survivor_level = self.class_relevance_levels.get(&survivor).copied();
        let demoted_level = self.class_relevance_levels.get(&demoted).copied();
        let propagation = match (survivor_level, demoted_level) {
            (Some(source_level), None) => Some(RelevantMergePropagation {
                members: RelevantMergeMembers::Demoted,
                level: source_level.max(level),
            }),
            (None, Some(source_level)) => {
                let activation_level = source_level.max(level);
                self.mark_class_relevant_internal(survivor, activation_level, false);
                Some(RelevantMergePropagation {
                    members: RelevantMergeMembers::Survivor,
                    level: activation_level,
                })
            }
            (Some(_), Some(_)) | (None, None) => None,
        };
        if let Some(propagation) = propagation
            && relevancy_trace_enabled()
        {
            eprintln!(
                "[relevancy] class merge {} <- {} promotes {:?} members (level={})",
                survivor, demoted, propagation.members, propagation.level
            );
        }
        propagation
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
        let old_level = self.assignment_levels[idx];
        let assignment_level = old_level.map_or(level, |old| old.min(level));
        self.assignments[idx] = polarity;
        self.assignment_levels[idx] = Some(assignment_level);
        if old_level != Some(assignment_level) {
            self.record_trail(assignment_level, RelevancyTrailEntry::Assignment(idx));
        }

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
        if !cond_targets.is_empty() && relevancy_trace_enabled() {
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
        if level + 1 < self.trail_by_level.len() {
            for mark_level in ((level + 1)..self.trail_by_level.len()).rev() {
                let entries = std::mem::take(&mut self.trail_by_level[mark_level]);
                for entry in entries.into_iter().rev() {
                    self.undo_trail_entry(entry, mark_level);
                }
            }
            self.trail_by_level.truncate(level + 1);
        }
        self.queue.clear();
        self.lits_for_term_propagation.clear();
        self.newly_relevant_lits.clear();
        self.newly_relevant_terms.clear();
        self.newly_relevant_classes.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::{
        NodeKind, RelevancyState, RelevancyTrait, RelevantMergeMembers, RelevantMergePropagation,
    };

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
    fn lowered_mark_does_not_hide_unrelated_backtrack_work() {
        let mut state = RelevancyState::new(true);
        state.mark_relevant_root(1, None, 3);
        state.mark_relevant_root(2, None, 3);
        state.mark_relevant_root(1, None, 0);

        state.backtrack_to(0);

        assert!(state.is_relevant(1));
        assert!(!state.is_relevant(2));
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

    #[test]
    fn relevant_class_merge_promotes_only_new_members_at_merge_level() {
        let mut state = RelevancyState::new(true);
        state.add_class_relevant(10, 0);
        assert_eq!(state.drain_newly_relevant_classes().len(), 1);

        assert_eq!(
            state.propagate_class_relevancy(10, 11, 2),
            Some(RelevantMergePropagation {
                members: RelevantMergeMembers::Demoted,
                level: 2,
            })
        );
        assert!(state.drain_newly_relevant_classes().is_empty());

        assert_eq!(
            state.propagate_class_relevancy(12, 10, 3),
            Some(RelevantMergePropagation {
                members: RelevantMergeMembers::Survivor,
                level: 3,
            })
        );
        assert!(state.class_relevant.contains(&12));
        assert!(state.drain_newly_relevant_classes().is_empty());
    }
}
