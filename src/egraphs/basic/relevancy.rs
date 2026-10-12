// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Relevancy and incremental e-matching for the basic e-graph.
//!
//! The same semantics as the semper adapter's (`egraphs/semper/mod.rs`,
//! "Relevancy" and "Incremental matching"), on the basic backend's own
//! stores. Z3's relevancy (`smt_relevancy.cpp`): a term is relevant once
//! relevancy reaches it; the rules, applied when a term is marked, at every
//! assignment of a relevant gate or of a child of one, and re-applied to
//! every relevant gate at the start of each filtered round:
//!   and = true, or = false, implies = false: every child;
//!   and = false / or = true: one witness, none if a witness is already
//!     relevant, else the first child in child order with that value;
//!   implies = true: a if a is false, else b if b is true;
//!   ite: both branches in one class -> the branches; otherwise the
//!     condition and the taken branch;
//!   any other application or equality: every argument;
//!   opaque terms (quantifiers): relevancy stops.
//! Closure: marking a term marks its class, and a merge with one relevant
//! side marks the merged class, except the true and false classes, which
//! every assigned atom joins. Seeds: the level-0 asserted atoms and every
//! quantifier instance body once true. Marks are undone on backtrack, as
//! Z3's are: the basic e-graph keeps every term across backtracks, so the
//! marks carry their own trail.
//!
//! Incremental matching (`SUNDANCE_INCR_MATCH=1`, `--incremental-matching`):
//! a round matches a trigger only at root candidates whose class, or a class
//! within the pattern's depth below it, gained a term, a member or a mark
//! since the previous round, Z3's `mam::add_eq_eh` seeding. Every match a
//! full scan finds that the previous round could not have found involves
//! such a candidate, so the filtered round yields the same new instances.
//! `SUNDANCE_INCR_MATCH_DIFF=1` runs the full scan too and reports the
//! misses.

use super::egraph::Egraph;
use super::repr::{Op, Pattern, PatternId, TermSlot};
use crate::utils::{DeterministicHashMap, FastDeterministicHashMap, FastDeterministicHashSet};
use std::sync::atomic::{AtomicU64, Ordering};
use yaspar_ir::ast::Local;

/// `SEMPER_RELEVANCY=1` (`--relevancy final|eager`): compute relevancy.
pub(super) fn rel_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("SEMPER_RELEVANCY").is_ok_and(|v| v == "1"))
}
/// `SEMPER_REL_NOFILTER=1`: compute relevancy but never let it decide.
fn rel_nofilter() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("SEMPER_REL_NOFILTER").is_some())
}
/// `SEMPER_REL_NOCLASS=1`: no closure over e-classes.
fn rel_noclass() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("SEMPER_REL_NOCLASS").is_some())
}
/// Seed true instance bodies; `SEMPER_REL_NO_SEED_INSTANCES=1` turns it off.
fn rel_seed_instances() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("SEMPER_REL_NO_SEED_INSTANCES").is_none())
}
/// Marks at every assignment; `SEMPER_REL_NO_INCREMENTAL=1` leaves them to
/// the per-round refresh.
fn rel_incremental() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("SEMPER_REL_NO_INCREMENTAL").is_none())
}
/// Re-apply every relevant gate's rule at the start of a filtered round;
/// `SEMPER_REL_NO_GATE_RESCAN=1` turns it off.
fn rel_gate_rescan() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("SEMPER_REL_NO_GATE_RESCAN").is_none())
}
pub(super) fn incr_match() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("SUNDANCE_INCR_MATCH").is_some())
}
/// `SEMPER_REL_DECIDE=1`: relevancy-driven decisions (see `rel_suggest_decision`).
fn rel_decide() -> bool {
    rel_decide_mode() != 0
}
fn rel_decide_mode() -> u32 {
    static ON: std::sync::OnceLock<u32> = std::sync::OnceLock::new();
    *ON.get_or_init(|| {
        std::env::var("SEMPER_REL_DECIDE")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(0)
    })
}
fn incr_match_diff() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("SUNDANCE_INCR_MATCH_DIFF").is_some())
}

static REL_MARKS: AtomicU64 = AtomicU64::new(0);
static REL_ASSIGN_HOOKS: AtomicU64 = AtomicU64::new(0);
static REL_SKIPPED_CANDIDATES: AtomicU64 = AtomicU64::new(0);
static REL_SKIPPED_QUANTIFIERS: AtomicU64 = AtomicU64::new(0);
static INCR_SKIPPED: AtomicU64 = AtomicU64::new(0);
static INCR_CONSIDERED: AtomicU64 = AtomicU64::new(0);
static INCR_DIFF_CALLS: AtomicU64 = AtomicU64::new(0);
static INCR_DIFF_MISSED: AtomicU64 = AtomicU64::new(0);
static INCR_EMPTY_ROUNDS: AtomicU64 = AtomicU64::new(0);

/// Depth of a pattern: 0 for a variable or ground term, 1 + max over the
/// arguments for an application.
pub(super) fn pattern_depth(p: &Pattern) -> u32 {
    match p {
        Pattern::App(_, subs) => 1 + subs.iter().map(pattern_depth).max().unwrap_or(0),
        _ => 0,
    }
}

fn grow<T: Clone>(v: &mut Vec<T>, id: u32, fill: T) {
    if v.len() <= id as usize {
        v.resize(id as usize + 1, fill);
    }
}

/// Relevancy state of the basic e-graph. Every `Vec` indexed by term id grows
/// on demand (`grow`), since ids are assigned by the e-graph in order.
#[derive(Default)]
pub(super) struct Relevancy {
    pub(super) enabled: bool,
    /// Relevancy decides matching and instantiation in the current round.
    pub(super) active: bool,
    /// Per term: marked relevant.
    pub(super) mark: Vec<bool>,
    /// Marks in order with the level they were made at; a backtrack below
    /// that level clears them.
    trail: Vec<(u32, usize)>,
    queue: Vec<u32>,
    /// Relevant gates (and/or/implies/ite) with their level, for the
    /// per-round rescan; truncated on backtrack with the marks.
    gates: Vec<(u32, usize)>,
    /// child -> gate parents (built at registration while enabled).
    pub(super) gate_parents: Vec<Vec<u32>>,
    /// Level-0 asserted atoms, the seeds.
    roots: Vec<u32>,
    /// Instance bodies (`note_instance_root`) with their level.
    instance_roots: Vec<(u32, usize)>,
    instance_root_flag: Vec<bool>,
    /// Merges (surviving root, absorbed root) since the last absorb.
    pub(super) merge_log: Vec<(u32, u32)>,
    merge_cursor: usize,
    /// Relevant atoms in marking order with the polarity the marking gate
    /// needs (`want`), for the decision policy; scanned from `decide_cursor`,
    /// which a backtrack resets.
    decide_queue: Vec<(u32, bool)>,
    decide_cursor: std::cell::Cell<usize>,
}

/// Incremental matching state of the basic e-graph.
#[derive(Default)]
pub(super) struct Incremental {
    /// child -> every parent (built at registration while on).
    pub(super) parents: Vec<Vec<u32>>,
    /// Representative of every term at the previous round's start.
    snapshot: Vec<u32>,
    /// Terms marked relevant since the previous round.
    pub(super) newly_relevant: Vec<u32>,
    max_depth: u32,
    /// Pattern labels: (f, i, g) for an application g at argument i of f;
    /// (f, i) for a variable or a ground term at argument i of f; and the
    /// set of pattern operators.
    pc_pairs: FastDeterministicHashSet<(Op, u32, Op)>,
    pc_var: FastDeterministicHashSet<(Op, u32)>,
    pc_ground: FastDeterministicHashSet<(Op, u32)>,
    pattern_ops: FastDeterministicHashSet<Op>,
    /// This round's root candidates per function key, with the ancestor
    /// level at which they were reached (0 = seed).
    cands: FastDeterministicHashMap<String, Vec<(u32, u32)>>,
    pub(super) active: bool,
    round: u64,
    /// Round at which each pattern was last scanned.
    pub(super) last_scanned: FastDeterministicHashMap<PatternId, u64>,
    /// Diff mode: every match produced so far per pattern.
    seen: FastDeterministicHashMap<PatternId, Vec<DeterministicHashMap<Local, u32>>>,
    /// Diagnostic: this round's seeds and renamed terms (term, old rep, new rep).
    last_seeds: Vec<u32>,
    last_renamed: Vec<(u32, u32, u32)>,
    /// Roots touched by a union or by the undo of a union since the last round.
    pub(super) touched: Vec<u32>,
    /// The last `incr_begin_round` found no change.
    empty_round: bool,
}

impl Relevancy {
    pub(super) fn new(enabled: bool) -> Self {
        Relevancy {
            enabled,
            ..Default::default()
        }
    }
}

impl Egraph {
    // --- registration and union hooks ----------------------------------

    /// Called by `register_term_internal` for an application term.
    pub(super) fn rel_register(&mut self, id: u32, op: &Op, children: &[u32]) {
        if incr_match() {
            for &c in children {
                grow(&mut self.incr.parents, c, Vec::new());
                self.incr.parents[c as usize].push(id);
            }
        }
        if self.rel.enabled {
            if let Op::Constant(name) = op {
                if name == "true" && self.true_id.is_none() {
                    self.true_id = Some(id);
                } else if name == "false" && self.false_id.is_none() {
                    self.false_id = Some(id);
                }
            }
            if Self::op_is_gate(op) {
                for &c in children {
                    grow(&mut self.rel.gate_parents, c, Vec::new());
                    self.rel.gate_parents[c as usize].push(id);
                }
            }
        }
    }

    /// Called by `cc_union` right after the union is performed, before any
    /// conflict check: the union stands until a backtrack undoes it, and the
    /// class lists and merge log must follow it either way.
    pub(super) fn rel_after_union(&mut self, x_root: u32, y_root: u32, level: usize) {
        grow(&mut self.next_in_class, x_root.max(y_root), u32::MAX);
        for r in [x_root, y_root] {
            if self.next_in_class[r as usize] == u32::MAX {
                self.next_in_class[r as usize] = r;
            }
        }
        self.next_in_class.swap(x_root as usize, y_root as usize);
        self.union_trail.push((level, x_root, y_root));
        if incr_match() {
            self.incr.touched.push(x_root);
            self.incr.touched.push(y_root);
        }
        if self.rel.enabled {
            self.rel.merge_log.push((x_root, y_root));
        }
    }

    /// Undo the class-list splices and the relevancy state above `level`.
    pub(super) fn rel_backtrack(&mut self, level: usize) {
        while let Some(&(l, a, b)) = self.union_trail.last() {
            if l <= level {
                break;
            }
            self.union_trail.pop();
            self.next_in_class.swap(a as usize, b as usize);
            if incr_match() {
                self.incr.touched.push(a);
                self.incr.touched.push(b);
            }
        }
        if !self.rel.enabled {
            return;
        }
        while let Some(&(t, l)) = self.rel.trail.last() {
            if l <= level {
                break;
            }
            self.rel.trail.pop();
            self.rel.mark[t as usize] = false;
        }
        while let Some(&(_, l)) = self.rel.gates.last() {
            if l <= level {
                break;
            }
            self.rel.gates.pop();
        }
        while let Some(&(t, l)) = self.rel.instance_roots.last() {
            if l <= level {
                break;
            }
            self.rel.instance_roots.pop();
            self.rel.instance_root_flag[t as usize] = false;
        }
        self.rel.queue.clear();
        self.rel.merge_log.clear();
        self.rel.merge_cursor = 0;
        // Candidates queued above `level` were marked above it; drop them
        // with the marks, and rescan from the start since atoms are unassigned.
        let keep = self
            .rel
            .decide_queue
            .iter()
            .rposition(|&(t, _)| self.rel_is_marked_strict(t))
            .map_or(0, |i| i + 1);
        self.rel.decide_queue.truncate(keep);
        self.rel.decide_cursor.set(0);
    }

    /// The members of `t`'s class, `t` first.
    pub(super) fn class_members(&self, t: u32) -> Vec<u32> {
        let mut out = vec![t];
        let mut cur = t;
        loop {
            let next = self
                .next_in_class
                .get(cur as usize)
                .copied()
                .unwrap_or(u32::MAX);
            if next == u32::MAX || next == t {
                break;
            }
            out.push(next);
            cur = next;
        }
        out
    }

    fn op_is_gate(op: &Op) -> bool {
        matches!(op, Op::And | Op::Or | Op::Implies | Op::Ite)
    }

    fn term_op_children(&self, t: u32) -> Option<(&Op, &[u32])> {
        match self.terms.get(t as usize) {
            Some(TermSlot::Term(e)) => Some((&e.op, e.children.as_slice())),
            _ => None,
        }
    }

    fn rel_is_gate(&self, t: u32) -> bool {
        self.term_op_children(t)
            .is_some_and(|(op, _)| Self::op_is_gate(op))
    }

    // --- relevancy ----------------------------------------------------------

    pub(super) fn rel_is_marked(&self, t: u32) -> bool {
        !self.rel.enabled || self.rel.mark.get(t as usize).copied().unwrap_or(false)
    }

    fn rel_is_truth_class(&self, t: u32) -> bool {
        let r = self.find(t);
        self.true_id.is_some_and(|x| self.find(x) == r)
            || self.false_id.is_some_and(|x| self.find(x) == r)
    }

    fn bool_value(&self, t: u32) -> Option<bool> {
        let r = self.find(t);
        if self.true_id.is_some_and(|x| self.find(x) == r) {
            Some(true)
        } else if self.false_id.is_some_and(|x| self.find(x) == r) {
            Some(false)
        } else {
            None
        }
    }

    fn rel_mark_one(&mut self, t: u32) -> bool {
        grow(&mut self.rel.mark, t, false);
        if self.rel.mark[t as usize] {
            return false;
        }
        self.rel.mark[t as usize] = true;
        self.rel.trail.push((t, self.decision_level));
        REL_MARKS.fetch_add(1, Ordering::Relaxed);
        if incr_match() {
            self.incr.newly_relevant.push(t);
        }
        self.rel.queue.push(t);
        true
    }

    /// Mark `t` relevant (and, under the closure, its whole class), queueing
    /// every newly marked term for rule application.
    pub(super) fn rel_mark(&mut self, t: u32) {
        self.rel_mark_pol(t, None);
    }

    /// `want`: the polarity the marking gate needs `t` to take, recorded for
    /// the decision policy when `t` is an atom (not a gate); a negation
    /// records its argument with the polarity flipped.
    fn rel_mark_pol(&mut self, t: u32, want: Option<bool>) {
        if !self.rel.enabled || !self.rel_mark_one(t) {
            return;
        }
        if let Some(w) = want
            && rel_decide()
        {
            match self.term_op_children(t) {
                Some((Op::Not, ch)) => {
                    if let Some(&c) = ch.first() {
                        self.rel_mark_pol(c, Some(!w));
                    }
                }
                Some((op, _)) if !Self::op_is_gate(op) => self.rel.decide_queue.push((t, w)),
                _ => {}
            }
        }
        if !rel_noclass() && !self.rel_is_truth_class(t) {
            self.rel_mark_class(t);
        }
    }

    fn rel_mark_class(&mut self, t: u32) {
        for m in self.class_members(t) {
            self.rel_mark_one(m);
        }
    }

    /// Apply the rule of the (relevant) term `t`: mark the children it makes
    /// relevant on the current assignment.
    fn rel_apply(&mut self, t: u32) {
        let Some((op, children)) = self.term_op_children(t) else {
            return;
        };
        let op = op.clone();
        let children: Vec<u32> = children.to_vec();
        match op {
            Op::And | Op::Or => match self.bool_value(t) {
                None => {}
                Some(v) => {
                    // A true `or` (false `and`) with no child of that value
                    // yet: nothing is relevant below it, but its first
                    // unassigned child is the decision that justifies it
                    // (Z3 case-splits it because the gate is relevant).
                    if rel_decide()
                        && (op == Op::And) != v
                        && !children.iter().any(|&c| self.bool_value(c) == Some(v))
                        && let Some(&c) = children.iter().find(|&&c| self.bool_value(c).is_none())
                    {
                        self.rel_queue_decision(c, v);
                    }
                    // and=true / or=false: every child; and=false / or=true:
                    // one witness with value `v`, none if one is relevant.
                    let all = (op == Op::And) == v;
                    if all {
                        for c in children {
                            self.rel_mark_pol(c, Some(v));
                        }
                    } else if !children
                        .iter()
                        .any(|&c| self.bool_value(c) == Some(v) && self.rel_is_marked(c))
                        && let Some(&w) = children.iter().find(|&&c| self.bool_value(c) == Some(v))
                    {
                        self.rel_mark_pol(w, Some(v));
                    }
                }
            },
            Op::Implies if children.len() == 2 => match self.bool_value(t) {
                Some(false) => {
                    self.rel_mark_pol(children[0], Some(true));
                    self.rel_mark_pol(children[1], Some(false));
                }
                Some(true) => {
                    if self.bool_value(children[0]) == Some(false) {
                        self.rel_mark_pol(children[0], Some(false));
                    } else if self.bool_value(children[1]) == Some(true) {
                        self.rel_mark_pol(children[1], Some(true));
                    }
                }
                None => {}
            },
            Op::Ite if children.len() == 3 => {
                if self.find(children[1]) == self.find(children[2]) {
                    self.rel_mark(children[1]);
                    self.rel_mark(children[2]);
                } else {
                    self.rel_mark(children[0]);
                    match self.bool_value(children[0]) {
                        Some(true) => self.rel_mark(children[1]),
                        Some(false) => self.rel_mark(children[2]),
                        None => {}
                    }
                }
            }
            _ => {
                for c in children {
                    self.rel_mark(c);
                }
            }
        }
    }

    /// Drain the mark queue, applying each newly marked term's rule; gates
    /// are remembered for the per-round rescan.
    fn rel_propagate(&mut self) {
        while let Some(t) = self.rel.queue.pop() {
            if self.rel_is_gate(t) {
                self.rel.gates.push((t, self.decision_level));
            }
            self.rel_apply(t);
        }
    }

    /// Carry relevancy across the merges since the last call (Z3's `add_eq`).
    fn rel_absorb_merges(&mut self) {
        if !self.rel.enabled {
            return;
        }
        if self.rel.merge_cursor > self.rel.merge_log.len() {
            self.rel.merge_cursor = 0;
        }
        if !rel_noclass() {
            let merges: Vec<(u32, u32)> = self.rel.merge_log[self.rel.merge_cursor..].to_vec();
            for (s, a) in merges {
                if (self.rel_is_marked(s) || self.rel_is_marked(a)) && !self.rel_is_truth_class(s) {
                    self.rel_mark_class(s);
                }
            }
        }
        self.rel.merge_cursor = self.rel.merge_log.len();
    }

    /// Bring the relevant set up to date with the current assignment at the
    /// start of a filtered round: merges, seeds, true instance bodies, the
    /// gate rescan.
    fn rel_refresh(&mut self) {
        if !self.rel.enabled {
            return;
        }
        self.rel_absorb_merges();
        // Nothing else reads the log: drop what was absorbed.
        self.rel.merge_log.clear();
        self.rel.merge_cursor = 0;
        let roots = self.rel.roots.clone();
        for t in roots {
            self.rel_mark(t);
        }
        if rel_seed_instances() {
            let inst: Vec<u32> = self.rel.instance_roots.iter().map(|&(t, _)| t).collect();
            for t in inst {
                if self.bool_value(t) == Some(true) {
                    self.rel_mark(t);
                }
            }
        }
        self.rel_propagate();
        if rel_gate_rescan() {
            let gates: Vec<u32> = self.rel.gates.iter().map(|&(g, _)| g).collect();
            for g in gates {
                self.rel_apply(g);
            }
            self.rel_propagate();
        }
    }

    /// `t` was just given a truth value: carry the merges, mark it if it is
    /// a true instance body, re-apply its own rule if it is a relevant gate
    /// and the rule of every relevant gate it is a child of, propagate.
    pub(super) fn rel_on_assignment(&mut self, t: u32) {
        if !self.rel.enabled || !rel_incremental() {
            return;
        }
        REL_ASSIGN_HOOKS.fetch_add(1, Ordering::Relaxed);
        self.rel_absorb_merges();
        if rel_seed_instances()
            && self
                .rel
                .instance_root_flag
                .get(t as usize)
                .copied()
                .unwrap_or(false)
            && self.bool_value(t) == Some(true)
        {
            self.rel_mark(t);
        }
        if self.rel_is_marked_strict(t) && self.rel_is_gate(t) {
            self.rel_apply(t);
        }
        if let Some(parents) = self.rel.gate_parents.get(t as usize) {
            let parents = parents.clone();
            for g in parents {
                if self.rel_is_marked_strict(g) {
                    self.rel_apply(g);
                }
            }
        }
        self.rel_propagate();
    }

    fn rel_is_marked_strict(&self, t: u32) -> bool {
        self.rel.mark.get(t as usize).copied().unwrap_or(false)
    }

    /// A level-0 assertion of the shape "Boolean atom asserted to a truth
    /// value": the non-constant endpoint is a root. Z3 marks an assertion
    /// relevant when it is asserted (`internalize_assertion`).
    pub(super) fn rel_seed_root_if_boolean(&mut self, t1: u32, t2: u32) {
        if self.decision_level != 0 {
            return;
        }
        let is_tf = |t: u32| Some(t) == self.true_id || Some(t) == self.false_id;
        let root = if is_tf(t2) && !is_tf(t1) {
            t1
        } else if is_tf(t1) && !is_tf(t2) {
            t2
        } else {
            return;
        };
        self.rel.roots.push(root);
        if self.rel.enabled && rel_incremental() {
            self.rel_mark(root);
            self.rel_propagate();
        }
    }

    /// Whether relevancy decides matching in the current round.
    fn rel_filtering(&self) -> bool {
        self.rel.enabled && self.rel.active && !rel_nofilter()
    }

    /// Whether candidate `t` is hidden from the matcher this round.
    pub(super) fn rel_shielded(&self, t: u32) -> bool {
        let s = self.rel_filtering() && !self.rel_is_marked_strict(t);
        if s {
            REL_SKIPPED_CANDIDATES.fetch_add(1, Ordering::Relaxed);
        }
        s
    }

    pub(super) fn rel_note_instance_root(&mut self, t: u32) {
        if !self.rel.enabled {
            return;
        }
        grow(&mut self.rel.instance_root_flag, t, false);
        if !self.rel.instance_root_flag[t as usize] {
            self.rel.instance_root_flag[t as usize] = true;
            self.rel.instance_roots.push((t, self.decision_level));
        }
    }

    pub(super) fn rel_set_active(&mut self, active: bool) {
        let was = self.rel_filtering();
        self.rel.active = active;
        if !self.rel.enabled {
            return;
        }
        // SUNDANCE_REL_PROBE=<substring>: at every filtered round, count the
        // terms whose printed form contains the substring, marked against
        // unmarked, with their Boolean value (diagnostic, prints every round).
        if active && let Some(sub) = std::env::var_os("SUNDANCE_REL_PROBE") {
            let sub = sub.to_string_lossy().to_string();
            let (mut marked, mut unmarked, mut t, mut f, mut u) = (0, 0, 0, 0, 0);
            for id in 0..self.next_id {
                if !matches!(
                    self.terms.get(id as usize),
                    Some(TermSlot::Term(_) | TermSlot::Opaque)
                ) {
                    continue;
                }
                let d = self.display_term(id);
                if !d.contains(&sub) {
                    continue;
                }
                if self.rel_is_marked_strict(id) {
                    marked += 1
                } else {
                    unmarked += 1
                }
                match self.bool_value(id) {
                    Some(true) => t += 1,
                    Some(false) => f += 1,
                    None => u += 1,
                }
            }
            eprintln!(
                "REL_PROBE level={} sub={sub} marked={marked} unmarked={unmarked} true={t} false={f} unassigned={u}",
                self.decision_level
            );
        }
        // Shield going off: every term becomes matchable without a mark, so
        // the incremental matcher scans every pattern in full.
        if was && !self.rel_filtering() {
            self.incr.last_scanned.clear();
        }
        if active {
            self.rel_refresh();
        }
    }

    pub(super) fn rel_is_term_relevant(&self, t: u32) -> bool {
        let r = !self.rel_filtering() || self.rel_is_marked_strict(t);
        if !r {
            REL_SKIPPED_QUANTIFIERS.fetch_add(1, Ordering::Relaxed);
        }
        r
    }

    // --- relevancy-driven decisions (SEMPER_REL_DECIDE=1) ---------------------
    //
    // Z3's relevancy decides the search as well as the matcher: with
    // `smt.relevancy=2` only relevant atoms are candidates for a case split,
    // so the guard atoms of the top-level gates are assigned before anything
    // else. On role.7 under relevancy eager without this, the 194 fuel guard
    // atoms `(fuel_bool f)` are never decided by CaDiCaL's own heuristic in
    // 30 s (REL_PROBE: 388 unassigned at every level), so the guarded axioms'
    // literals stay unassigned and 42 quantifiers are never instantiated.
    // The policy descends the relevant Boolean structure from the level-0
    // roots with the desired polarity and returns the first unassigned atom
    // whose assignment justifies an unsatisfied relevant gate (the semper
    // adapter's `suggest_rec`, same cases).

    /// Queue `t` (an atom, or the argument of a negation with the polarity
    /// flipped) as a decision candidate with polarity `want`.
    fn rel_queue_decision(&mut self, t: u32, want: bool) {
        match self.term_op_children(t) {
            Some((Op::Not, ch)) => {
                if let Some(&c) = ch.first() {
                    self.rel_queue_decision(c, !want);
                }
            }
            Some((op, _)) if !Self::op_is_gate(op) => self.rel.decide_queue.push((t, want)),
            _ => {}
        }
    }

    /// `SEMPER_REL_DECIDE=1`: the first queued candidate still unassigned,
    /// from the cursor; `=2`: the descent from the roots (the semper
    /// adapter's policy, O(relevant structure) per decision).
    pub(super) fn rel_suggest_decision(&self) -> Option<(u32, bool)> {
        if !self.rel.enabled || !rel_decide() {
            return None;
        }
        if rel_decide_mode() == 1 {
            let mut i = self.rel.decide_cursor.get();
            let mut out = None;
            while i < self.rel.decide_queue.len() {
                let (t, w) = self.rel.decide_queue[i];
                if self.bool_value(t).is_none() {
                    out = Some((t, w));
                    break;
                }
                i += 1;
            }
            self.rel.decide_cursor.set(i);
            if std::env::var_os("SUNDANCE_REL_DECIDE_TRACE").is_some()
                && let Some((t, w)) = out
            {
                eprintln!(
                    "REL_DECIDE level={} term={} want={w} queue={}",
                    self.decision_level,
                    self.display_term(t),
                    self.rel.decide_queue.len()
                );
            }
            return out;
        }
        let mut visited: FastDeterministicHashSet<(u32, bool)> =
            FastDeterministicHashSet::default();
        for &r in &self.rel.roots {
            if let Some(d) = self.suggest_rec(r, true, &mut visited) {
                return Some(d);
            }
        }
        None
    }

    fn suggest_rec(
        &self,
        t: u32,
        want: bool,
        visited: &mut FastDeterministicHashSet<(u32, bool)>,
    ) -> Option<(u32, bool)> {
        if !visited.insert((t, want)) {
            return None;
        }
        let val = self.bool_value(t);
        if val == Some(!want) {
            return None;
        }
        let (op, children) = self.term_op_children(t)?;
        let children: Vec<u32> = children.to_vec();
        let is_true = |c: u32| self.bool_value(c) == Some(true);
        let is_false = |c: u32| self.bool_value(c) == Some(false);
        match op {
            Op::And => {
                if want {
                    children
                        .iter()
                        .find_map(|&c| self.suggest_rec(c, true, visited))
                } else if children.iter().any(|&c| is_false(c)) {
                    None
                } else {
                    children
                        .iter()
                        .find_map(|&c| self.suggest_rec(c, false, visited))
                }
            }
            Op::Or => {
                if want {
                    if children.iter().any(|&c| is_true(c)) {
                        None
                    } else {
                        children
                            .iter()
                            .find_map(|&c| self.suggest_rec(c, true, visited))
                    }
                } else {
                    children
                        .iter()
                        .find_map(|&c| self.suggest_rec(c, false, visited))
                }
            }
            Op::Not => children
                .first()
                .and_then(|&c| self.suggest_rec(c, !want, visited)),
            Op::Implies if children.len() == 2 => {
                let (a, b) = (children[0], children[1]);
                if want {
                    if is_false(a) || is_true(b) {
                        None
                    } else {
                        self.suggest_rec(a, false, visited)
                            .or_else(|| self.suggest_rec(b, true, visited))
                    }
                } else {
                    self.suggest_rec(a, true, visited)
                        .or_else(|| self.suggest_rec(b, false, visited))
                }
            }
            Op::Ite if children.len() == 3 => match self.bool_value(children[0]) {
                None => self.suggest_rec(children[0], true, visited),
                Some(true) => self.suggest_rec(children[1], want, visited),
                Some(false) => self.suggest_rec(children[2], want, visited),
            },
            _ => {
                if val.is_none() {
                    Some((t, want))
                } else {
                    None
                }
            }
        }
    }

    // --- incremental matching ----------------------------------------------

    pub(super) fn incr_compile_pattern(&mut self, pattern: &Pattern) {
        self.incr.max_depth = self.incr.max_depth.max(pattern_depth(pattern));
        fn labels(p: &Pattern, inc: &mut Incremental) {
            if let Pattern::App(f, subs) = p {
                inc.pattern_ops.insert(f.clone());
                for (i, sub) in subs.iter().enumerate() {
                    match sub {
                        Pattern::App(g, _) => {
                            inc.pc_pairs.insert((f.clone(), i as u32, g.clone()));
                        }
                        Pattern::Var(_) => {
                            inc.pc_var.insert((f.clone(), i as u32));
                        }
                        Pattern::Ground(_) => {
                            inc.pc_ground.insert((f.clone(), i as u32));
                        }
                    }
                    labels(sub, inc);
                }
            }
        }
        labels(pattern, &mut self.incr);
    }

    /// Snapshot the round: seeds (new terms, newly relevant terms, parents of
    /// renamed or split class members by pattern label), their class-aware
    /// ancestors up to the deepest pattern, grouped per function key.
    pub(super) fn incr_begin_round(&mut self) {
        // Change-driven (Z3's `mam::add_eq_eh` is O(changes)): the classes
        // whose representative may have changed since the previous round are
        // those of the roots touched by a union or by the undo of a union
        // (`incr.touched`), so renamed members and splits are computed over
        // the members of those classes only; the previous version recomputed
        // every term's representative (24% of an eager round on role.7).
        // When nothing changed
        // (no new term, no touched class, no new mark) the round is empty:
        // no pattern scanned in the previous real round can have a new match.
        let n = self.next_id as usize;
        let old_n = self.incr.snapshot.len();
        let touched = std::mem::take(&mut self.incr.touched);
        let newly = std::mem::take(&mut self.incr.newly_relevant);
        if old_n == n && touched.is_empty() && newly.is_empty() && self.incr.active {
            self.incr.empty_round = true;
            INCR_EMPTY_ROUNDS.fetch_add(1, Ordering::Relaxed);
            return;
        }
        self.incr.empty_round = false;
        // Members of every touched class, once each.
        let mut touched_terms: Vec<u32> = Vec::new();
        let mut seen_rep: FastDeterministicHashSet<u32> = FastDeterministicHashSet::default();
        for &r in &touched {
            let z = self.find(r);
            if seen_rep.insert(z) {
                touched_terms.extend(self.class_members(z));
            }
        }
        if old_n == 0 {
            // First round: every term is new; nothing to diff.
            touched_terms.clear();
        }
        let op_of = |s: &Self, t: u32| s.term_op_children(t).map(|(op, _)| op.clone());
        let old_rep = |s: &Self, t: u32| -> u32 {
            if (t as usize) < old_n {
                s.incr.snapshot[t as usize]
            } else {
                u32::MAX - t
            }
        };
        let mut seeds: Vec<u32> = (old_n as u32..n as u32).collect();
        seeds.extend(newly.into_iter().filter(|&t| (t as usize) < n));
        let seed_parents = |s: &Self,
                            m: u32,
                            other_ops: &FastDeterministicHashSet<Op>,
                            vars: bool,
                            out: &mut Vec<u32>| {
            let Some(ps) = s.incr.parents.get(m as usize) else {
                return;
            };
            for &p in ps {
                let Some((f, pch)) = s.term_op_children(p) else {
                    continue;
                };
                if !s.incr.pattern_ops.contains(f) {
                    continue;
                }
                let hit = pch.iter().enumerate().any(|(i, &c)| {
                    c == m
                        && ((vars && s.incr.pc_var.contains(&(f.clone(), i as u32)))
                            || s.incr.pc_ground.contains(&(f.clone(), i as u32))
                            || other_ops.iter().any(|g| {
                                s.incr.pc_pairs.contains(&(f.clone(), i as u32, g.clone()))
                            }))
                });
                if hit {
                    out.push(p);
                }
            }
        };
        // Merged classes among the touched ones: a class with a member whose
        // representative changed. Every member seeds its parents against the
        // operators of the members that had a different representative in
        // the previous round (new terms count as their own class).
        let mut by_new: FastDeterministicHashMap<u32, Vec<u32>> =
            FastDeterministicHashMap::default();
        for &t in &touched_terms {
            by_new.entry(self.find(t)).or_default().push(t);
        }
        let mut renamed_dbg: Vec<(u32, u32, u32)> = Vec::new();
        for (&z, all) in &by_new {
            let any_renamed = all
                .iter()
                .any(|&t| (t as usize) >= old_n || self.incr.snapshot[t as usize] != z);
            if !any_renamed {
                continue;
            }
            // Members grouped by their previous-round class, the operator
            // set of each group computed once: per member it was a scan of
            // the whole class, O(class size squared) per round, which on the
            // true class (every assigned atom) was 90% of an eager round.
            let mut groups: FastDeterministicHashMap<u32, Vec<u32>> =
                FastDeterministicHashMap::default();
            for &m in all {
                if (m as usize) < old_n && self.incr.snapshot[m as usize] != z {
                    renamed_dbg.push((m, self.incr.snapshot[m as usize], z));
                }
                groups.entry(old_rep(self, m)).or_default().push(m);
            }
            let group_ops: Vec<(u32, FastDeterministicHashSet<Op>)> = groups
                .iter()
                .map(|(&o, ms)| (o, ms.iter().filter_map(|&t| op_of(self, t)).collect()))
                .collect();
            for (o, ms) in &groups {
                let mut other_ops: FastDeterministicHashSet<Op> =
                    FastDeterministicHashSet::default();
                for (o2, ops) in &group_ops {
                    if o2 != o {
                        other_ops.extend(ops.iter().cloned());
                    }
                }
                if other_ops.is_empty() && self.incr.pc_ground.is_empty() {
                    continue;
                }
                for &m in ms {
                    seed_parents(self, m, &other_ops, true, &mut seeds);
                }
            }
        }
        // Splits among the touched terms: members of one previous-round
        // class now in several classes.
        let mut by_old: FastDeterministicHashMap<u32, Vec<u32>> =
            FastDeterministicHashMap::default();
        for &t in &touched_terms {
            if (t as usize) < old_n {
                by_old
                    .entry(self.incr.snapshot[t as usize])
                    .or_default()
                    .push(t);
            }
        }
        for (_, group) in by_old {
            let mut parts: FastDeterministicHashMap<u32, Vec<u32>> =
                FastDeterministicHashMap::default();
            for &t in &group {
                parts.entry(self.find(t)).or_default().push(t);
            }
            if parts.len() < 2 {
                continue;
            }
            let all_ops: Vec<(u32, FastDeterministicHashSet<Op>)> = parts
                .iter()
                .map(|(&z, ms)| (z, ms.iter().filter_map(|&t| op_of(self, t)).collect()))
                .collect();
            for (z, ms) in &parts {
                let mut other_ops: FastDeterministicHashSet<Op> =
                    FastDeterministicHashSet::default();
                for (z2, ops) in &all_ops {
                    if z2 != z {
                        other_ops.extend(ops.iter().cloned());
                    }
                }
                for &m in ms {
                    seed_parents(self, m, &other_ops, true, &mut seeds);
                }
            }
        }
        // Class-aware ancestors, by level.
        let mut level_of: FastDeterministicHashMap<u32, u32> = FastDeterministicHashMap::default();
        let mut frontier: Vec<u32> = Vec::new();
        for t in seeds {
            if level_of.insert(t, 0).is_none() {
                frontier.push(t);
            }
        }
        let mut expanded: FastDeterministicHashSet<u32> = FastDeterministicHashSet::default();
        for k in 1..=self.incr.max_depth {
            let mut next = Vec::new();
            for &u in &frontier {
                let name = self.find(u);
                if !expanded.insert(name) {
                    continue;
                }
                for m in self.class_members(name) {
                    let Some(ps) = self.incr.parents.get(m as usize) else {
                        continue;
                    };
                    for &p in ps {
                        if op_of(self, p).is_some_and(|f| self.incr.pattern_ops.contains(&f))
                            && !level_of.contains_key(&p)
                        {
                            level_of.insert(p, k);
                            next.push(p);
                        }
                    }
                }
            }
            frontier = next;
        }
        self.incr.last_seeds = level_of
            .iter()
            .filter(|&(_, &l)| l == 0)
            .map(|(&t, _)| t)
            .collect();
        self.incr.last_renamed = renamed_dbg;
        self.incr.cands.clear();
        for (&t, &lvl) in &level_of {
            if let Some((op, _)) = self.term_op_children(t) {
                self.incr
                    .cands
                    .entry(op.to_function_map_key())
                    .or_default()
                    .push((t, lvl));
            }
        }
        for v in self.incr.cands.values_mut() {
            v.sort_unstable();
        }
        // Snapshot: representatives of the touched members and of the new
        // terms; every other term's representative is unchanged.
        self.incr.snapshot.resize(n, u32::MAX);
        for &t in &touched_terms {
            self.incr.snapshot[t as usize] = self.find(t);
        }
        for t in old_n..n {
            self.incr.snapshot[t] = self.find(t as u32);
        }
        self.incr.active = true;
        self.incr.round += 1;
    }

    /// The round's root candidates for `func_key` at or below `depth`, plus
    /// every term registered since the snapshot (ids are increasing).
    pub(super) fn incr_candidates(&self, func_key: &str, depth: u32, all: usize) -> Vec<u32> {
        let mut cs: Vec<u32> = self
            .incr
            .cands
            .get(func_key)
            .map(|v| {
                v.iter()
                    .filter(|&&(_, l)| l <= depth)
                    .map(|&(t, _)| t)
                    .collect()
            })
            .unwrap_or_default();
        let since = self.incr.snapshot.len() as u32;
        if let Some(list) = self.function_maps.get(func_key) {
            let start = list.partition_point(|&(t, _)| t < since);
            cs.extend(list[start..].iter().map(|&(t, _)| t));
        }
        INCR_CONSIDERED.fetch_add(cs.len() as u64, Ordering::Relaxed);
        INCR_SKIPPED.fetch_add(all.saturating_sub(cs.len()) as u64, Ordering::Relaxed);
        cs
    }

    /// Whether this call filters: incremental matching is on, a round has
    /// started, and the first pattern was scanned in the previous round (so
    /// the diff since then is exact); records the scan.
    /// `None`: skip the call, the round is empty and the pattern was scanned
    /// in the last real round, so no new match exists (checked by the diff
    /// mode, which never skips). `Some(filter)` otherwise.
    pub(super) fn incr_filter_for(&mut self, first: PatternId) -> Option<bool> {
        if !incr_match() || !self.incr.active {
            return Some(false);
        }
        if self.incr.empty_round {
            let scanned_last = self.incr.last_scanned.get(&first) == Some(&self.incr.round);
            if scanned_last && !incr_match_diff() {
                return None;
            }
            // Not scanned in the last real round: full scan, recorded at the
            // current round so the next real round's diff is exact.
            let prev = self.incr.last_scanned.insert(first, self.incr.round);
            return Some(prev == Some(self.incr.round) && incr_match_diff());
        }
        let prev = self.incr.last_scanned.insert(first, self.incr.round);
        Some(prev == Some(self.incr.round - 1))
    }

    /// Diff mode bookkeeping after a `match_triggers` call.
    pub(super) fn incr_record(
        &mut self,
        pairs: &[(PatternId, Option<u32>)],
        filtered: bool,
        matches: &[DeterministicHashMap<Local, u32>],
    ) {
        if !incr_match_diff() || pairs.len() != 1 {
            return;
        }
        let pattern = pairs[0].0;
        if !filtered {
            self.incr
                .seen
                .entry(pattern)
                .or_default()
                .extend(matches.iter().cloned());
            return;
        }
        let mut a = DeterministicHashMap::default();
        let full = self.match_patterns(&mut a, &[(pattern, None)], false);
        let canon = |m: &DeterministicHashMap<Local, u32>| {
            let mut kv: Vec<(Local, u32)> =
                m.iter().map(|(l, &d)| (l.clone(), self.find(d))).collect();
            kv.sort();
            kv
        };
        let fk: FastDeterministicHashSet<Vec<(Local, u32)>> = matches.iter().map(canon).collect();
        let seen: FastDeterministicHashSet<Vec<(Local, u32)>> = self
            .incr
            .seen
            .get(&pattern)
            .map(|v| v.iter().map(canon).collect())
            .unwrap_or_default();
        let missed: Vec<&DeterministicHashMap<Local, u32>> = full
            .iter()
            .filter(|m| {
                let k = canon(m);
                !fk.contains(&k) && !seen.contains(&k)
            })
            .collect();
        if !missed.is_empty() {
            INCR_DIFF_CALLS.fetch_add(1, Ordering::Relaxed);
            INCR_DIFF_MISSED.fetch_add(missed.len() as u64, Ordering::Relaxed);
            eprintln!(
                "INCR_DIFF round={} pattern={pattern} {:?} full={} filtered={} missed_new={}",
                self.incr.round,
                self.compiled_patterns[pattern],
                full.len(),
                matches.len(),
                missed.len()
            );
            for m in missed.iter().take(3) {
                let b: Vec<String> = m
                    .iter()
                    .map(|(l, &d)| {
                        format!(
                            "{}->{} (class {})",
                            l.symbol,
                            self.display_term(d),
                            self.find(d)
                        )
                    })
                    .collect();
                eprintln!("INCR_DIFF   missed [{}]", b.join("; "));
            }
            if let Pattern::App(op, _) = &self.compiled_patterns[pattern] {
                let key = op.to_function_map_key();
                let cands: Vec<String> = self
                    .incr
                    .cands
                    .get(&key)
                    .map(|v| {
                        v.iter()
                            .map(|&(t, l)| format!("{}@{l}={}", t, self.display_term(t)))
                            .collect()
                    })
                    .unwrap_or_default();
                let all: Vec<String> = self
                    .function_maps
                    .get(&key)
                    .map(|v| {
                        v.iter()
                            .map(|&(t, _)| {
                                format!("{}={} [class {}]", t, self.display_term(t), self.find(t))
                            })
                            .collect()
                    })
                    .unwrap_or_default();
                let seeds: Vec<String> = self
                    .incr
                    .last_seeds
                    .iter()
                    .map(|&t| format!("{}={}", t, self.display_term(t)))
                    .collect();
                eprintln!(
                    "INCR_DIFF   snapshot_len={} next_id={} seeds=[{}]",
                    self.incr.snapshot.len(),
                    self.next_id,
                    seeds.join(", ")
                );
                eprintln!("INCR_DIFF   cands({key})=[{}]", cands.join(", "));
                let ren: Vec<String> = self
                    .incr
                    .last_renamed
                    .iter()
                    .map(|&(t, o, n)| format!("{}={} {o}->{n}", t, self.display_term(t)))
                    .collect();
                eprintln!("INCR_DIFF   renamed=[{}]", ren.join(", "));
                let pars: Vec<String> = self
                    .incr
                    .last_renamed
                    .iter()
                    .map(|&(t, _, _)| format!("{}:{:?}", t, self.incr.parents.get(t as usize)))
                    .collect();
                eprintln!("INCR_DIFF   parents_of_renamed=[{}]", pars.join(", "));
                eprintln!("INCR_DIFF   all({key})=[{}]", all.join(", "));
            }
        }
        self.incr.seen.entry(pattern).or_default().extend(full);
    }

    /// Counters, printed at teardown (same keys as the semper adapter's).
    pub(super) fn rel_report(&self) {
        if self.rel.enabled {
            eprintln!(
                "SEMPER_RELEVANCY marks={} assign_hooks={} skipped_candidates={} skipped_quantifiers={}",
                REL_MARKS.load(Ordering::Relaxed),
                REL_ASSIGN_HOOKS.load(Ordering::Relaxed),
                REL_SKIPPED_CANDIDATES.load(Ordering::Relaxed),
                REL_SKIPPED_QUANTIFIERS.load(Ordering::Relaxed)
            );
        }
        if incr_match() {
            eprintln!(
                "SEMPER_INCR_MATCH skipped={} considered={} diff_calls={} diff_missed={} empty_rounds={}",
                INCR_SKIPPED.load(Ordering::Relaxed),
                INCR_CONSIDERED.load(Ordering::Relaxed),
                INCR_DIFF_CALLS.load(Ordering::Relaxed),
                INCR_DIFF_MISSED.load(Ordering::Relaxed),
                INCR_EMPTY_ROUNDS.load(Ordering::Relaxed)
            );
        }
    }
}
