// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//! Semi-persistent e-graph backend for [`EgraphTrait`].
//!
//! Implements the trait over `semi-persistent-egraph`, replacing the basic
//! backend's hand-written trails (sig_trail, proof-forest stack, per-level
//! replay) with the engine's mark/restore tokens: one token per decision
//! level, and `backtrack_to` is a single restore to the target level's
//! token, whatever the distance.
//!
//! Two contracts need adaptation:
//!
//! - **Terms are permanent, equalities are scoped.** The driver's id maps
//!   (`id_map`, CNF var maps) are never rolled back, so a term registered at
//!   level 5 must survive a backtrack to level 0 — but a semi-persistent
//!   restore deletes nodes created after the mark. The backend therefore
//!   never hands out raw node ids: a driver id is an index into the stable
//!   `terms` table, and every registration is logged. `backtrack_to`
//!   restores the token, then replays the logged registrations above the
//!   restore point, re-interning each term into the restored graph and
//!   repairing its table entry. Replay resolves children through the table,
//!   so a replayed term lands on the correct (possibly re-minted) nodes.
//!
//! - **Conflicts are explained as asserted-equality pairs.** The engine's
//!   proof steps carry [`Justification`] leaves; each `assert_equal` merge
//!   is justified with `Assumption` carrying its index in the assertion
//!   log, and explanation maps the indices back to the asserted pairs the
//!   driver expects (it reconstructs SAT literals itself via `make_eq`).
//!
//! E-matching (`match_triggers`) is implemented as a port of the basic
//! backend's top-down matcher over the registration log, and relevancy
//! filtering of match candidates is implemented as a traversal of the merge
//! state (the e-graph is the relevancy skeleton). Both are opt-in:
//! `SEMPER_EMATCH=1` enables the matcher, `SEMPER_RELEVANCY=1` adds the
//! filter. E-matching is gated off by default because it currently emits an
//! unsound theory lemma on 2 of 224 quantifier regression files: a true=false
//! conflict from two congruent equality-atoms merged to opposite truth values
//! is explained via `explain_pairs(true, false)`, which can take a forest path
//! that omits the congruence's child-equality antecedents. The fix is to
//! explain the two colliding atom-nodes instead, forcing the congruence
//! expansion. With the matcher off, quantified problems are sound but
//! incomplete (unknown).
//!
//! `drain_arithmetic_equalities` returns none (Nelson-Oppen equality
//! propagation needs a merge-observation hook in the engine), so arithmetic
//! problems still need the basic backend / `--arith-solver none`.

use crate::egraphs::repr::{Op, Pattern, PatternId};
use crate::egraphs::traits::{Conflict, EgraphResult, EgraphTrait, Lit};
// FxHashMap, not utils::DeterministicHashMap: that alias is ordered (needs
// Ord, which Op lacks), and neither map here is ever iterated, so ordering
// buys nothing. FxHashMap has no random state, keeping runs reproducible.
use rustc_hash::FxHashMap;
use semi_persistent_egraph::containers::ShrinkPolicy;
use semi_persistent_egraph::id::ENodeId;
use semi_persistent_egraph::model::MachineLit;
use semi_persistent_egraph::union_find::{Justification, ProofBuf};
use semi_persistent_egraph::{EGraph31, EGraphToken, IndexLike};
use std::cell::RefCell;
use std::fmt;
use yaspar_ir::ast::Local;

type Eg = EGraph31<MachineLit, true, true>;
type SortId = semi_persistent_egraph::id::SortId;
type OpId = semi_persistent_egraph::id::OpId;

/// Counters surfaced to the driver (`propagator.sync_external_stats` reads
/// `stats.merges`).
#[derive(Default)]
pub struct SemperStats {
    pub merges: u64,
}

/// One driver-visible registration, replayable after a restore. Children are
/// driver ids, resolved through the terms table at replay time.
enum RegEvent {
    Term { op: Op, children: Vec<u32> },
    Opaque,
}

/// Snapshot taken on entering a decision level: the engine token plus the
/// lengths of the scoped logs. Registrations are not truncated — they replay.
struct LevelMark {
    token: EGraphToken,
    asserts_len: usize,
    diseqs_len: usize,
    reg_len: usize,
}

pub struct SemperEgraph {
    eg: Eg,
    term_sort: SortId,
    /// Op interning, keyed by (op, arity): the same symbol can only recur at
    /// one arity per key, and registry names are mangled with the arity so
    /// `App("f")/1` and `Constant("f")/0` cannot collide.
    ops: FxHashMap<(Op, usize), OpId>,
    /// Driver id -> current engine node. Append-only; entries above a
    /// restore point are repaired by replay, never removed.
    terms: Vec<ENodeId>,
    /// Engine node -> first driver id that produced it. Gives `find` a
    /// canonical driver id per class (the root node's first registrant), so
    /// the driver's `find(id) == id` is-representative idiom stays
    /// meaningful. Rebuilt after a restore, since replay can re-mint nodes.
    node_to_driver: FxHashMap<ENodeId, u32>,
    reg_log: Vec<RegEvent>,
    opaque_count: usize,
    /// Asserted equalities; index i is the `Assumption` payload of merge i.
    asserts: Vec<(u32, u32)>,
    /// Asserted disequalities with the literal that asserted each.
    diseqs: Vec<(u32, u32, Lit)>,
    /// Cached class roots per disequality, making the per-assert violation
    /// check O(1) for the common entry: two distinct roots stay distinct
    /// until one is absorbed, and testing "still a root" is one parent read
    /// (`find_const` on a root terminates immediately). Entries are stamped
    /// with `epoch`; a restore bumps it, because a cached root above the
    /// restore point may name a deleted or re-minted node.
    diseq_roots: Vec<(ENodeId, ENodeId)>,
    diseq_epoch: Vec<u64>,
    epoch: u64,
    /// Conflict reporting is edge-triggered: a violated disequality is
    /// reported once, not on every subsequent assertion while it stays
    /// violated. Re-reporting queued a duplicate of the same theory clause
    /// per assertion until the backtrack — 24% more clauses than the basic
    /// backend on eq_diamond14 (10906 vs 8781), with the cost showing up as
    /// CaDiCaL clause-addition and propagation time. Cleared on backtrack;
    /// a violation that survives one (possible under chronological
    /// backtracking) is re-reported once, which is sound — the clause is
    /// already in the solver either way.
    reported_diseqs: rustc_hash::FxHashSet<usize>,
    reported_tf: bool,
    /// `register_eq` watches. Recorded for the future propagation hook; the
    /// driver does not consume `EgraphResult::propagations` yet.
    eq_watches: Vec<(u32, u32, Lit)>,
    patterns: Vec<Pattern<u32>>,
    /// (op, arity) -> driver ids of registered terms, for e-matching
    /// candidate enumeration. Built incrementally from `reg_log` up to
    /// `fn_index_upto`. Both live in driver-id space, which is
    /// backtrack-stable (terms are permanent), so the index survives
    /// restores without repair — the same reason `reg_log` replays work.
    fn_index: FxHashMap<(Op, usize), Vec<u32>>,
    fn_index_upto: usize,
    /// Terms asserted at level 0: the input formula's top level, and the
    /// seeds of the relevancy slice. Level 0 takes no token, so these are
    /// never rolled back and the vector is append-only.
    root_terms: Vec<u32>,
    /// Relevancy gating for e-matching (SEMPER_RELEVANCY=1). When enabled,
    /// match_triggers computes the relevant cone of the current assignment
    /// (Z3's witness rules, read off the merge state: a gate's truth value
    /// is whether its root is the true or false class) and skips candidates
    /// outside it. Off by default so regression comparisons are unaffected.
    relevancy_enabled: bool,
    /// The slice for the match round in progress; None when gating is off.
    active_slice: Option<rustc_hash::FxHashSet<u32>>,
    /// E-matching is opt-in (SEMPER_EMATCH=1) while a soundness bug in the
    /// conflict path with instantiation-created terms is open: it emits an
    /// unsound theory lemma on 2 of 224 quantifier regression files
    /// (quantifier_disequalities_level{,2}: wrong unsat, Z3 says sat). Off by
    /// default, match_triggers returns nothing, so quantified problems are
    /// sound-but-incomplete (unknown) exactly as before the matcher landed.
    ematch_enabled: bool,
    /// Current SAT decision level, advanced by `notify_new_decision_level`.
    level: usize,
    /// Materialized scopes, tagged with the level that first mutated the
    /// e-graph. Marking is lazy: a decision level that only does Boolean
    /// work never takes a token, so it costs nothing here — the engine's
    /// `mark` is time-O(parent-frame captures) across every sub-container,
    /// and CaDiCaL opens a level per decision. A level with no mark needs no
    /// undo: the state at its end equals the state at the last mark below it.
    marks: Vec<(usize, LevelMark)>,
    /// Scratch for proof extraction, reused across explanations.
    scratch: RefCell<ProofBuf<ENodeId>>,
    arithmetic_terms: Vec<u32>,
    incremental_arith: bool,
    /// The driver's true/false constants, captured at registration. Their
    /// disequality is built in: the driver debug-asserts that a true/false
    /// merge never goes undetected, so the backend must report it as a
    /// conflict itself (with no disequality literal — the equality path
    /// alone is contradictory).
    true_term: Option<u32>,
    false_term: Option<u32>,
    pub stats: SemperStats,
}

impl Default for SemperEgraph {
    fn default() -> Self {
        Self::new()
    }
}

impl SemperEgraph {
    pub fn new() -> Self {
        let mut eg = Eg::new();
        // One interned (hence non-concrete) sort for every term: the driver
        // enforces sort discipline upstream in yaspar, and the engine's sort
        // checks only require merge endpoints to agree.
        let term_sort = eg.sorts_mut().intern("SunTerm");
        SemperEgraph {
            eg,
            term_sort,
            ops: FxHashMap::default(),
            terms: Vec::new(),
            node_to_driver: FxHashMap::default(),
            reg_log: Vec::new(),
            opaque_count: 0,
            asserts: Vec::new(),
            diseqs: Vec::new(),
            diseq_roots: Vec::new(),
            diseq_epoch: Vec::new(),
            epoch: 0,
            reported_diseqs: rustc_hash::FxHashSet::default(),
            reported_tf: false,
            eq_watches: Vec::new(),
            patterns: Vec::new(),
            fn_index: FxHashMap::default(),
            fn_index_upto: 0,
            root_terms: Vec::new(),
            relevancy_enabled: std::env::var("SEMPER_RELEVANCY").is_ok_and(|v| v == "1"),
            active_slice: None,
            ematch_enabled: std::env::var("SEMPER_EMATCH").is_ok_and(|v| v == "1"),
            level: 0,
            marks: Vec::new(),
            scratch: RefCell::new(ProofBuf::new()),
            arithmetic_terms: Vec::new(),
            incremental_arith: false,
            true_term: None,
            false_term: None,
            stats: SemperStats::default(),
        }
    }

    fn node(&self, driver_id: u32) -> ENodeId {
        self.terms[driver_id as usize]
    }

    fn op_id(&mut self, op: &Op, arity: usize) -> OpId {
        if let Some(&id) = self.ops.get(&(op.clone(), arity)) {
            return id;
        }
        let name = format!("{}${arity}", op.to_function_map_key());
        // The registry is the authority, the map only a cache: the registry
        // is semi-persistent, so a restore can drop ops registered in the
        // popped scopes, and `backtrack_to` clears the cache to match. An op
        // that survived the restore is found again by name; one that was
        // dropped is re-registered by the replay that needs it.
        let id = if let Some(id) = self.eg.ops().id_by_name(&name) {
            id
        } else if matches!(op, Op::Eq) && arity == 2 {
            // Eq gets the commutative (sorted-pair) representation so both
            // argument orders intern to one node.
            self.eg
                .ops_mut()
                .register_c(&name, [self.term_sort, self.term_sort], self.term_sort)
        } else {
            let sorts = vec![self.term_sort; arity];
            self.eg.ops_mut().register(&name, &sorts, self.term_sort)
        };
        self.ops.insert((op.clone(), arity), id);
        id
    }

    /// Intern one registration event into the engine, returning the node.
    /// Used both for first registration and for replay after a restore.
    fn intern(&mut self, event_index: usize) -> ENodeId {
        match &self.reg_log[event_index] {
            RegEvent::Term { op, children } => {
                let op = op.clone();
                let children: Vec<ENodeId> = children.iter().map(|&c| self.node(c)).collect();
                let op_id = self.op_id(&op, children.len());
                self.eg.add(op_id, &children)
            }
            RegEvent::Opaque => {
                // A unique nullary op per opaque index keeps replay
                // deterministic: the same event re-interns the same symbol.
                // Lookup-or-register for the same reason as `op_id`: a
                // restore between two replays of this event drops and
                // re-creates the registry entry.
                let name = format!("opaque${event_index}");
                let op_id = match self.eg.ops().id_by_name(&name) {
                    Some(id) => id,
                    None => self.eg.ops_mut().register(&name, &[], self.term_sort),
                };
                self.eg.add(op_id, &[])
            }
        }
    }

    fn push_registration(&mut self, event: RegEvent) -> u32 {
        self.reg_log.push(event);
        let node = self.intern(self.reg_log.len() - 1);
        let driver_id = u32::try_from(self.terms.len()).expect("driver term table exceeds u32");
        self.terms.push(node);
        self.node_to_driver.entry(node).or_insert(driver_id);
        driver_id
    }

    /// Take a token for the current level if it has none yet. Every mutating
    /// entry point calls this first, which is what makes marking lazy.
    fn ensure_scope(&mut self) {
        if self.level == 0 {
            return;
        }
        if self.marks.last().is_some_and(|&(l, _)| l >= self.level) {
            return;
        }
        let mark = LevelMark {
            token: self.eg.mark(ShrinkPolicy::Never),
            asserts_len: self.asserts.len(),
            diseqs_len: self.diseqs.len(),
            reg_len: self.reg_log.len(),
        };
        self.marks.push((self.level, mark));
    }

    /// The asserted-equality pairs whose merges (closed under congruence)
    /// force `find(a) == find(b)`.
    fn explain_pairs(&self, a: u32, b: u32) -> Vec<(u32, u32)> {
        let mut buf = self.scratch.borrow_mut();
        buf.steps.clear();
        let ok = self.eg.explain_deep(self.node(a), self.node(b), &mut buf);
        debug_assert!(ok, "explain_pairs on unequal classes");
        // Proof-path order, deduplicated by first occurrence. Sorted order
        // was also tried on the hypothesis that antecedent order steers
        // CaDiCaL's watched literals onto a different search trajectory:
        // measured no difference on the 103-file subset (11.9s vs 11.7s,
        // run noise), so the choice between them is free. Path order is
        // kept because the dedup is O(k) against the sort's O(k log k).
        let mut seen: rustc_hash::FxHashSet<(u32, u32)> = rustc_hash::FxHashSet::default();
        buf.steps
            .iter()
            .filter_map(|&(_, _, j)| match j {
                Justification::Assumption { lit } => Some(self.asserts[lit.as_usize()]),
                _ => None,
            })
            .filter(|&p| seen.insert(p))
            .collect()
    }

    /// Scan the disequality log for one violated by the current classes.
    /// The true/false pair is checked first: its merge is the deepest
    /// possible conflict and carries no asserting literal. The per-entry
    /// cost is two parent reads in the common case, via the cached roots.
    fn violated_diseq(&mut self) -> Option<Conflict<u32>> {
        if !self.reported_tf
            && let (Some(t), Some(f)) = (self.true_term, self.false_term)
            && self.eg.find_const(self.node(t)) == self.eg.find_const(self.node(f))
        {
            self.reported_tf = true;
            return Some(Conflict {
                equalities: self.explain_pairs(t, f),
                disequality: (t, f),
                diseq_lit: None,
            });
        }
        for i in 0..self.diseqs.len() {
            if self.reported_diseqs.contains(&i) {
                continue;
            }
            let (t1, t2, lit) = self.diseqs[i];
            let (r1, r2) = if self.diseq_epoch[i] == self.epoch {
                // Two distinct roots stay distinct until one is absorbed;
                // find_const on a still-live root is a single parent read.
                self.diseq_roots[i]
            } else {
                (self.node(t1), self.node(t2))
            };
            let nr1 = self.eg.find_const(r1);
            let nr2 = self.eg.find_const(r2);
            if nr1 == nr2 {
                self.reported_diseqs.insert(i);
                return Some(Conflict {
                    equalities: self.explain_pairs(t1, t2),
                    disequality: (t1, t2),
                    diseq_lit: Some(lit),
                });
            }
            self.diseq_roots[i] = (nr1, nr2);
            self.diseq_epoch[i] = self.epoch;
        }
        None
    }

    fn result_after_merge(&mut self) -> EgraphResult<u32> {
        match self.violated_diseq() {
            Some(c) => EgraphResult::with_conflict(c),
            None => EgraphResult::ok(),
        }
    }

    /// Extend the (op, arity) -> terms index over registrations made since
    /// the last call. Driver ids and `reg_log` children never change, so
    /// extension is the only maintenance the index ever needs.
    fn ensure_fn_index(&mut self) {
        for i in self.fn_index_upto..self.reg_log.len() {
            if let RegEvent::Term { op, children } = &self.reg_log[i] {
                self.fn_index
                    .entry((op.clone(), children.len()))
                    .or_default()
                    .push(u32::try_from(i).expect("driver id fits u32"));
            }
        }
        self.fn_index_upto = self.reg_log.len();
    }

    fn reg_children(&self, term: u32) -> &[u32] {
        match &self.reg_log[term as usize] {
            RegEvent::Term { children, .. } => children,
            RegEvent::Opaque => &[],
        }
    }

    // --- Relevancy --------------------------------------------------------
    //
    // The e-graph itself is the relevancy skeleton: the driver registers
    // every term including the logical operators, and truth values arrive
    // as merges with the true/false classes, so the relevant cone is
    // computable by traversal alone. The slice is recomputed per match
    // round rather than maintained incrementally — matching dominates its
    // O(terms) cost, and a transient set has no backtracking interaction
    // at all. The incremental version (a flag bit in the engine's node
    // headers, which are already captured by the semi-persistent stores)
    // becomes worth it only if slicing shows up in a profile.

    /// The relevant cone of the current assignment: Z3's witness rules,
    /// closed under equivalence classes, seeded by the level-0 assertions.
    fn relevant_slice(&self) -> rustc_hash::FxHashSet<u32> {
        let true_root = self.true_term.map(|t| self.find(t));
        let false_root = self.false_term.map(|t| self.find(t));
        // Class membership over driver ids, for the class-closure rule.
        let mut class_members: FxHashMap<u32, Vec<u32>> = FxHashMap::default();
        for i in 0..self.terms.len() {
            let i = i as u32;
            class_members.entry(self.find(i)).or_default().push(i);
        }
        let mut relevant: rustc_hash::FxHashSet<u32> = rustc_hash::FxHashSet::default();
        let mut queue: Vec<u32> = self.root_terms.clone();
        while let Some(t) = queue.pop() {
            if !relevant.insert(t) {
                continue;
            }
            // Relevancy is a property of the whole class.
            if let Some(members) = class_members.get(&self.find(t)) {
                for &m in members {
                    if !relevant.contains(&m) {
                        queue.push(m);
                    }
                }
            }
            let RegEvent::Term { op, children } = &self.reg_log[t as usize] else {
                continue;
            };
            let value = {
                let r = self.find(t);
                if Some(r) == true_root {
                    Some(true)
                } else if Some(r) == false_root {
                    Some(false)
                } else {
                    None
                }
            };
            let child_is = |c: u32, v: bool| {
                let r = self.find(c);
                if v {
                    Some(r) == true_root
                } else {
                    Some(r) == false_root
                }
            };
            match (op, value) {
                // A satisfied gate needs one witness; a falsified one needs
                // every child. An unassigned gate contributes nothing yet.
                (Op::And, Some(true)) | (Op::Or, Some(false)) => queue.extend(children),
                (Op::And, Some(false)) => {
                    if let Some(&w) = children.iter().find(|&&c| child_is(c, false)) {
                        queue.push(w);
                    }
                }
                (Op::Or, Some(true)) => {
                    if let Some(&w) = children.iter().find(|&&c| child_is(c, true)) {
                        queue.push(w);
                    }
                }
                (Op::Implies, Some(false)) => queue.extend(children),
                (Op::Implies, Some(true)) => {
                    if children.len() == 2 {
                        if child_is(children[0], false) {
                            queue.push(children[0]);
                        } else if child_is(children[1], true) {
                            queue.push(children[1]);
                        }
                    } else {
                        queue.extend(children);
                    }
                }
                (Op::And | Op::Or | Op::Implies, None) => {}
                (Op::Ite, _) if children.len() == 3 => {
                    queue.push(children[0]);
                    if child_is(children[0], true) {
                        queue.push(children[1]);
                    } else if child_is(children[0], false) {
                        queue.push(children[2]);
                    }
                }
                // Everything else — applications, equalities, negation —
                // makes all its arguments relevant.
                _ => queue.extend(children),
            }
        }
        relevant
    }

    fn candidate_relevant(&self, cand: u32) -> bool {
        self.active_slice.as_ref().is_none_or(|s| s.contains(&cand))
    }

    // --- E-matching -------------------------------------------------------
    //
    // A faithful port of the basic backend's top-down matcher, over the
    // registration log instead of its function_maps: same binding
    // discipline (variables bind raw ids, consistency compared by class),
    // same congruence dedup (candidates with canonically equal subterm
    // vectors are matched once), same multi-trigger semantics (one
    // substitution threaded through all trigger patterns). Bridging to the
    // engine's compiled leapfrog matcher is the planned upgrade; this port
    // establishes behavioral parity first so that swap is measurable.

    fn match_pairs(
        &self,
        assignment: &mut crate::utils::DeterministicHashMap<Local, u32>,
        pairs: &[(PatternId, Option<u32>)],
    ) -> Vec<crate::utils::DeterministicHashMap<Local, u32>> {
        let Some(&(pattern_id, hint)) = pairs.first() else {
            return vec![assignment.clone()];
        };
        let pattern = self.patterns[pattern_id].clone();
        self.match_top(assignment, &pattern, hint, &pairs[1..])
    }

    fn match_top(
        &self,
        assignment: &mut crate::utils::DeterministicHashMap<Local, u32>,
        pattern: &Pattern<u32>,
        hint: Option<u32>,
        remaining: &[(PatternId, Option<u32>)],
    ) -> Vec<crate::utils::DeterministicHashMap<Local, u32>> {
        match pattern {
            Pattern::Var(name) => {
                let ground = hint.expect("Pattern::Var requires a ground term to bind");
                match assignment.get(name) {
                    None => {
                        assignment.insert(name.clone(), ground);
                        self.match_pairs(assignment, remaining)
                    }
                    Some(&v) if self.find(v) == self.find(ground) => {
                        self.match_pairs(assignment, remaining)
                    }
                    Some(_) => vec![],
                }
            }
            Pattern::Ground(id) => match hint {
                Some(ground) if self.find(*id) == self.find(ground) => {
                    self.match_pairs(assignment, remaining)
                }
                None => self.match_pairs(assignment, remaining),
                _ => vec![],
            },
            Pattern::App(op, subs) => {
                let Some(candidates) = self.fn_index.get(&(op.clone(), subs.len())) else {
                    return vec![];
                };
                let ground_root = hint.map(|t| self.find(t));
                let mut out = Vec::new();
                let mut considered: rustc_hash::FxHashSet<Vec<u32>> =
                    rustc_hash::FxHashSet::default();
                for &cand in candidates {
                    if !self.candidate_relevant(cand) {
                        continue;
                    }
                    if let Some(gr) = ground_root
                        && self.find(cand) != gr
                    {
                        continue;
                    }
                    let subterms: Vec<u32> = self.reg_children(cand).to_vec();
                    let canonical: Vec<u32> = subterms.iter().map(|&s| self.find(s)).collect();
                    if !considered.insert(canonical) {
                        continue;
                    }
                    let mut sub_assignment = assignment.clone();
                    out.extend(self.match_subs(&mut sub_assignment, subs, &subterms, remaining));
                }
                out
            }
        }
    }

    fn match_subs(
        &self,
        assignment: &mut crate::utils::DeterministicHashMap<Local, u32>,
        sub_patterns: &[Pattern<u32>],
        grounds: &[u32],
        remaining: &[(PatternId, Option<u32>)],
    ) -> Vec<crate::utils::DeterministicHashMap<Local, u32>> {
        let Some(pattern) = sub_patterns.first() else {
            return self.match_pairs(assignment, remaining);
        };
        let ground = grounds[0];
        let rest_patterns = &sub_patterns[1..];
        let rest_grounds = &grounds[1..];
        match pattern {
            Pattern::Var(name) => match assignment.get(name) {
                None => {
                    assignment.insert(name.clone(), ground);
                    self.match_subs(assignment, rest_patterns, rest_grounds, remaining)
                }
                Some(&v) if self.find(v) == self.find(ground) => {
                    self.match_subs(assignment, rest_patterns, rest_grounds, remaining)
                }
                Some(_) => vec![],
            },
            Pattern::Ground(id) => {
                if self.find(*id) == self.find(ground) {
                    self.match_subs(assignment, rest_patterns, rest_grounds, remaining)
                } else {
                    vec![]
                }
            }
            Pattern::App(op, children) => {
                let Some(candidates) = self.fn_index.get(&(op.clone(), children.len())) else {
                    return vec![];
                };
                let ground_root = self.find(ground);
                let mut out = Vec::new();
                let mut considered: rustc_hash::FxHashSet<Vec<u32>> =
                    rustc_hash::FxHashSet::default();
                for &cand in candidates {
                    if !self.candidate_relevant(cand) {
                        continue;
                    }
                    if self.find(cand) != ground_root {
                        continue;
                    }
                    let subterms: Vec<u32> = self.reg_children(cand).to_vec();
                    let canonical: Vec<u32> = subterms.iter().map(|&s| self.find(s)).collect();
                    if !considered.insert(canonical) {
                        continue;
                    }
                    let mut sub_assignment = assignment.clone();
                    for mut sub in self.match_subs(&mut sub_assignment, children, &subterms, &[]) {
                        out.extend(self.match_subs(
                            &mut sub,
                            rest_patterns,
                            rest_grounds,
                            remaining,
                        ));
                    }
                }
                out
            }
        }
    }
}

impl EgraphTrait for SemperEgraph {
    type Op = Op;
    type TermId = u32;

    fn register_term(&mut self, op: Op, children: &[u32], _dynamic: bool) -> u32 {
        // Hash-consing plus build-time child canonicalization make every
        // registration "dynamic": a term congruent to an existing one under
        // the current classes interns to that node.
        self.ensure_scope();
        self.push_registration(RegEvent::Term {
            op,
            children: children.to_vec(),
        })
    }

    fn register_constant(&mut self, op: Op) -> u32 {
        let tf = match &op {
            Op::Constant(s) if s == "true" => Some(true),
            Op::Constant(s) if s == "false" => Some(false),
            _ => None,
        };
        self.ensure_scope();
        let id = self.push_registration(RegEvent::Term {
            op,
            children: Vec::new(),
        });
        match tf {
            Some(true) => self.true_term.get_or_insert(id),
            Some(false) => self.false_term.get_or_insert(id),
            None => return id,
        };
        id
    }

    fn register_opaque(&mut self) -> u32 {
        self.ensure_scope();
        self.opaque_count += 1;
        self.push_registration(RegEvent::Opaque)
    }

    fn compile_pattern(&mut self, pattern: Pattern<u32>) -> PatternId {
        self.patterns.push(pattern);
        self.patterns.len() - 1
    }

    fn register_eq(&mut self, t1: u32, t2: u32, lit: Lit) {
        self.eq_watches.push((t1, t2, lit));
    }

    fn register_boolean_term(&mut self, op: Op, children: &[u32], _lit: Lit) -> u32 {
        self.ensure_scope();
        self.push_registration(RegEvent::Term {
            op,
            children: children.to_vec(),
        })
    }

    fn mark_arithmetic(&mut self, term: u32) {
        self.arithmetic_terms.push(term);
    }

    fn incremental_arithmetic(&mut self, enabled: bool) {
        self.incremental_arith = enabled;
    }

    fn drain_arithmetic_equalities(&mut self) -> Vec<(u32, u32)> {
        // Nelson-Oppen equality propagation needs merge observation in the
        // engine; until that hook exists this backend supports EUF only.
        Vec::new()
    }

    fn notify_new_decision_level(&mut self) {
        // Lazy: the token is taken by the first mutation at this level, if
        // any (see `ensure_scope`).
        self.level += 1;
    }

    fn assert_equal(&mut self, t1: u32, t2: u32) -> EgraphResult<u32> {
        self.ensure_scope();
        let idx = self.asserts.len();
        self.asserts.push((t1, t2));
        let word = u32::try_from(idx).expect("assertion log exceeds the index word");
        let merged = self.eg.merge_justified(
            self.node(t1),
            self.node(t2),
            Justification::Assumption { lit: word },
        );
        if self.level == 0 {
            self.root_terms.push(t1);
            self.root_terms.push(t2);
        }
        if merged.is_none() {
            // Already equal: no class changed, so no rebuild is needed and
            // no disequality can have become violated.
            return EgraphResult::ok();
        }
        self.stats.merges += 1;
        self.eg.rebuild();
        self.result_after_merge()
    }

    fn assert_disequal(&mut self, t1: u32, t2: u32, lit: Lit) -> EgraphResult<u32> {
        self.ensure_scope();
        let r1 = self.eg.find_const(self.node(t1));
        let r2 = self.eg.find_const(self.node(t2));
        if self.level == 0 {
            self.root_terms.push(t1);
            self.root_terms.push(t2);
        }
        self.diseqs.push((t1, t2, lit));
        self.diseq_roots.push((r1, r2));
        self.diseq_epoch.push(self.epoch);
        if r1 == r2 {
            self.reported_diseqs.insert(self.diseqs.len() - 1);
            return EgraphResult::with_conflict(Conflict {
                equalities: self.explain_pairs(t1, t2),
                disequality: (t1, t2),
                diseq_lit: Some(lit),
            });
        }
        EgraphResult::ok()
    }

    fn assert_distinct(&mut self, terms: &[u32], lit: Lit) -> EgraphResult<u32> {
        for (i, &t1) in terms.iter().enumerate() {
            for &t2 in &terms[i + 1..] {
                let r = self.assert_disequal(t1, t2, lit);
                if r.conflict.is_some() {
                    return r;
                }
            }
        }
        EgraphResult::ok()
    }

    fn find(&self, term: u32) -> u32 {
        let root = self.eg.find_const(self.node(term));
        // Every engine node was produced by a registration, so the root
        // always has a driver id; its first registrant is the class name.
        *self
            .node_to_driver
            .get(&root)
            .expect("every node comes from a registration")
    }

    fn are_equal(&self, t1: u32, t2: u32) -> bool {
        self.eg.find_const(self.node(t1)) == self.eg.find_const(self.node(t2))
    }

    fn match_triggers(
        &mut self,
        trigger_term_pairs: Vec<(PatternId, Option<u32>)>,
    ) -> Vec<crate::utils::DeterministicHashMap<Local, u32>> {
        if !self.ematch_enabled {
            return Vec::new();
        }
        self.ensure_fn_index();
        self.active_slice = self.relevancy_enabled.then(|| self.relevant_slice());
        let mut assignment = crate::utils::DeterministicHashMap::default();
        let matches = self.match_pairs(&mut assignment, &trigger_term_pairs);
        self.active_slice = None;
        matches
    }

    fn backtrack_to(&mut self, level: usize) {
        self.level = level;
        self.reported_diseqs.clear();
        self.reported_tf = false;
        // Marks are level-ascending; the first one above the target is the
        // restore point, and it also undoes every deeper mark (ancestor
        // restore). No mark above the target means no e-graph mutation
        // happened there: nothing to undo.
        let pos = self.marks.partition_point(|&(l, _)| l <= level);
        if pos == self.marks.len() {
            return;
        }
        let (_, mark) = self
            .marks
            .drain(pos..)
            .next()
            .expect("guarded by the length check above");
        self.eg.restore(mark.token);
        // Cached disequality roots may name nodes deleted by the restore.
        self.epoch += 1;
        // The restore may have dropped ops registered in the popped scopes;
        // the cache would hand out their dangling ids, so it is cleared and
        // repopulated from the registry on demand.
        self.ops.clear();
        self.asserts.truncate(mark.asserts_len);
        self.diseqs.truncate(mark.diseqs_len);
        self.diseq_roots.truncate(mark.diseqs_len);
        self.diseq_epoch.truncate(mark.diseqs_len);
        // Terms registered above the restore point were deleted with it, but
        // the driver's id maps still name them: replay their registrations
        // into the restored graph and repair the table entries.
        for i in mark.reg_len..self.reg_log.len() {
            let node = self.intern(i);
            let table_index = self.terms.len() - (self.reg_log.len() - i);
            self.terms[table_index] = node;
        }
        // Replay can re-mint node ids, so the reverse map is rebuilt from
        // the repaired table (first registrant wins, as at registration).
        if mark.reg_len < self.reg_log.len() {
            self.node_to_driver.clear();
            for (i, &node) in self.terms.iter().enumerate() {
                self.node_to_driver.entry(node).or_insert(i as u32);
            }
        }
    }

    fn make_decision(&self, _assignments: &[i32]) -> i32 {
        0
    }

    fn make_decision_lit(&self, _lit: Lit, _assignments: &[i32]) -> Lit {
        0
    }

    fn explain_equality(&self, t1: u32, t2: u32) -> Option<Vec<(u32, u32)>> {
        if !self.are_equal(t1, t2) {
            return None;
        }
        Some(self.explain_pairs(t1, t2))
    }
}

impl fmt::Display for SemperEgraph {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "SemperEgraph: {} terms, {} asserts, {} diseqs, level {}",
            self.terms.len(),
            self.asserts.len(),
            self.diseqs.len(),
            self.level
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn constant(e: &mut SemperEgraph, name: &str) -> u32 {
        e.register_constant(Op::Constant(name.to_string()))
    }

    #[test]
    fn transitivity_conflict_reports_path_and_diseq_lit() {
        let mut e = SemperEgraph::new();
        let a = constant(&mut e, "a");
        let b = constant(&mut e, "b");
        let c = constant(&mut e, "c");
        assert!(e.assert_equal(a, b).conflict.is_none());
        assert!(e.assert_equal(b, c).conflict.is_none());
        let r = e.assert_disequal(a, c, 7);
        let conflict = r.conflict.expect("a=b, b=c contradicts a!=c");
        assert_eq!(conflict.disequality, (a, c));
        assert_eq!(conflict.diseq_lit, Some(7));
        let mut expected = vec![(a, b), (b, c)];
        expected.sort_unstable();
        assert_eq!(conflict.equalities, expected);
    }

    #[test]
    fn congruence_conflict_explains_leaf_assertion() {
        let mut e = SemperEgraph::new();
        let a = constant(&mut e, "a");
        let b = constant(&mut e, "b");
        let fa = e.register_term(Op::App("f".to_string()), &[a], false);
        let fb = e.register_term(Op::App("f".to_string()), &[b], false);
        assert!(e.assert_disequal(fa, fb, 3).conflict.is_none());
        let r = e.assert_equal(a, b);
        let conflict = r.conflict.expect("a=b forces f(a)=f(b)");
        assert_eq!(conflict.disequality, (fa, fb));
        assert_eq!(conflict.diseq_lit, Some(3));
        assert_eq!(conflict.equalities, vec![(a, b)]);
    }

    #[test]
    fn eq_atoms_intern_symmetrically() {
        let mut e = SemperEgraph::new();
        let a = constant(&mut e, "a");
        let b = constant(&mut e, "b");
        let ab = e.register_term(Op::Eq, &[a, b], false);
        let ba = e.register_term(Op::Eq, &[b, a], false);
        assert!(e.are_equal(ab, ba));
    }

    #[test]
    fn backtrack_is_one_restore_across_levels() {
        let mut e = SemperEgraph::new();
        let a = constant(&mut e, "a");
        let b = constant(&mut e, "b");
        let c = constant(&mut e, "c");
        e.notify_new_decision_level();
        assert!(e.assert_equal(a, b).conflict.is_none());
        e.notify_new_decision_level();
        assert!(e.assert_equal(b, c).conflict.is_none());
        assert!(e.are_equal(a, c));
        e.backtrack_to(0);
        assert!(!e.are_equal(a, b));
        assert!(!e.are_equal(b, c));
    }

    #[test]
    fn terms_registered_in_scope_survive_backtrack() {
        // The driver's id maps are never rolled back, so a term registered
        // at level 1 must stay usable after backtracking to level 0.
        let mut e = SemperEgraph::new();
        let a = constant(&mut e, "a");
        let b = constant(&mut e, "b");
        e.notify_new_decision_level();
        let fa = e.register_term(Op::App("f".to_string()), &[a], false);
        assert!(e.assert_equal(fa, b).conflict.is_none());
        e.backtrack_to(0);
        // The equality is undone; the term is not.
        assert!(!e.are_equal(fa, b));
        let fa2 = e.register_term(Op::App("f".to_string()), &[a], false);
        assert!(e.are_equal(fa, fa2));
        // And it still participates in congruence.
        e.notify_new_decision_level();
        let c = constant(&mut e, "c");
        let fc = e.register_term(Op::App("f".to_string()), &[c], false);
        assert!(e.assert_equal(a, c).conflict.is_none());
        assert!(e.are_equal(fa, fc));
    }

    #[test]
    fn levels_without_writes_take_no_token_and_backtrack_correctly() {
        let mut e = SemperEgraph::new();
        let a = constant(&mut e, "a");
        let b = constant(&mut e, "b");
        let c = constant(&mut e, "c");
        // Levels 1 and 2 do only Boolean work (no e-graph calls); the first
        // mutation happens at level 3.
        e.notify_new_decision_level();
        e.notify_new_decision_level();
        e.notify_new_decision_level();
        assert!(e.assert_equal(a, b).conflict.is_none());
        assert_eq!(e.marks.len(), 1, "only the mutating level takes a token");
        // Backtracking to an empty level above the mark undoes level 3's
        // merge (the state at level 2's end equals the pre-mark state).
        e.backtrack_to(2);
        assert!(!e.are_equal(a, b));
        assert!(e.marks.is_empty());
        // Backtracking through levels that never materialized is a no-op.
        e.backtrack_to(0);
        assert!(!e.are_equal(a, b));
        // The next scope works normally.
        e.notify_new_decision_level();
        assert!(e.assert_equal(b, c).conflict.is_none());
        e.backtrack_to(0);
        assert!(!e.are_equal(b, c));
    }

    #[test]
    fn distinct_is_pairwise() {
        let mut e = SemperEgraph::new();
        let a = constant(&mut e, "a");
        let b = constant(&mut e, "b");
        let c = constant(&mut e, "c");
        assert!(e.assert_distinct(&[a, b, c], 9).conflict.is_none());
        let r = e.assert_equal(a, c);
        let conflict = r.conflict.expect("distinct(a,b,c) contradicts a=c");
        assert_eq!(conflict.diseq_lit, Some(9));
    }
}
