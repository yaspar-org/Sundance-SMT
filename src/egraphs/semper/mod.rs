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
//! Current limits, by design of this first cut: `match_triggers` returns no
//! matches (quantified problems need the pattern compiler bridge), and
//! `drain_arithmetic_equalities` returns none (Nelson-Oppen equality
//! propagation needs a merge-observation hook in the engine), so run with
//! quantifier-free problems and `--arith-solver none`.

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
    /// `register_eq` watches. Recorded for the future propagation hook; the
    /// driver does not consume `EgraphResult::propagations` yet.
    eq_watches: Vec<(u32, u32, Lit)>,
    patterns: Vec<Pattern<u32>>,
    marks: Vec<LevelMark>,
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
            eq_watches: Vec::new(),
            patterns: Vec::new(),
            marks: Vec::new(),
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
                let children: Vec<ENodeId> =
                    children.iter().map(|&c| self.node(c)).collect();
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
        let driver_id =
            u32::try_from(self.terms.len()).expect("driver term table exceeds u32");
        self.terms.push(node);
        self.node_to_driver.entry(node).or_insert(driver_id);
        driver_id
    }

    /// The asserted-equality pairs whose merges (closed under congruence)
    /// force `find(a) == find(b)`.
    fn explain_pairs(&self, a: u32, b: u32) -> Vec<(u32, u32)> {
        let mut buf = ProofBuf::new();
        let ok = self.eg.explain_deep(self.node(a), self.node(b), &mut buf);
        debug_assert!(ok, "explain_pairs on unequal classes");
        let mut pairs: Vec<(u32, u32)> = buf
            .steps
            .iter()
            .filter_map(|&(_, _, j)| match j {
                Justification::Assumption { lit } => Some(self.asserts[lit.as_usize()]),
                _ => None,
            })
            .collect();
        pairs.sort_unstable();
        pairs.dedup();
        pairs
    }

    /// Scan the disequality log for one violated by the current classes.
    /// The true/false pair is checked first: its merge is the deepest
    /// possible conflict and carries no asserting literal.
    fn violated_diseq(&self) -> Option<Conflict<u32>> {
        if let (Some(t), Some(f)) = (self.true_term, self.false_term)
            && self.eg.find_const(self.node(t)) == self.eg.find_const(self.node(f))
        {
            return Some(Conflict {
                equalities: self.explain_pairs(t, f),
                disequality: (t, f),
                diseq_lit: None,
            });
        }
        for &(t1, t2, lit) in &self.diseqs {
            if self.eg.find_const(self.node(t1)) == self.eg.find_const(self.node(t2)) {
                return Some(Conflict {
                    equalities: self.explain_pairs(t1, t2),
                    disequality: (t1, t2),
                    diseq_lit: Some(lit),
                });
            }
        }
        None
    }

    fn result_after_merge(&self) -> EgraphResult<u32> {
        match self.violated_diseq() {
            Some(c) => EgraphResult::with_conflict(c),
            None => EgraphResult::ok(),
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
        self.marks.push(LevelMark {
            token: self.eg.mark(ShrinkPolicy::Never),
            asserts_len: self.asserts.len(),
            diseqs_len: self.diseqs.len(),
            reg_len: self.reg_log.len(),
        });
    }

    fn assert_equal(&mut self, t1: u32, t2: u32) -> EgraphResult<u32> {
        let idx = self.asserts.len();
        self.asserts.push((t1, t2));
        let word = u32::try_from(idx).expect("assertion log exceeds the index word");
        let merged = self.eg.merge_justified(
            self.node(t1),
            self.node(t2),
            Justification::Assumption { lit: word },
        );
        if merged.is_some() {
            self.stats.merges += 1;
        }
        self.eg.rebuild();
        self.result_after_merge()
    }

    fn assert_disequal(&mut self, t1: u32, t2: u32, lit: Lit) -> EgraphResult<u32> {
        self.diseqs.push((t1, t2, lit));
        if self.eg.find_const(self.node(t1)) == self.eg.find_const(self.node(t2)) {
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
        _trigger_term_pairs: Vec<(PatternId, Option<u32>)>,
    ) -> Vec<crate::utils::DeterministicHashMap<Local, u32>> {
        // Pattern-compiler bridge to the engine's e-matching is the next
        // step; until then quantified problems need the basic backend.
        Vec::new()
    }

    fn backtrack_to(&mut self, level: usize) {
        if self.marks.len() <= level {
            return;
        }
        let mark = self
            .marks
            .drain(level..)
            .next()
            .expect("guarded by the length check above");
        self.eg.restore(mark.token);
        // The restore may have dropped ops registered in the popped scopes;
        // the cache would hand out their dangling ids, so it is cleared and
        // repopulated from the registry on demand.
        self.ops.clear();
        self.asserts.truncate(mark.asserts_len);
        self.diseqs.truncate(mark.diseqs_len);
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
            self.marks.len()
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
