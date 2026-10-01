// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! A clause tableau that drives an IPASIR-UP `ExternalPropagator`.
//!
//! The search is depth-first over one open branch. Each decision level is a
//! branch point. Branching picks a literal of an open (unsatisfied) clause.
//! There is no clause learning and there are no restarts; the only clauses
//! are the input clauses and the lemmas supplied by the propagator.
//!
//! A falsified clause `C` whose highest level `k` holds exactly one literal
//! asserts that literal at the second-highest level of `C`. Otherwise the
//! branch below decision `k` is closed and the decision is flipped at level
//! `k - 1`. Each step lexicographically increases the vector of per-level
//! assignment counts, so the search terminates for a fixed clause set.
//!
//! Like CaDiCaL with chronological backtracking, a lemma that is unit under
//! lower levels is assigned at that lower level without backtracking. Such
//! literals survive backtracks above their level and are notified again.

use crate::debug_println;
use cadical_sys::{ExternalPropagator, ProofTracer, Status, Terminator};
use std::cell::RefCell;
use std::rc::Rc;

/// How a literal came to be on the branch
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Reason {
    Decision,
    /// The negation of a closed branch point; its dependencies are in `flip_deps`
    Flip,
    Clause(usize),
}

/// Result of handling a falsified clause
enum Closure {
    Unsat,
    Continue,
}

/// Result of adding a clause to the current branch
#[derive(PartialEq, Eq)]
enum Added {
    Unsat,
    /// The branch changed: an assignment, a closure or a backjump
    Changed,
    Unchanged,
}

#[derive(Default)]
pub struct TableauStats {
    pub decisions: u64,
    pub closures: u64,
    pub flips: u64,
    pub asserts: u64,
    pub model_checks: u64,
    pub external_clauses: u64,
}

pub struct SatTableau {
    /// Clauses not yet given to the search (input before `solve`)
    input: Vec<Vec<i32>>,
    /// Clause literals; positions 0 and 1 are watched when the length is >= 2
    clauses: Vec<Vec<i32>>,
    /// Indexed by `lit_index(l)`: clauses watching `l`
    watches: Vec<Vec<usize>>,
    /// Per variable: 1 true, -1 false, 0 unassigned
    vals: Vec<i8>,
    levels: Vec<usize>,
    reasons: Vec<Reason>,
    /// Per variable: decision levels a `Flip` literal depends on
    flip_deps: Vec<Vec<usize>>,
    /// Scratch marks for `dependencies`
    seen: Vec<bool>,
    /// Per variable: the propagator level at which it was notified
    notified: Vec<Option<usize>>,
    observed: Vec<bool>,
    /// The branch, in assignment order (levels are not monotone)
    trail: Vec<i32>,
    /// Decision literal of each level (`decisions[l - 1]` for level `l`)
    decisions: Vec<i32>,
    /// Trail entries before this index have been propagated
    qhead: usize,
    /// Trail entries before this index have been notified if observed
    notify_head: usize,
    /// Clauses before this index were satisfied when last scanned
    open_cursor: usize,
    observed_queue: Rc<RefCell<Vec<i32>>>,
    pub stats: TableauStats,
}

fn lit_index(lit: i32) -> usize {
    2 * lit.unsigned_abs() as usize + usize::from(lit < 0)
}

fn lit_value(vals: &[i8], lit: i32) -> i8 {
    let v = vals[lit.unsigned_abs() as usize];
    if lit < 0 { -v } else { v }
}

impl Default for SatTableau {
    fn default() -> Self {
        Self::new()
    }
}

impl SatTableau {
    pub fn new() -> Self {
        SatTableau {
            input: vec![],
            clauses: vec![],
            watches: vec![vec![], vec![]],
            vals: vec![0],
            levels: vec![0],
            reasons: vec![Reason::Decision],
            flip_deps: vec![vec![]],
            seen: vec![false],
            notified: vec![None],
            observed: vec![false],
            trail: vec![],
            decisions: vec![],
            qhead: 0,
            notify_head: 0,
            open_cursor: 0,
            observed_queue: Rc::new(RefCell::new(vec![])),
            stats: TableauStats::default(),
        }
    }

    /// The queue through which the propagator registers observed variables
    pub fn observed_queue(&self) -> Rc<RefCell<Vec<i32>>> {
        Rc::clone(&self.observed_queue)
    }

    pub fn add_clause(&mut self, clause: &[i32]) {
        self.input.push(clause.to_vec());
    }

    fn level(&self) -> usize {
        self.decisions.len()
    }

    fn ensure_var(&mut self, var: usize) {
        if var >= self.vals.len() {
            let n = var + 1;
            self.vals.resize(n, 0);
            self.levels.resize(n, 0);
            self.reasons.resize(n, Reason::Decision);
            self.flip_deps.resize(n, vec![]);
            self.seen.resize(n, false);
            self.notified.resize(n, None);
            self.observed.resize(n, false);
            self.watches.resize(2 * n, vec![]);
        }
    }

    fn num_vars(&self) -> usize {
        self.vals.len() - 1
    }

    fn value(&self, lit: i32) -> i8 {
        lit_value(&self.vals, lit)
    }

    fn lit_level(&self, lit: i32) -> usize {
        self.levels[lit.unsigned_abs() as usize]
    }

    fn assign(&mut self, lit: i32, level: usize, reason: Reason) {
        let var = lit.unsigned_abs() as usize;
        debug_assert_eq!(self.vals[var], 0);
        debug_assert!(level <= self.level());
        self.vals[var] = if lit > 0 { 1 } else { -1 };
        self.levels[var] = level;
        self.reasons[var] = reason;
        self.trail.push(lit);
    }

    fn drain_observed(&mut self) {
        let vars: Vec<i32> = std::mem::take(&mut *self.observed_queue.borrow_mut());
        for var in vars {
            let var = var.unsigned_abs() as usize;
            self.ensure_var(var);
            if !self.observed[var] {
                self.observed[var] = true;
                if self.vals[var] != 0 {
                    // Rare: observed after assignment, so rescan for notification.
                    self.notify_head = 0;
                }
            }
        }
    }

    /// Notify the propagator of observed assignments not yet notified
    fn notify_pending(&mut self, prop: &mut dyn ExternalPropagator) {
        self.drain_observed();
        if self.notify_head >= self.trail.len() {
            return;
        }
        let level = self.level();
        let mut batch = vec![];
        for &lit in &self.trail[self.notify_head..] {
            let var = lit.unsigned_abs() as usize;
            if self.observed[var] && self.notified[var].is_none() {
                self.notified[var] = Some(level);
                batch.push(lit);
            }
        }
        self.notify_head = self.trail.len();
        if !batch.is_empty() {
            prop.notify_assignment(&batch);
            self.drain_observed();
        }
    }

    /// Undo every assignment above `target`, keeping lower-level literals
    /// that were assigned out of order.
    fn backtrack(&mut self, target: usize, prop: &mut dyn ExternalPropagator) {
        if target >= self.level() {
            return;
        }
        prop.notify_backtrack(target);
        self.drain_observed();
        let old_qhead = self.qhead;
        let mut new_qhead = 0;
        let mut kept = 0;
        let mut renotify_from = usize::MAX;
        for i in 0..self.trail.len() {
            let lit = self.trail[i];
            let var = lit.unsigned_abs() as usize;
            if self.levels[var] <= target {
                if self.notified[var].is_some_and(|l| l > target) {
                    // The propagator undid this notification with its level.
                    self.notified[var] = None;
                    renotify_from = renotify_from.min(kept);
                }
                if self.notified[var].is_none() {
                    renotify_from = renotify_from.min(kept);
                }
                self.trail[kept] = lit;
                kept += 1;
                if i < old_qhead {
                    new_qhead = kept;
                }
            } else {
                self.vals[var] = 0;
                self.notified[var] = None;
            }
        }
        self.trail.truncate(kept);
        self.qhead = new_qhead;
        self.notify_head = renotify_from.min(kept);
        self.decisions.truncate(target);
        self.open_cursor = 0;
    }

    /// Move the watches of clause `c` to positions `i` and `j`
    fn rewatch(&mut self, c: usize, i: usize, j: usize) {
        debug_assert!(i != j);
        let old = [self.clauses[c][0], self.clauses[c][1]];
        for lit in old {
            self.watches[lit_index(lit)].retain(|&d| d != c);
        }
        let cl = &mut self.clauses[c];
        cl.swap(0, i);
        let j = if j == 0 { i } else { j };
        cl.swap(1, j);
        let new = [cl[0], cl[1]];
        for lit in new {
            self.watches[lit_index(lit)].push(c);
        }
    }

    /// Unit propagation to fixpoint. Returns a falsified clause, if any.
    fn propagate(&mut self) -> Option<usize> {
        while self.qhead < self.trail.len() {
            let false_lit = -self.trail[self.qhead];
            self.qhead += 1;
            let mut ws = std::mem::take(&mut self.watches[lit_index(false_lit)]);
            let mut i = 0;
            let mut j = 0;
            let mut conflict = None;
            while i < ws.len() {
                let c = ws[i];
                i += 1;
                let cl = &mut self.clauses[c];
                if cl[0] == false_lit {
                    cl.swap(0, 1);
                }
                debug_assert_eq!(cl[1], false_lit);
                if lit_value(&self.vals, cl[0]) == 1 {
                    ws[j] = c;
                    j += 1;
                    continue;
                }
                if let Some(k) = (2..cl.len()).find(|&k| lit_value(&self.vals, cl[k]) != -1) {
                    cl.swap(1, k);
                    let new_watch = cl[1];
                    self.watches[lit_index(new_watch)].push(c);
                    continue;
                }
                ws[j] = c;
                j += 1;
                let first = cl[0];
                if lit_value(&self.vals, first) == 0 {
                    let level = cl[1..]
                        .iter()
                        .map(|l| self.levels[l.unsigned_abs() as usize])
                        .max()
                        .unwrap_or(0);
                    self.assign(first, level, Reason::Clause(c));
                } else {
                    conflict = Some(c);
                    while i < ws.len() {
                        ws[j] = ws[i];
                        i += 1;
                        j += 1;
                    }
                }
            }
            ws.truncate(j);
            let slot = &mut self.watches[lit_index(false_lit)];
            ws.append(slot);
            *slot = ws;
            if conflict.is_some() {
                // The rest of the list was not visited, and an out-of-order
                // literal can survive the backtrack, so propagate it again.
                self.qhead -= 1;
                return conflict;
            }
        }
        None
    }

    /// Close or repair the branch given a clause all of whose literals are false
    fn close(&mut self, c: usize, prop: &mut dyn ExternalPropagator) -> Closure {
        self.stats.closures += 1;
        let cl = &self.clauses[c];
        if cl.is_empty() {
            return Closure::Unsat;
        }
        // Positions of the highest and second-highest level literals
        let mut top = 0;
        for (p, &l) in cl.iter().enumerate() {
            if self.lit_level(l) > self.lit_level(cl[top]) {
                top = p;
            }
        }
        let k = self.lit_level(cl[top]);
        if k == 0 {
            return Closure::Unsat;
        }
        let at_top = cl.iter().filter(|&&l| self.lit_level(l) == k).count();
        let second = (0..cl.len())
            .filter(|&p| p != top)
            .max_by_key(|&p| (self.lit_level(cl[p]) == k, self.lit_level(cl[p])));
        if let Some(second) = second {
            self.rewatch(c, top, second);
        }
        if at_top == 1 {
            // Assert the unique top literal where the rest of C is already false.
            let j = if self.clauses[c].len() > 1 {
                self.lit_level(self.clauses[c][1])
            } else {
                0
            };
            let lit = self.clauses[c][0];
            self.backtrack(j, prop);
            self.assign(lit, j, Reason::Clause(c));
            self.stats.asserts += 1;
        } else {
            // Dependency-directed backjumping: close the latest branch point
            // the conflict depends on, and flip it where its other
            // dependencies hold.
            let mut deps = self.dependencies(c);
            let Some(k) = deps.pop() else {
                return Closure::Unsat;
            };
            let j = deps.last().copied().unwrap_or(0);
            let decision = self.decisions[k - 1];
            self.backtrack(k - 1, prop);
            self.assign(-decision, j, Reason::Flip);
            self.flip_deps[decision.unsigned_abs() as usize] = deps;
            self.stats.flips += 1;
        }
        Closure::Continue
    }

    /// Sorted decision levels that the falsity of clause `c` depends on
    fn dependencies(&mut self, c: usize) -> Vec<usize> {
        let mut deps = vec![];
        let mut touched = vec![];
        let mut stack: Vec<usize> = self.clauses[c]
            .iter()
            .map(|l| l.unsigned_abs() as usize)
            .collect();
        while let Some(v) = stack.pop() {
            if self.seen[v] || self.levels[v] == 0 {
                continue;
            }
            self.seen[v] = true;
            touched.push(v);
            match self.reasons[v] {
                Reason::Decision => deps.push(self.levels[v]),
                Reason::Flip => deps.extend_from_slice(&self.flip_deps[v]),
                Reason::Clause(r) => stack.extend(
                    self.clauses[r]
                        .iter()
                        .map(|l| l.unsigned_abs() as usize)
                        .filter(|&u| u != v),
                ),
            }
        }
        for v in touched {
            self.seen[v] = false;
        }
        deps.sort_unstable();
        deps.dedup();
        deps
    }

    /// Add a clause to the search, handling it under the current branch
    fn add_to_search(&mut self, clause: &[i32], prop: &mut dyn ExternalPropagator) -> Added {
        let mut lits: Vec<i32> = vec![];
        for &l in clause {
            self.ensure_var(l.unsigned_abs() as usize);
            if lits.contains(&-l) {
                return Added::Unchanged; // tautology
            }
            if !lits.contains(&l) {
                lits.push(l);
            }
        }
        if lits.is_empty() {
            return Added::Unsat;
        }
        // Order: true, then unassigned, then false by decreasing level
        lits.sort_by_key(|&l| {
            let v = self.value(l);
            (-v, std::cmp::Reverse(self.lit_level(l)))
        });
        let c = self.clauses.len();
        self.clauses.push(lits);
        let cl = &self.clauses[c];
        if cl.len() >= 2 {
            self.watches[lit_index(cl[0])].push(c);
            self.watches[lit_index(cl[1])].push(c);
        }
        let first = cl[0];
        match self.value(first) {
            // An unwatched unit must hold at the root to survive backtracks.
            1 if cl.len() == 1 && self.lit_level(first) > 0 => {
                self.backtrack(0, prop);
                self.assign(first, 0, Reason::Clause(c));
                Added::Changed
            }
            1 => Added::Unchanged,
            0 => {
                if cl.len() >= 2 && self.value(cl[1]) == 0 {
                    return Added::Unchanged;
                }
                let level = if cl.len() >= 2 {
                    self.lit_level(cl[1])
                } else {
                    0
                };
                self.assign(first, level, Reason::Clause(c));
                Added::Changed
            }
            _ => match self.close(c, prop) {
                Closure::Unsat => Added::Unsat,
                Closure::Continue => Added::Changed,
            },
        }
    }

    fn record_clause(tracer: Option<&RefCell<dyn ProofTracer + '_>>, id: usize, clause: &[i32]) {
        if let Some(tracer) = tracer {
            tracer
                .borrow_mut()
                .add_original_clause(id as i64 + 1, false, clause, false);
        }
    }

    /// Ask the propagator for lemmas, stopping after one changes the branch
    fn add_external_clauses(
        &mut self,
        prop: &mut dyn ExternalPropagator,
        tracer: Option<&RefCell<dyn ProofTracer + '_>>,
    ) -> Added {
        let mut forgettable = false;
        while prop.cb_has_external_clause(&mut forgettable) {
            let mut clause = vec![];
            loop {
                let lit = prop.cb_add_external_clause_lit();
                if lit == 0 {
                    break;
                }
                clause.push(lit);
            }
            self.drain_observed();
            self.stats.external_clauses += 1;
            Self::record_clause(tracer, self.clauses.len(), &clause);
            match self.add_to_search(&clause, prop) {
                Added::Unchanged => {}
                other => return other,
            }
        }
        Added::Unchanged
    }

    /// First unassigned literal of an open clause, else any unassigned variable
    fn pick_branch(&mut self) -> Option<i32> {
        while self.open_cursor < self.clauses.len() {
            let cl = &self.clauses[self.open_cursor];
            if !cl.iter().any(|&l| lit_value(&self.vals, l) == 1)
                && let Some(&l) = cl.iter().find(|&&l| lit_value(&self.vals, l) == 0)
            {
                return Some(l);
            }
            self.open_cursor += 1;
        }
        (1..=self.num_vars())
            .find(|&v| self.vals[v] == 0)
            .map(|v| v as i32)
    }

    fn decide(&mut self, lit: i32, prop: &mut dyn ExternalPropagator) {
        self.stats.decisions += 1;
        prop.notify_new_decision_level();
        self.drain_observed();
        self.decisions.push(lit);
        let level = self.level();
        self.assign(lit, level, Reason::Decision);
    }

    /// Run the search. The tracer, if given, receives every clause once.
    pub fn solve(
        &mut self,
        prop: &mut dyn ExternalPropagator,
        tracer: Option<&RefCell<dyn ProofTracer + '_>>,
        mut terminator: Option<&mut dyn Terminator>,
    ) -> Status {
        self.drain_observed();
        let input = std::mem::take(&mut self.input);
        for clause in &input {
            Self::record_clause(tracer, self.clauses.len(), clause);
            if self.add_to_search(clause, prop) == Added::Unsat {
                return Status::UNSATISFIABLE;
            }
        }
        let mut steps: u64 = 0;
        loop {
            steps += 1;
            if steps.is_multiple_of(20000) {
                debug_println!(
                    2,
                    0,
                    "TABLEAU: level {} trail {} vars {} clauses {} decisions {} flips {} asserts {} checks {}",
                    self.level(),
                    self.trail.len(),
                    self.num_vars(),
                    self.clauses.len(),
                    self.stats.decisions,
                    self.stats.flips,
                    self.stats.asserts,
                    self.stats.model_checks
                );
            }
            if steps.is_multiple_of(64) && terminator.as_mut().is_some_and(|t| t.terminated()) {
                return Status::UNKNOWN;
            }
            if let Some(c) = self.propagate() {
                match self.close(c, prop) {
                    Closure::Unsat => return Status::UNSATISFIABLE,
                    Closure::Continue => continue,
                }
            }
            self.notify_pending(prop);
            let lit = prop.cb_propagate();
            if lit != 0 {
                let mut reason = vec![];
                loop {
                    let l = prop.cb_add_reason_clause_lit(lit);
                    if l == 0 {
                        break;
                    }
                    reason.push(l);
                }
                self.drain_observed();
                Self::record_clause(tracer, self.clauses.len(), &reason);
                match self.add_to_search(&reason, prop) {
                    Added::Unsat => return Status::UNSATISFIABLE,
                    _ => continue,
                }
            }
            match self.add_external_clauses(prop, tracer) {
                Added::Unsat => return Status::UNSATISFIABLE,
                Added::Changed => continue,
                Added::Unchanged => {}
            }
            if self.qhead < self.trail.len() || self.notify_head < self.trail.len() {
                continue;
            }
            let suggested = prop.cb_decide();
            self.drain_observed();
            let branch = if suggested != 0 {
                self.ensure_var(suggested.unsigned_abs() as usize);
                (self.value(suggested) == 0).then_some(suggested)
            } else {
                None
            };
            if let Some(lit) = branch.or_else(|| self.pick_branch()) {
                self.decide(lit, prop);
                continue;
            }
            // Every variable is assigned and every clause is satisfied.
            self.stats.model_checks += 1;
            let model: Vec<i32> = (1..=self.num_vars())
                .filter(|&v| self.observed[v])
                .map(|v| {
                    if self.vals[v] > 0 {
                        v as i32
                    } else {
                        -(v as i32)
                    }
                })
                .collect();
            if prop.cb_check_found_model(&model) {
                return Status::SATISFIABLE;
            }
            self.drain_observed();
            let had_clause = self.stats.external_clauses;
            match self.add_external_clauses(prop, tracer) {
                Added::Unsat => return Status::UNSATISFIABLE,
                Added::Changed => continue,
                Added::Unchanged => {}
            }
            let fresh_vars = (1..=self.num_vars()).any(|v| self.vals[v] == 0);
            if self.stats.external_clauses == had_clause && !fresh_vars {
                // A rejection without a lemma accepts the model, as in CaDiCaL.
                return Status::SATISFIABLE;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Tracks the notified assignment the way Sundance's propagator does and
    /// reveals hidden clauses lazily, either eagerly on falsification or at
    /// the model check.
    struct LazyProp {
        level: usize,
        /// Per variable: (propagator level + 1) * sign, 0 if unassigned
        assignment: Vec<i32>,
        hidden: Vec<Vec<i32>>,
        revealed: Vec<bool>,
        eager: bool,
        queue: Vec<Vec<i32>>,
    }

    impl LazyProp {
        fn new(num_vars: usize, hidden: Vec<Vec<i32>>, eager: bool) -> Self {
            let n = hidden.len();
            LazyProp {
                level: 0,
                assignment: vec![0; num_vars + 1],
                hidden,
                revealed: vec![false; n],
                eager,
                queue: vec![],
            }
        }

        fn falsified(&self, clause: &[i32]) -> bool {
            clause.iter().all(|&l| {
                let a = self.assignment[l.unsigned_abs() as usize];
                a != 0 && (a > 0) != (l > 0)
            })
        }

        fn reveal_falsified(&mut self) {
            for i in 0..self.hidden.len() {
                if !self.revealed[i] && self.falsified(&self.hidden[i]) {
                    self.revealed[i] = true;
                    self.queue.push(self.hidden[i].clone());
                }
            }
        }
    }

    impl ExternalPropagator for LazyProp {
        fn notify_assignment(&mut self, lits: &[i32]) {
            for &l in lits {
                let v = l.unsigned_abs() as usize;
                assert_eq!(self.assignment[v], 0, "variable {v} notified twice");
                let sign = if l > 0 { 1 } else { -1 };
                self.assignment[v] = (self.level as i32 + 1) * sign;
            }
            if self.eager {
                self.reveal_falsified();
            }
        }

        fn notify_new_decision_level(&mut self) {
            self.level += 1;
        }

        fn notify_backtrack(&mut self, new_level: usize) {
            assert!(new_level < self.level);
            for a in self.assignment.iter_mut() {
                if a.unsigned_abs() as usize > new_level + 1 {
                    *a = 0;
                }
            }
            self.level = new_level;
        }

        fn cb_check_found_model(&mut self, model: &[i32]) -> bool {
            for &l in model {
                let a = self.assignment[l.unsigned_abs() as usize];
                assert!(
                    a != 0 && (a > 0) == (l > 0),
                    "model literal {l} not notified"
                );
            }
            self.reveal_falsified();
            self.queue.is_empty()
        }

        fn cb_has_external_clause(&mut self, is_forgettable: &mut bool) -> bool {
            *is_forgettable = false;
            !self.queue.is_empty()
        }

        fn cb_add_external_clause_lit(&mut self) -> i32 {
            let clause = self.queue.last_mut().unwrap();
            match clause.pop() {
                Some(l) => l,
                None => {
                    self.queue.pop();
                    0
                }
            }
        }
    }

    fn brute_force(num_vars: usize, clauses: &[Vec<i32>]) -> bool {
        (0..1u32 << num_vars).any(|m| {
            clauses.iter().all(|c| {
                c.iter().any(|&l| {
                    let bit = (m >> (l.unsigned_abs() - 1)) & 1 == 1;
                    bit == (l > 0)
                })
            })
        })
    }

    /// Small deterministic generator (xorshift)
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    fn random_cnf(rng: &mut Rng, num_vars: usize, num_clauses: usize) -> Vec<Vec<i32>> {
        (0..num_clauses)
            .map(|_| {
                let len = 1 + rng.below(3) as usize;
                (0..len)
                    .map(|_| {
                        let v = 1 + rng.below(num_vars as u64) as i32;
                        if rng.below(2) == 0 { v } else { -v }
                    })
                    .collect()
            })
            .collect()
    }

    fn run(num_vars: usize, visible: &[Vec<i32>], hidden: Vec<Vec<i32>>, eager: bool) -> Status {
        let mut tableau = SatTableau::new();
        for v in 1..=num_vars {
            tableau.observed_queue().borrow_mut().push(v as i32);
        }
        // Mention every variable so the model is total over them.
        tableau.ensure_var(num_vars);
        for c in visible {
            tableau.add_clause(c);
        }
        let mut prop = LazyProp::new(num_vars, hidden, eager);
        let status = tableau.solve(&mut prop, None, None);
        if status == Status::SATISFIABLE {
            let all: Vec<Vec<i32>> = visible.iter().chain(prop.hidden.iter()).cloned().collect();
            for c in &all {
                assert!(
                    c.iter().any(|&l| tableau.value(l) == 1),
                    "clause {c:?} not satisfied"
                );
            }
        }
        status
    }

    #[test]
    fn simple_cases() {
        assert!(run(1, &[vec![1], vec![-1]], vec![], false) == Status::UNSATISFIABLE);
        assert!(run(2, &[vec![1, 2], vec![-1, 2]], vec![], false) == Status::SATISFIABLE);
        assert!(run(2, &[vec![1, 2]], vec![vec![-1], vec![-2]], false) == Status::UNSATISFIABLE);
        assert!(run(2, &[vec![]], vec![], false) == Status::UNSATISFIABLE);
    }

    #[test]
    fn agrees_with_brute_force() {
        let mut rng = Rng(0x9e3779b97f4a7c15);
        for round in 0..20000 {
            let num_vars = 1 + rng.below(10) as usize;
            let num_clauses = rng.below(4 * num_vars as u64 + 4) as usize;
            let cnf = random_cnf(&mut rng, num_vars, num_clauses);
            let split = rng.below(num_clauses as u64 + 1) as usize;
            let (visible, hidden) = cnf.split_at(split);
            let expected = brute_force(num_vars, &cnf);
            for eager in [false, true] {
                let status = run(num_vars, visible, hidden.to_vec(), eager);
                let got = status == Status::SATISFIABLE;
                assert!(
                    status != Status::UNKNOWN && got == expected,
                    "round {round} eager {eager}: expected sat={expected}, cnf {cnf:?} split {split}"
                );
            }
        }
    }
}
