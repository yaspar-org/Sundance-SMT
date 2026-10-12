// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Conformance tests for [`EgraphTrait`] implementations.
//!
//! Every test here is generic over the backend and is instantiated for each
//! implementation at the bottom of the file. Each pins one behaviour sundance
//! relies on that the trait's types do not express; the obligations and how
//! they were found are written up in the trait's documentation
//! (`traits.rs`). Two oracles are shared:
//!
//! - **Explanation oracle** ([`Harness::entails`]): an antecedent set is
//!   valid only if congruence closure over the *client's* terms (the syntax
//!   the test registered, not the backend's nodes) derives the conclusion
//!   from the cited pairs alone. Backends that store canonical children or
//!   share one node between syntactically different terms produce paths that
//!   are valid for their nodes and miss equalities the client needs.
//! - **Asserted-pair oracle** ([`Harness::all_asserted`]): sundance turns a
//!   cited pair into a clause literal with `SolverState::make_eq`, which
//!   allocates a fresh, unassigned atom for a pair it has never seen; such a
//!   clause is not a conflict. Every cited pair must be one the client asserted.

use super::repr::{Op, Pattern};
use super::traits::{Conflict, EgraphTrait};
use rustc_hash::{FxHashMap, FxHashSet};
use yaspar_ir::ast::*;

/// A backend under test plus the client-side record the oracles need: the
/// syntax of every registered term and every asserted pair.
struct Harness<E> {
    e: E,
    syn: FxHashMap<u32, (Op, Vec<u32>)>,
    /// Asserted pairs with the decision level they were asserted at; a
    /// backtrack drops the popped ones, so a conflict citing an assertion
    /// that no longer holds fails the asserted-pair oracle.
    asserted: Vec<((u32, u32), usize)>,
    level: usize,
    t: u32,
    f: u32,
}

impl<E: EgraphTrait<Op = Op, TermId = u32>> Harness<E> {
    fn new(mut e: E) -> Self {
        let t = e.register_constant(Op::Constant("true".to_string()));
        let f = e.register_constant(Op::Constant("false".to_string()));
        let mut syn = FxHashMap::default();
        syn.insert(t, (Op::Constant("true".to_string()), vec![]));
        syn.insert(f, (Op::Constant("false".to_string()), vec![]));
        Harness {
            e,
            syn,
            asserted: vec![],
            level: 0,
            t,
            f,
        }
    }

    /// An uninterpreted constant (a declared `Global`): sundance registers it
    /// with `register_term(Op::App(name), [])`. `register_constant` and
    /// `Op::Constant` are reserved for literal values (numerals, strings,
    /// `true`, `false`), which are pairwise distinct.
    fn c(&mut self, name: &str) -> u32 {
        self.term(Op::App(name.to_string()), &[])
    }

    /// A literal value (`Op::Constant`), registered as sundance does.
    fn lit(&mut self, value: &str) -> u32 {
        let op = Op::Constant(value.to_string());
        let id = self.e.register_constant(op.clone());
        self.syn.insert(id, (op, vec![]));
        id
    }

    /// `dynamic = true`: the contract is that a congruent registration is in
    /// its class immediately (sundance registers instance terms this way).
    fn app(&mut self, f: &str, ch: &[u32]) -> u32 {
        self.term(Op::App(f.to_string()), ch)
    }

    fn term(&mut self, op: Op, ch: &[u32]) -> u32 {
        let id = self.e.register_term(op.clone(), ch, true);
        self.syn.insert(id, (op, ch.to_vec()));
        id
    }

    fn eq(&mut self, a: u32, b: u32) -> Option<Conflict<u32>> {
        self.asserted.push(((a, b), self.level));
        self.e.assert_equal(a, b).conflict
    }

    fn level_up(&mut self) {
        self.e.notify_new_decision_level();
        self.level += 1;
    }

    fn backtrack(&mut self, level: usize) {
        self.e.backtrack_to(level);
        self.level = level;
        self.asserted.retain(|&(_, l)| l <= level);
    }

    fn neq(&mut self, a: u32, b: u32, lit: i32) -> Option<Conflict<u32>> {
        self.e.assert_disequal(a, b, lit).conflict
    }

    /// Congruence closure over the client's syntax: do `eqs` alone entail
    /// `x = y`? `=` is order-free, as the trait requires.
    fn entails(&self, eqs: &[(u32, u32)], x: u32, y: u32) -> bool {
        let mut terms: Vec<u32> = Vec::new();
        let mut seen: FxHashSet<u32> = FxHashSet::default();
        let mut stack: Vec<u32> = eqs
            .iter()
            .flat_map(|&(a, b)| [a, b])
            .chain([x, y])
            .collect();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            terms.push(t);
            if let Some((_, ch)) = self.syn.get(&t) {
                stack.extend(ch.iter().copied());
            }
        }
        let idx: FxHashMap<u32, usize> = terms.iter().enumerate().map(|(i, &t)| (t, i)).collect();
        let mut p: Vec<usize> = (0..terms.len()).collect();
        fn find(p: &mut [usize], mut i: usize) -> usize {
            while p[i] != i {
                p[i] = p[p[i]];
                i = p[i];
            }
            i
        }
        for &(a, b) in eqs {
            let (ra, rb) = (find(&mut p, idx[&a]), find(&mut p, idx[&b]));
            p[ra] = rb;
        }
        loop {
            let mut changed = false;
            let mut sig: FxHashMap<(String, Vec<usize>), usize> = FxHashMap::default();
            for (i, t) in terms.iter().enumerate() {
                let Some((op, ch)) = self.syn.get(t) else {
                    continue;
                };
                let mut c: Vec<usize> = ch.iter().map(|x| find(&mut p, idx[x])).collect();
                if *op == Op::Eq {
                    c.sort_unstable();
                }
                let k = (format!("{op:?}"), c);
                match sig.get(&k) {
                    Some(&j) => {
                        let (ri, rj) = (find(&mut p, i), find(&mut p, j));
                        if ri != rj {
                            p[ri] = rj;
                            changed = true;
                        }
                    }
                    None => {
                        sig.insert(k, i);
                    }
                }
            }
            if !changed {
                break;
            }
        }
        find(&mut p, idx[&x]) == find(&mut p, idx[&y])
    }

    /// The registered syntax of `t`, with ids, for failure messages.
    fn show(&self, t: u32) -> String {
        match self.syn.get(&t) {
            Some((op, ch)) if ch.is_empty() => format!("{}#{t}", op.to_function_map_key()),
            Some((op, ch)) => format!(
                "({} {})#{t}",
                op.to_function_map_key(),
                ch.iter()
                    .map(|&c| self.show(c))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            None => format!("?#{t}"),
        }
    }

    fn all_asserted(&self, eqs: &[(u32, u32)]) -> bool {
        eqs.iter().all(|&(a, b)| {
            self.asserted
                .iter()
                .any(|&((x, y), _)| (x, y) == (a, b) || (x, y) == (b, a))
        })
    }

    /// Both oracles on a conflict.
    fn check_conflict(&self, c: &Conflict<u32>, what: &str) {
        let (x, y) = c.disequality;
        assert!(
            self.entails(&c.equalities, x, y),
            "{what}: the antecedents {:?} do not entail {x} = {y} over the client's terms",
            c.equalities
        );
        assert!(
            self.all_asserted(&c.equalities),
            "{what}: a cited pair was never asserted: {:?}",
            c.equalities
        );
    }
}

// --- 1. Term identity and registration --------------------------------------

/// A term registered at a decision level stays a valid id after that level
/// is popped: sundance never re-registers.
fn ids_survive_backtrack<E: EgraphTrait<Op = Op, TermId = u32>>(e: E) {
    let mut h = Harness::new(e);
    let a = h.c("a");
    let b = h.c("b");
    h.level_up();
    let fa = h.app("f", &[a]);
    let fb = h.app("f", &[b]);
    h.backtrack(0);
    assert!(!h.e.are_equal(fa, fb));
    assert!(h.eq(a, b).is_none());
    assert!(
        h.e.are_equal(fa, fb),
        "congruence over terms registered at a popped level"
    );
}

/// A registration congruent to an existing term is in its class at once.
fn congruent_registration_merges_now<E: EgraphTrait<Op = Op, TermId = u32>>(e: E) {
    let mut h = Harness::new(e);
    let a = h.c("a");
    let b = h.c("b");
    let fa = h.app("f", &[a]);
    assert!(h.eq(a, b).is_none());
    let fb = h.app("f", &[b]);
    assert!(h.e.are_equal(fa, fb));
}

/// `(= a b)` and `(= b a)` are one class.
fn eq_is_commutative<E: EgraphTrait<Op = Op, TermId = u32>>(e: E) {
    let mut h = Harness::new(e);
    let a = h.c("a");
    let b = h.c("b");
    let ab = h.term(Op::Eq, &[a, b]);
    let ba = h.term(Op::Eq, &[b, a]);
    assert!(h.e.are_equal(ab, ba));
}

/// Two different literal values (`register_constant`) are distinct: merging
/// them is a conflict without a disequality literal, explained by the merges
/// that joined them.
fn distinct_literals_conflict<E: EgraphTrait<Op = Op, TermId = u32>>(e: E) {
    let mut h = Harness::new(e);
    let one = h.lit("1");
    let two = h.lit("2");
    let x = h.c("x");
    assert!(h.eq(x, one).is_none());
    let c = h.eq(x, two).expect("x = 1 and x = 2: 1 = 2");
    assert_eq!(c.diseq_lit, None);
    let (p, q) = c.disequality;
    assert!(
        (p, q) == (one, two)
            || (p, q) == (two, one)
            || h.e.are_equal(p, one) && h.e.are_equal(q, two),
        "the disequality names the two literals: {:?}",
        c.disequality
    );
    assert!(
        h.entails(&c.equalities, one, two),
        "{:?} do not entail 1 = 2",
        c.equalities
    );
}

// --- 2. Truth values ---------------------------------------------------------

/// Two congruent atoms asserted to opposite values collapse true into false:
/// exactly one conflict, valid for the client's terms, undone by backtrack.
fn true_false_collision<E: EgraphTrait<Op = Op, TermId = u32>>(e: E) {
    let mut h = Harness::new(e);
    let a = h.c("a");
    let b = h.c("b");
    let pa = h.app("p", &[a]);
    let pb = h.app("p", &[b]);
    let (t, f) = (h.t, h.f);
    h.level_up();
    assert!(h.eq(pa, t).is_none());
    assert!(h.eq(pb, f).is_none());
    h.level_up();
    let c = h
        .eq(a, b)
        .expect("p(a) = true, p(b) = false, a = b: true = false");
    h.check_conflict(&c, "true=false collision");
    h.backtrack(1);
    assert!(!h.e.are_equal(t, f));
    assert!(!h.e.true_false_conflict_pending());
}

// --- 3. Conflicts ------------------------------------------------------------

/// A disequality between already-equal terms is a conflict now, carrying the
/// asserting literal.
fn disequal_on_equal_conflicts_now<E: EgraphTrait<Op = Op, TermId = u32>>(e: E) {
    let mut h = Harness::new(e);
    let a = h.c("a");
    let b = h.c("b");
    let c = h.c("c");
    assert!(h.eq(a, b).is_none());
    assert!(h.eq(b, c).is_none());
    let k = h.neq(a, c, 7).expect("a = b = c contradicts a != c");
    // Either convention is correct: the driver (`solver_state.rs`, the
    // disequality branch of `process_assignment`) appends the equality
    // atom's literal to the clause itself, so a backend may return `None`
    // here (basic) or the asserting literal (semper), never another one.
    assert!(
        matches!(k.diseq_lit, None | Some(7)),
        "diseq_lit {:?}",
        k.diseq_lit
    );
    h.check_conflict(&k, "assert_disequal on equal terms");
}

/// A congruence conflict found by a later merge cites asserted pairs only.
fn congruence_conflict_is_valid<E: EgraphTrait<Op = Op, TermId = u32>>(e: E) {
    let mut h = Harness::new(e);
    let a = h.c("a");
    let b = h.c("b");
    let fa = h.app("f", &[a]);
    let fb = h.app("f", &[b]);
    assert!(h.neq(fa, fb, 3).is_none());
    let k = h.eq(a, b).expect("a = b forces f(a) = f(b)");
    assert_eq!(k.diseq_lit, Some(3));
    h.check_conflict(&k, "congruence conflict");
}

// --- 4. Explanations are complete for the client's terms ---------------------

/// The node of a term created after one of its children merged may store the
/// child's class root; a congruence step through it must still cite the
/// merge. Measured in sundance on Verus: the path-only explanation omitted it
/// (`r@ = route(node!, key!)` in `subtraction.smt2`).
fn explanation_complete_canonical_children<E: EgraphTrait<Op = Op, TermId = u32>>(e: E) {
    let mut h = Harness::new(e);
    let n = h.c("n");
    let k = h.c("k");
    let r = h.c("r");
    let x = h.c("x");
    let y = h.c("y");
    let route = h.app("route", &[n, k]);
    assert!(h.eq(r, route).is_none());
    // Created after r = route(n, k): canonical children would store route's class.
    let lt_r = h.app("lt", &[r, x]);
    let lt_route = h.app("lt", &[route, y]);
    h.level_up();
    assert!(h.neq(lt_r, lt_route, 11).is_none());
    let c = h
        .eq(x, y)
        .expect("r = route(n,k), x = y: lt(r,x) = lt(route,y)");
    h.check_conflict(&c, "canonical children at creation");
}

/// A term registered onto a node another term created (hash-consing under
/// an existing merge) equals that creator only through the merge; a conflict
/// through the creator must cite it.
fn explanation_complete_hashcons_onto_creator<E: EgraphTrait<Op = Op, TermId = u32>>(e: E) {
    let mut h = Harness::new(e);
    let a = h.c("a");
    let b = h.c("b");
    let c = h.c("c");
    let fa = h.app("f", &[a]);
    assert!(h.eq(a, b).is_none());
    let fb = h.app("f", &[b]);
    h.level_up();
    assert!(h.neq(fb, c, 5).is_none());
    let k = h.eq(fa, c).expect("f(a) = c, a = b: f(b) = c");
    h.check_conflict(&k, "hash-cons onto creator");
}

/// `explain_equality` serves the arithmetic and datatype layers for any pair
/// that is currently equal, including pairs never asserted.
fn explain_equality_complete_any_pair<E: EgraphTrait<Op = Op, TermId = u32>>(e: E) {
    let mut h = Harness::new(e);
    let a = h.c("a");
    let b = h.c("b");
    let c = h.c("c");
    let fa = h.app("f", &[a]);
    assert!(h.eq(a, b).is_none());
    let gfb = {
        let fb = h.app("f", &[b]);
        h.app("g", &[fb])
    };
    let gfa = h.app("g", &[fa]);
    assert!(h.eq(b, c).is_none());
    let fc = h.app("f", &[c]);
    for (x, y) in [(fa, fc), (gfa, gfb), (a, c)] {
        let eqs =
            h.e.explain_equality(x, y)
                .unwrap_or_else(|| panic!("{x} and {y} are equal"));
        assert!(
            h.entails(&eqs, x, y),
            "explain_equality({x}, {y}) = {eqs:?} is incomplete"
        );
        assert!(
            h.all_asserted(&eqs),
            "explain_equality({x}, {y}) cites an unasserted pair"
        );
    }
    assert!(
        h.e.explain_equality(fa, h.t).is_none(),
        "unequal pairs have no explanation"
    );
}

/// Random interleavings of registrations, merges, disequalities, levels and
/// backtracks: every conflict passes both oracles. The generator draws from
/// the high bits of an LCG (its low bits cycle with a short period).
/// Number of random seeds: 40 by default, `CONFORMANCE_SEEDS` to raise it.
fn seeds(default: u64) -> u64 {
    std::env::var("CONFORMANCE_SEEDS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(default)
}

fn random_conflicts_are_valid<E: EgraphTrait<Op = Op, TermId = u32>>(mk: impl Fn() -> E) {
    for seed in 1..=seeds(40) {
        let mut h = Harness::new(mk());
        let mut s = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let mut next = |m: usize| {
            s = s
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            ((s >> 33) as usize) % m
        };
        let mut pool: Vec<u32> = (0..4).map(|i| h.c(&format!("c{i}"))).collect();
        let mut level = 0usize;
        let mut log: Vec<String> = pool.iter().map(|&t| format!("reg {}", h.show(t))).collect();
        for step in 0..60 {
            match next(10) {
                0..=2 => {
                    let f = ["f", "g"][next(2)];
                    let x = pool[next(pool.len())];
                    let t = if next(2) == 0 {
                        h.app(f, &[x])
                    } else {
                        let y = pool[next(pool.len())];
                        h.app(f, &[x, y])
                    };
                    log.push(format!("reg {} at level {level}", h.show(t)));
                    pool.push(t);
                }
                3..=5 => {
                    let (x, y) = (pool[next(pool.len())], pool[next(pool.len())]);
                    log.push(format!("eq #{x} #{y} at level {level}"));
                    if let Some(c) = h.eq(x, y) {
                        log.push("  conflict".to_string());
                        h.check_conflict(&c, &format!("seed {seed} step {step} merge"));
                        h.backtrack(level.saturating_sub(1));
                        level = level.saturating_sub(1);
                    }
                }
                6 => {
                    let (x, y) = (pool[next(pool.len())], pool[next(pool.len())]);
                    log.push(format!("neq #{x} #{y} at level {level}"));
                    if x != y
                        && let Some(c) = h.neq(x, y, 100 + step)
                    {
                        log.push("  conflict".to_string());
                        h.check_conflict(&c, &format!("seed {seed} step {step} diseq"));
                        h.backtrack(level.saturating_sub(1));
                        level = level.saturating_sub(1);
                    }
                }
                7 | 8 => {
                    h.level_up();
                    level += 1;
                    log.push(format!("level -> {level}"));
                }
                _ => {
                    let to = next(level + 1);
                    h.backtrack(to);
                    level = to;
                    log.push(format!("backtrack -> {level}"));
                }
            }
            // Explanations of current equalities, conflict or not.
            let (x, y) = (pool[next(pool.len())], pool[next(pool.len())]);
            if x != y && h.e.are_equal(x, y) {
                let eqs = h.e.explain_equality(x, y).expect("equal");
                assert!(
                    h.entails(&eqs, x, y),
                    "seed {seed} step {step}: explain_equality({x}, {y}) = {eqs:?} is incomplete; \
                     {x} = {}, {y} = {}\nlog:\n{}",
                    h.show(x),
                    h.show(y),
                    log.join("\n")
                );
            }
        }
    }
}

// --- 5. Backtracking ---------------------------------------------------------

/// After popping a level, the classes are exactly those of the assertions
/// that remain, whatever was asserted in the popped levels.
fn backtrack_restores_classes<E: EgraphTrait<Op = Op, TermId = u32>>(mk: impl Fn() -> E) {
    let mut h = Harness::new(mk());
    let cs: Vec<u32> = (0..5).map(|i| h.c(&format!("c{i}"))).collect();
    let fs: Vec<u32> = cs.iter().map(|&c| h.app("f", &[c])).collect();
    assert!(h.eq(cs[0], cs[1]).is_none());
    let snapshot = |h: &Harness<E>| -> Vec<bool> {
        let all: Vec<u32> = cs.iter().chain(fs.iter()).copied().collect();
        all.iter()
            .flat_map(|&x| all.iter().map(move |&y| (x, y)))
            .map(|(x, y)| h.e.are_equal(x, y))
            .collect()
    };
    let before = snapshot(&h);
    h.level_up();
    assert!(h.eq(cs[2], cs[3]).is_none());
    h.level_up();
    assert!(h.eq(fs[3], cs[4]).is_none());
    let g = h.app("g", &[fs[2]]);
    let _ = g;
    h.backtrack(0);
    assert_eq!(
        snapshot(&h),
        before,
        "backtrack_to(0) left equalities of popped levels"
    );
}

/// A level-0 disequality is never undone: after any sequence of new levels
/// and backtracks, merging its sides is a conflict. (Found by
/// `differential_basic_against_semper`, seed 764: a backtrack to level 0
/// issued while already at level 0, then new levels and a backtrack to 1.)
fn level0_disequality_survives_backtracks<E: EgraphTrait<Op = Op, TermId = u32>>(e: E) {
    let mut h = Harness::new(e);
    let a = h.c("a");
    let b = h.c("b");
    h.backtrack(0);
    assert!(h.neq(a, b, 9).is_none());
    h.level_up();
    h.level_up();
    h.level_up();
    h.backtrack(1);
    let c = h.eq(a, b).expect("a != b was asserted at level 0");
    h.check_conflict(&c, "level-0 disequality after backtracks");
}

/// The same without the redundant backtrack at level 0.
fn level0_disequality_survives_backtracks_plain<E: EgraphTrait<Op = Op, TermId = u32>>(e: E) {
    let mut h = Harness::new(e);
    let a = h.c("a");
    let b = h.c("b");
    assert!(h.neq(a, b, 9).is_none());
    h.level_up();
    h.level_up();
    h.backtrack(1);
    let c = h.eq(a, b).expect("a != b was asserted at level 0");
    h.check_conflict(&c, "level-0 disequality after backtracks");
}

/// A disequality survives the popping of a later disequality between the
/// same two classes. (Minimized from `differential_basic_against_semper`
/// seed 764 by `minimize_divergence`: the basic backend lost the level-0
/// disequality when a level-2 one over the same classes was popped, and a
/// merge that contradicts it went unreported.)
fn disequality_survives_popped_duplicate<E: EgraphTrait<Op = Op, TermId = u32>>(e: E) {
    let mut h = Harness::new(e);
    let a = h.c("a");
    let b = h.c("b");
    let a2 = h.c("a2");
    let b2 = h.c("b2");
    assert!(h.eq(a, a2).is_none());
    assert!(h.eq(b, b2).is_none());
    assert!(h.neq(a, b, 1).is_none());
    h.level_up();
    h.level_up();
    assert!(h.neq(a2, b2, 2).is_none());
    h.backtrack(1);
    let c = h
        .eq(a, b)
        .expect("a != b (level 0) still holds after popping a2 != b2 (level 2)");
    h.check_conflict(&c, "disequality after a popped duplicate");
}

/// As `disequality_survives_popped_duplicate`, with the later disequality
/// asserted in the opposite orientation (`b2 != a2`), as in seed 764.
fn disequality_survives_popped_reversed_duplicate<E: EgraphTrait<Op = Op, TermId = u32>>(e: E) {
    let mut h = Harness::new(e);
    let a = h.c("a");
    let b = h.c("b");
    let a2 = h.c("a2");
    let b2 = h.c("b2");
    assert!(h.eq(a, a2).is_none());
    assert!(h.eq(b, b2).is_none());
    assert!(h.neq(a, b, 1).is_none());
    h.level_up();
    h.level_up();
    assert!(h.neq(b2, a2, 2).is_none());
    h.backtrack(1);
    let c = h
        .eq(a, b)
        .expect("a != b (level 0) still holds after popping b2 != a2 (level 2)");
    h.check_conflict(&c, "disequality after a popped reversed duplicate");
}

/// The general shape of seed 764: a disequality asserted at level L after an
/// earlier backtrack to L stays live when a deeper duplicate over the same
/// classes is popped.
fn disequality_after_backtrack_survives_popped_duplicate<E: EgraphTrait<Op = Op, TermId = u32>>(
    mk: impl Fn() -> E,
) {
    for l in 0..3usize {
        let mut h = Harness::new(mk());
        let a = h.c("a");
        let b = h.c("b");
        let a2 = h.c("a2");
        let b2 = h.c("b2");
        assert!(h.eq(a, a2).is_none());
        assert!(h.eq(b, b2).is_none());
        for _ in 0..l + 1 {
            h.level_up();
        }
        h.backtrack(l);
        assert!(h.neq(a, b, 1).is_none());
        h.level_up();
        h.level_up();
        assert!(h.neq(a2, b2, 2).is_none());
        h.backtrack(l + 1);
        let c = h
            .eq(a, b)
            .expect("a != b (level L, after a backtrack to L) still holds");
        h.check_conflict(&c, "disequality after backtrack and popped duplicate");
    }
}

/// The minimal script `minimize_divergence` extracted from
/// `differential_basic_against_semper` seed 764. At level 0: c2 = c1,
/// x = f(c3, c1), y = g(x), c0 = y, c0 = c2, c3 != y. Then two levels,
/// c1 != c3 at level 2 (popped by the backtrack to 1), and y = c3 at level 1,
/// which contradicts the level-0 c3 != y. The semper backend reports the
/// conflict. The basic backend did not: the redundant backtrack at level 0
/// bumps its stamp counter, so the level-0 disequality carries a stamp above
/// the level's base stamp, and its duplicate-insert rule took that for a
/// popped entry and let the level-2 disequality over the same classes
/// replace it. `disequality_survives_popped_duplicate` misses the bug
/// because it has no backtrack before the first disequality.
fn seed_764_minimal<E: EgraphTrait<Op = Op, TermId = u32>>(e: E) {
    let mut h = Harness::new(e);
    let c0 = h.c("c0");
    let c1 = h.c("c1");
    let c2 = h.c("c2");
    let c3 = h.c("c3");
    assert!(h.eq(c2, c1).is_none());
    let x = h.app("f", &[c3, c1]);
    let y = h.app("g", &[x]);
    h.backtrack(0);
    assert!(h.eq(c0, y).is_none());
    assert!(h.eq(c0, c2).is_none());
    assert!(h.neq(c3, y, 1035).is_none());
    h.level_up();
    h.level_up();
    assert!(h.neq(c1, c3, 1331).is_none());
    h.backtrack(1);
    let c = h.eq(y, c3).expect("y = c3 contradicts the level-0 c3 != y");
    h.check_conflict(&c, "seed 764 minimal");
}

// --- 6. Arithmetic interface --------------------------------------------------

/// Union-find over drained pairs: are `x` and `y` connected?
fn connected(pairs: &[(u32, u32)], x: u32, y: u32) -> bool {
    let mut p: FxHashMap<u32, u32> = FxHashMap::default();
    fn root(p: &mut FxHashMap<u32, u32>, mut x: u32) -> u32 {
        while let Some(&q) = p.get(&x) {
            if q == x {
                break;
            }
            x = q;
        }
        x
    }
    for &(a, b) in pairs {
        let (ra, rb) = (root(&mut p, a), root(&mut p, b));
        if ra != rb {
            p.insert(ra, rb);
        }
    }
    root(&mut p, x) == root(&mut p, y)
}

/// Two arithmetic terms that are equal must reach the arithmetic solver as
/// an equality, also when the backend stores them as one node (no merge).
fn drain_reports_equal_arithmetic_terms<E: EgraphTrait<Op = Op, TermId = u32>>(e: E) {
    let mut h = Harness::new(e);
    h.e.incremental_arithmetic(true);
    let a = h.c("a");
    let b = h.c("b");
    let fa = h.app("len", &[a]);
    h.e.mark_arithmetic(fa);
    assert!(h.eq(a, b).is_none());
    let fb = h.app("len", &[b]);
    h.e.mark_arithmetic(fb);
    let drained = h.e.drain_arithmetic_equalities();
    assert!(
        connected(&drained, fa, fb),
        "len(a) = len(b) never reached the arithmetic solver: {drained:?}"
    );
}

/// The arithmetic solver drops equalities reported at a popped level. An
/// equality that still holds after the backtrack must be reported again.
/// (Sundance: reporting once per run lost `A = C`, and the solver accepted a
/// model Z3 finds contradictory.)
fn drain_rereports_after_backtrack<E: EgraphTrait<Op = Op, TermId = u32>>(e: E) {
    let mut h = Harness::new(e);
    h.e.incremental_arithmetic(true);
    let a = h.c("a");
    let b = h.c("b");
    let fa = h.app("len", &[a]);
    h.e.mark_arithmetic(fa);
    assert!(h.eq(a, b).is_none());
    let _ = h.e.drain_arithmetic_equalities();
    h.level_up();
    let fb = h.app("len", &[b]);
    h.e.mark_arithmetic(fb);
    let first = h.e.drain_arithmetic_equalities();
    assert!(
        connected(&first, fa, fb),
        "not reported at level 1: {first:?}"
    );
    h.backtrack(0);
    assert!(
        h.e.are_equal(fa, fb),
        "len(a) = len(b) still holds at level 0"
    );
    let again = h.e.drain_arithmetic_equalities();
    assert!(
        connected(&again, fa, fb),
        "an equality the arithmetic solver dropped on backtrack was not reported again: {again:?}"
    );
}

// --- 7. E-matching -------------------------------------------------------------

fn var(ctx: &mut Context, name: &str, id: usize) -> Local {
    Local {
        id,
        symbol: ctx.allocate_symbol(name),
        sort: ctx.int_sort(),
    }
}

/// Classes of the bindings of a match set, order-free.
fn match_classes<E: EgraphTrait<Op = Op, TermId = u32>>(
    e: &E,
    ms: &[crate::utils::DeterministicHashMap<Local, u32>],
) -> FxHashSet<Vec<(usize, u32)>> {
    ms.iter()
        .map(|m| {
            let mut v: Vec<(usize, u32)> = m.iter().map(|(l, &t)| (l.id, e.find(t))).collect();
            v.sort_unstable();
            v
        })
        .collect()
}

/// `trigger_root_candidates`: the union of the rooted calls is the unrooted
/// result. Rooting changes enumeration and cost, never the match set.
fn rooted_union_equals_unrooted<E: EgraphTrait<Op = Op, TermId = u32>>(e: E) {
    let mut ctx = Context::default();
    let x = var(&mut ctx, "x", 1);
    let mut h = Harness::new(e);
    let cs: Vec<u32> = (0..4).map(|i| h.c(&format!("c{i}"))).collect();
    for &c in &cs {
        h.app("f", &[c]);
    }
    assert!(h.eq(cs[0], cs[1]).is_none());
    let p =
        h.e.compile_pattern(Pattern::App(Op::App("f".into()), vec![Pattern::Var(x)]));
    let unrooted = h.e.match_triggers(vec![(p, None)]);
    if let Some(roots) = h.e.trigger_root_candidates(p) {
        let mut all = Vec::new();
        for r in roots {
            all.extend(h.e.match_triggers(vec![(p, Some(r))]));
        }
        assert_eq!(match_classes(&h.e, &all), match_classes(&h.e, &unrooted));
    }
    assert_eq!(
        match_classes(&h.e, &unrooted).len(),
        3,
        "f(c0)=f(c1), f(c2), f(c3)"
    );
}

/// The instantiation dedup keys on the substituted term, so the term bound to
/// a class must not change when merges elsewhere change roots. (Sundance:
/// binding the root's term re-instantiated the same match every round and
/// diverged.)
fn bindings_stable_across_root_changes<E: EgraphTrait<Op = Op, TermId = u32>>(e: E) {
    let mut ctx = Context::default();
    let x = var(&mut ctx, "x", 1);
    let mut h = Harness::new(e);
    let cs: Vec<u32> = (0..6).map(|i| h.c(&format!("c{i}"))).collect();
    for &c in &cs {
        h.app("f", &[c]);
    }
    let p = h.e.compile_pattern(Pattern::App(
        Op::App("f".into()),
        vec![Pattern::Var(x.clone())],
    ));
    assert!(h.eq(cs[0], cs[1]).is_none());
    let bound_in_c01 = |h: &mut Harness<E>| -> FxHashSet<u32> {
        let ms = h.e.match_triggers(vec![(p, None)]);
        ms.iter()
            .map(|m| m[&x])
            .filter(|&t| h.e.are_equal(t, cs[0]))
            .collect()
    };
    let first = bound_in_c01(&mut h);
    // Merges that change roots of other classes.
    assert!(h.eq(cs[2], cs[3]).is_none());
    assert!(h.eq(cs[4], cs[5]).is_none());
    assert!(h.eq(cs[3], cs[5]).is_none());
    let second = bound_in_c01(&mut h);
    assert_eq!(first, second, "the binding of an untouched class changed");
}

/// A round with relevancy inactive (the complete-model round) produces
/// every match, and every term counts as relevant.
fn inactive_relevancy_filters_nothing<E: EgraphTrait<Op = Op, TermId = u32>>(e: E) {
    let mut ctx = Context::default();
    let x = var(&mut ctx, "x", 1);
    let mut h = Harness::new(e);
    let cs: Vec<u32> = (0..3).map(|i| h.c(&format!("c{i}"))).collect();
    let fs: Vec<u32> = cs.iter().map(|&c| h.app("f", &[c])).collect();
    let p =
        h.e.compile_pattern(Pattern::App(Op::App("f".into()), vec![Pattern::Var(x)]));
    h.e.set_relevancy_active(false);
    assert_eq!(h.e.match_triggers(vec![(p, None)]).len(), 3);
    for &t in fs.iter().chain(cs.iter()) {
        assert!(
            h.e.is_term_relevant(t),
            "relevancy inactive: {t} must be relevant"
        );
    }
}

// --- Recording and replay -----------------------------------------------------
//
// A script of trait calls is recorded on one backend with the observable
// result of each call, then replayed on another backend through an id map.
// The replay reports every call whose observable differs: a registration that
// joins a different class, a conflict present on one side only, a pair equal
// on one side only, an explanation the oracle rejects, or match sets that
// differ modulo classes. This is how two implementations are diffed without
// guessing which behaviour the client relies on.

#[derive(Clone, Debug)]
enum Call {
    Term(Op, Vec<u32>),
    /// A literal value; not produced by `calls_of`, which avoids the known
    /// literal-distinctness divergence (`distinct_literals_conflict`).
    #[allow(dead_code)]
    Literal(String),
    Eq(u32, u32),
    Neq(u32, u32, i32),
    Level,
    Backtrack(usize),
}

#[derive(Clone, Debug, PartialEq)]
enum Seen {
    Id(u32),
    Conflict(bool),
    Unit,
}

/// A random script over uninterpreted terms: registrations, merges,
/// disequalities, levels, backtracks. Ids in the script are the recording
/// backend's ids; `remap` translates them for the replay.
fn random_script(seed: u64, steps: usize) -> Vec<(u8, usize, usize, usize)> {
    let mut s = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    let mut next = |m: usize| {
        s = s
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((s >> 33) as usize) % m
    };
    (0..steps)
        .map(|_| (next(10) as u8, next(1 << 16), next(1 << 16), next(1 << 16)))
        .collect()
}

/// Build the concrete call list from a random script, by index into the
/// terms registered so far, so the same script means the same calls on
/// every backend.
fn calls_of(script: &[(u8, usize, usize, usize)]) -> Vec<Call> {
    let mut calls = Vec::new();
    let mut n_terms = 0usize;
    let mut level = 0usize;
    // Terms are named by registration order; the replay maps order to ids.
    for i in 0..4 {
        calls.push(Call::Term(Op::App(format!("c{i}")), vec![]));
        n_terms += 1;
    }
    for &(k, a, b, c) in script {
        match k {
            0..=2 => {
                let f = ["f", "g"][a % 2];
                let ch = if b % 2 == 0 {
                    vec![(c % n_terms) as u32]
                } else {
                    vec![(c % n_terms) as u32, (b % n_terms) as u32]
                };
                calls.push(Call::Term(Op::App(f.to_string()), ch));
                n_terms += 1;
            }
            3..=5 => calls.push(Call::Eq((a % n_terms) as u32, (b % n_terms) as u32)),
            6 => calls.push(Call::Neq(
                (a % n_terms) as u32,
                (b % n_terms) as u32,
                1000 + c as i32 % 1000,
            )),
            7 | 8 => {
                calls.push(Call::Level);
                level += 1;
            }
            _ => {
                let to = a % (level + 1);
                calls.push(Call::Backtrack(to));
                level = to;
            }
        }
    }
    calls
}

/// Record a script on two backends and report the first divergence, if
/// any: per call, the conflict outcome, and the equality relation over all
/// terms registered so far.
fn diff_backends<A, B>(mk_a: impl Fn() -> A, mk_b: impl Fn() -> B, calls: &[Call]) -> Option<String>
where
    A: EgraphTrait<Op = Op, TermId = u32>,
    B: EgraphTrait<Op = Op, TermId = u32>,
{
    // Registration order -> id is learned by a first pass per backend: ids
    // are assigned at registration, so bind lazily while recording.
    #[allow(clippy::type_complexity)]
    fn run<E: EgraphTrait<Op = Op, TermId = u32>>(
        e: E,
        calls: &[Call],
    ) -> (Vec<Seen>, Vec<Vec<bool>>) {
        let mut order: Vec<u32> = Vec::new();
        let mut h = Harness::new(e);
        let mut seen = Vec::new();
        let mut rel = Vec::new();
        // The driver's protocol: after a conflict it backtracks one level (a
        // level-0 conflict ends the run), and it never backtracks upward.
        let mut level = 0usize;
        let mut stop = false;
        for c in calls {
            if stop {
                break;
            }
            let c = match c {
                Call::Term(op, ch) => {
                    Call::Term(op.clone(), ch.iter().map(|i| order[*i as usize]).collect())
                }
                Call::Eq(a, b) => Call::Eq(order[*a as usize], order[*b as usize]),
                Call::Neq(a, b, l) => Call::Neq(order[*a as usize], order[*b as usize], *l),
                other => other.clone(),
            };
            let r = match &c {
                Call::Term(op, ch) => {
                    let id = h.term(op.clone(), ch);
                    order.push(id);
                    Seen::Id(order.len() as u32 - 1)
                }
                Call::Literal(v) => {
                    let id = h.lit(v);
                    order.push(id);
                    Seen::Id(order.len() as u32 - 1)
                }
                Call::Eq(..) | Call::Neq(..) => {
                    let k = match &c {
                        Call::Eq(a, b) => h.eq(*a, *b),
                        Call::Neq(a, b, l) => h.neq(*a, *b, *l),
                        _ => unreachable!(),
                    };
                    if let Some(k) = &k {
                        h.check_conflict(k, "replay");
                        if level == 0 {
                            stop = true;
                        } else {
                            level -= 1;
                            h.backtrack(level);
                        }
                    }
                    Seen::Conflict(k.is_some())
                }
                Call::Level => {
                    h.level_up();
                    level += 1;
                    Seen::Unit
                }
                Call::Backtrack(l) => {
                    level = (*l).min(level);
                    h.backtrack(level);
                    Seen::Unit
                }
            };
            // The state right after a conflict is unspecified (a backend may or
            // may not have performed the conflicting merge); the client only
            // reads it after backtracking, so it is not compared.
            let conflicted = matches!(r, Seen::Conflict(true));
            seen.push(r);
            rel.push(if conflicted && stop {
                Vec::new()
            } else {
                order
                    .iter()
                    .flat_map(|&x| order.iter().map(move |&y| (x, y)))
                    .map(|(x, y)| h.e.are_equal(x, y))
                    .collect()
            });
        }
        (seen, rel)
    }
    let (sa, ra) = run(mk_a(), calls);
    let (sb, rb) = run(mk_b(), calls);
    for i in 0..sa.len().min(sb.len()) {
        if sa[i] != sb[i] {
            return Some(format!(
                "call {i} {:?}: {:?} against {:?}",
                calls[i], sa[i], sb[i]
            ));
        }
        if ra[i] != rb[i] {
            let n = (ra[i].len() as f64).sqrt() as usize;
            let k = (0..ra[i].len())
                .find(|&k| ra[i][k] != rb[i][k])
                .expect("differ");
            let script: Vec<String> = calls[..=i]
                .iter()
                .enumerate()
                .map(|(j, c)| format!("{j}: {c:?}"))
                .collect();
            return Some(format!(
                "call {i} {:?}: terms #{} and #{} (registration order) are equal in A: {}, in B: {}\nscript:\n{}",
                calls[i],
                k / n,
                k % n,
                ra[i][k],
                rb[i][k],
                script.join("\n")
            ));
        }
    }
    None
}

/// The replay harness is deterministic: a backend replayed against itself
/// never diverges. This keeps the harness exercised in builds without a
/// second backend; a second implementation is diffed against the sundance
/// e-graph by instantiating `diff_backends` with it.
#[test]
fn replay_is_deterministic_on_one_backend() {
    for seed in 0..seeds(20) {
        let calls = calls_of(&random_script(seed, 120));
        assert_eq!(
            diff_backends(
                crate::egraphs::Egraph::new,
                crate::egraphs::Egraph::new,
                &calls
            ),
            None,
            "seed {seed}"
        );
    }
}

// --- Oracle self-tests ---------------------------------------------------------

/// The oracle must reject the path-only explanation of the canonical-children
/// scenario, or the tests above prove nothing.
#[test]
fn oracle_rejects_missing_child_equality() {
    let mut h = Harness::new(crate::egraphs::Egraph::new());
    let n = h.c("n");
    let k = h.c("k");
    let r = h.c("r");
    let x = h.c("x");
    let y = h.c("y");
    let route = h.app("route", &[n, k]);
    let lt_r = h.app("lt", &[r, x]);
    let lt_route = h.app("lt", &[route, y]);
    assert!(!h.entails(&[(x, y)], lt_r, lt_route));
    assert!(h.entails(&[(x, y), (r, route)], lt_r, lt_route));
}

// --- Instantiation ---------------------------------------------------------------

// One test per line, per backend. A known divergence is `#[ignore]`d with
// the reason, so it stays visible (`cargo test -- --ignored`) without
// failing the suite; removing the attribute is the acceptance test of a fix.
macro_rules! t {
    ($name:ident, $mk:expr) => {
        #[test]
        fn $name() {
            super::$name($mk)
        }
    };
    ($name:ident, $mk:expr, ignore = $why:literal) => {
        #[test]
        #[ignore = $why]
        fn $name() {
            super::$name($mk)
        }
    };
}

mod basic {
    use crate::egraphs::Egraph;
    t!(ids_survive_backtrack, Egraph::new());
    t!(congruent_registration_merges_now, Egraph::new());
    t!(
        eq_is_commutative,
        Egraph::new(),
        ignore = "basic keeps (= a b) and (= b a) apart: a completeness gap, not a soundness one"
    );
    t!(distinct_literals_conflict, Egraph::new());
    t!(true_false_collision, Egraph::new());
    t!(disequal_on_equal_conflicts_now, Egraph::new());
    t!(congruence_conflict_is_valid, Egraph::new());
    t!(explanation_complete_canonical_children, Egraph::new());
    t!(explanation_complete_hashcons_onto_creator, Egraph::new());
    t!(explain_equality_complete_any_pair, Egraph::new());
    t!(level0_disequality_survives_backtracks, Egraph::new());
    t!(disequality_survives_popped_duplicate, Egraph::new());
    t!(seed_764_minimal, Egraph::new());
    t!(
        disequality_survives_popped_reversed_duplicate,
        Egraph::new()
    );
    t!(level0_disequality_survives_backtracks_plain, Egraph::new());
    t!(drain_reports_equal_arithmetic_terms, Egraph::new());
    t!(drain_rereports_after_backtrack, Egraph::new());
    t!(rooted_union_equals_unrooted, Egraph::new());
    t!(bindings_stable_across_root_changes, Egraph::new());
    t!(inactive_relevancy_filters_nothing, Egraph::new());
    #[test]
    fn disequality_after_backtrack_survives_popped_duplicate() {
        super::disequality_after_backtrack_survives_popped_duplicate(Egraph::new)
    }
    #[test]
    fn random_conflicts_are_valid() {
        super::random_conflicts_are_valid(Egraph::new)
    }
    #[test]
    fn backtrack_restores_classes() {
        super::backtrack_restores_classes(Egraph::new)
    }
}

// --- The semper e-graph against the sundance e-graph --------------------------

#[cfg(feature = "semper-egraph")]
#[test]
fn differential_basic_against_semper() {
    let only: Option<u64> = std::env::var("CONFORMANCE_SEED")
        .ok()
        .and_then(|v| v.parse().ok());
    for seed in 1..=seeds(60) {
        if only.is_some_and(|o| o != seed) {
            continue;
        }
        let calls = calls_of(&random_script(seed, 50));
        if let Some(d) = diff_backends(
            crate::egraphs::Egraph::new,
            crate::egraphs::semper::SemperEgraph::new,
            &calls,
        ) {
            panic!("seed {seed}: basic and semper diverge at {d}");
        }
    }
}

#[cfg(feature = "semper-egraph")]
fn minimize(mut calls: Vec<Call>) -> Vec<Call> {
    let diverges = |c: &[Call]| {
        diff_backends(
            crate::egraphs::Egraph::new,
            crate::egraphs::semper::SemperEgraph::new,
            c,
        )
        .is_some()
    };
    assert!(diverges(&calls));
    loop {
        let mut shrunk = false;
        for i in (0..calls.len()).rev() {
            // Index of the registration removed, if call i is one.
            let reg_index = calls[..i]
                .iter()
                .filter(|c| matches!(c, Call::Term(..)))
                .count() as u32;
            let is_term = matches!(calls[i], Call::Term(..));
            if is_term {
                let referenced = calls[i + 1..].iter().any(|c| match c {
                    Call::Term(_, ch) => ch.contains(&reg_index),
                    Call::Eq(a, b) | Call::Neq(a, b, _) => *a == reg_index || *b == reg_index,
                    _ => false,
                });
                if referenced {
                    continue;
                }
            }
            let mut cand: Vec<Call> = calls.clone();
            cand.remove(i);
            if is_term {
                let shift = |x: &mut u32| {
                    if *x > reg_index {
                        *x -= 1;
                    }
                };
                for c in cand.iter_mut() {
                    match c {
                        Call::Term(_, ch) => ch.iter_mut().for_each(shift),
                        Call::Eq(a, b) | Call::Neq(a, b, _) => {
                            shift(a);
                            shift(b);
                        }
                        _ => {}
                    }
                }
            }
            if diverges(&cand) {
                calls = cand;
                shrunk = true;
            }
        }
        if !shrunk {
            return calls;
        }
    }
}

#[cfg(feature = "semper-egraph")]
#[test]
#[ignore = "diagnostic: shrinks a diverging seed of differential_basic_against_semper"]
fn minimize_divergence() {
    let seed: u64 = std::env::var("CONFORMANCE_SEED")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(764);
    let calls = calls_of(&random_script(seed, 50));
    let min = minimize(calls);
    let d = diff_backends(
        crate::egraphs::Egraph::new,
        crate::egraphs::semper::SemperEgraph::new,
        &min,
    )
    .expect("still diverges");
    eprintln!("minimal divergence ({} calls): {d}", min.len());
    for (i, c) in min.iter().enumerate() {
        eprintln!("{i}: {c:?}");
    }
}

#[cfg(feature = "semper-egraph")]
mod semper {
    use crate::egraphs::semper::SemperEgraph;
    t!(ids_survive_backtrack, SemperEgraph::new());
    t!(congruent_registration_merges_now, SemperEgraph::new());
    t!(eq_is_commutative, SemperEgraph::new());
    t!(
        distinct_literals_conflict,
        SemperEgraph::new(),
        ignore = "the semper adapter merges two different literal values without a conflict"
    );
    t!(true_false_collision, SemperEgraph::new());
    t!(disequal_on_equal_conflicts_now, SemperEgraph::new());
    t!(congruence_conflict_is_valid, SemperEgraph::new());
    t!(explanation_complete_canonical_children, SemperEgraph::new());
    t!(
        explanation_complete_hashcons_onto_creator,
        SemperEgraph::new()
    );
    t!(explain_equality_complete_any_pair, SemperEgraph::new());
    t!(level0_disequality_survives_backtracks, SemperEgraph::new());
    t!(disequality_survives_popped_duplicate, SemperEgraph::new());
    t!(seed_764_minimal, SemperEgraph::new());
    t!(
        disequality_survives_popped_reversed_duplicate,
        SemperEgraph::new()
    );
    t!(
        level0_disequality_survives_backtracks_plain,
        SemperEgraph::new()
    );
    t!(drain_reports_equal_arithmetic_terms, SemperEgraph::new());
    t!(drain_rereports_after_backtrack, SemperEgraph::new());
    t!(rooted_union_equals_unrooted, SemperEgraph::new());
    t!(bindings_stable_across_root_changes, SemperEgraph::new());
    t!(inactive_relevancy_filters_nothing, SemperEgraph::new());
    #[test]
    fn disequality_after_backtrack_survives_popped_duplicate() {
        super::disequality_after_backtrack_survives_popped_duplicate(SemperEgraph::new)
    }
    #[test]
    fn random_conflicts_are_valid() {
        super::random_conflicts_are_valid(SemperEgraph::new)
    }
    #[test]
    fn backtrack_restores_classes() {
        super::backtrack_restores_classes(SemperEgraph::new)
    }
}
