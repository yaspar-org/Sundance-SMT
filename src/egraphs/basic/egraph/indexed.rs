// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Indexed e-matching ([`EMatching::Indexed`](crate::egraphs::EMatching::Indexed)).
//!
//! [`Egraph::match_triggers_indexed`] returns the same substitutions, in the same order, as the
//! top-down matcher (`Egraph::match_patterns`). It runs the same depth-first enumeration over the
//! same candidates, visited in `function_maps` order, but finds them through indexes instead of
//! scans:
//!
//! - An application nested in a pattern can only match an application in the class of the
//!   subterm it is matched against. Its candidates come from a per-symbol index of applications
//!   by class root, where the top-down matcher scans every application of the symbol.
//! - A top-level application with a ground child, or with a nested application of a symbol that
//!   has fewer applications, is entered through a per-(symbol, child position) index of
//!   applications by the class of that child.
//! - The partial substitution is one binding stack and the patterns are borrowed, so nothing is
//!   cloned per candidate.
//!
//! The candidates an index skips are exactly ones that cannot match: a match only depends on the
//! classes of a candidate's children. For the same reason the de-duplication of candidates with
//! equal canonical children keeps the same (first) candidate as the top-down matcher.
//!
//! The indexes describe the current terms and classes. They are built lazily on first use and
//! dropped after the next write of a term, a proof-forest edge, or a compiled pattern (see
//! [`MatchIndex::invalidate`]), so within one instantiation round, where the egraph does not
//! change, every `match_triggers` call shares them.

use super::Egraph;
use crate::egraphs::basic::repr::{Op, Pattern, PatternId};
use crate::utils::{DeterministicHashMap, FastDeterministicHashMap, FastDeterministicHashSet};
use std::rc::Rc;
use yaspar_ir::ast::Local;

/// Positions in `function_maps[symbol]`, grouped by a class root. Positions are ascending.
type PositionsByRoot = FastDeterministicHashMap<u32, Vec<u32>>;

/// The lookup tables of the indexed matcher. Every table is filled lazily.
#[derive(Default)]
pub(super) struct MatchIndex {
    /// False once the egraph may have changed since the tables were filled.
    fresh: bool,
    /// Symbol -> class root of an application -> its position.
    by_class: FastDeterministicHashMap<String, Rc<PositionsByRoot>>,
    /// Symbol -> child position k -> class root of the k-th child -> position of the application.
    by_child: FastDeterministicHashMap<String, Vec<Option<Rc<PositionsByRoot>>>>,
    /// Address of an application node of a compiled pattern -> class roots of the applications
    /// it can match (`None`: not worth restricting, see [`Egraph::pattern_roots`]).
    roots: FastDeterministicHashMap<usize, Option<Rc<Vec<u32>>>>,
}

impl MatchIndex {
    /// Marks the tables stale. Called wherever the egraph writes a term or a proof-forest edge,
    /// which covers every change of `function_maps` or of `find`, and when a pattern is compiled
    /// (the `roots` keys are addresses inside `compiled_patterns`).
    pub(super) fn invalidate(&mut self) {
        self.fresh = false;
    }

    /// Drops stale tables.
    fn refresh(&mut self) {
        if !self.fresh {
            self.by_class.clear();
            self.by_child.clear();
            self.roots.clear();
            self.fresh = true;
        }
    }
}

/// One pending obligation of the depth-first matcher.
#[derive(Clone, Copy)]
enum Goal<'p> {
    /// A pattern of the multipattern, optionally restricted to the class of a hint term.
    Top(&'p Pattern, Option<u32>),
    /// A sub-pattern that must match the given subterm modulo equality.
    Sub(&'p Pattern, u32),
}

type Substitution = DeterministicHashMap<Local, u32>;

impl Egraph {
    /// [`EMatching::Indexed`](crate::egraphs::EMatching::Indexed) implementation of
    /// `match_triggers`: same result, in the same order, as `match_patterns`.
    pub(super) fn match_triggers_indexed(
        &mut self,
        trigger_term_pairs: &[(PatternId, Option<u32>)],
    ) -> Vec<Substitution> {
        self.match_index.get_mut().refresh();
        let this: &Egraph = self;
        // The goal stack is popped from the end, so the first pattern goes last.
        let mut goals: Vec<Goal<'_>> = trigger_term_pairs
            .iter()
            .rev()
            .map(|&(pattern_id, hint)| Goal::Top(&this.compiled_patterns[pattern_id], hint))
            .collect();
        let mut bindings = Vec::new();
        let mut matches = Vec::new();
        this.match_goals(&mut goals, &mut bindings, &mut matches);
        matches
    }

    /// Solves the goals on the stack depth-first and records one substitution per solution.
    /// Leaves `goals` and `bindings` as it found them.
    fn match_goals<'p>(
        &'p self,
        goals: &mut Vec<Goal<'p>>,
        bindings: &mut Vec<(Local, u32)>,
        matches: &mut Vec<Substitution>,
    ) {
        let Some(goal) = goals.pop() else {
            matches.push(bindings.iter().cloned().collect());
            return;
        };
        let (pattern, term) = match goal {
            Goal::Top(pattern, hint) => (pattern, hint),
            Goal::Sub(pattern, subterm) => (pattern, Some(subterm)),
        };
        match pattern {
            Pattern::Var(name) => {
                let term = term.expect("Pattern::Var requires a ground term to bind");
                let bound = bindings
                    .iter()
                    .find(|(var, _)| var == name)
                    .map(|&(_, value)| value);
                match bound {
                    None => {
                        bindings.push((name.clone(), term));
                        self.match_goals(goals, bindings, matches);
                        bindings.pop();
                    }
                    Some(value) if self.find(value) == self.find(term) => {
                        self.match_goals(goals, bindings, matches);
                    }
                    Some(_) => {}
                }
            }
            Pattern::Ground(ground) => {
                if term.is_none_or(|t| self.find(*ground) == self.find(t)) {
                    self.match_goals(goals, bindings, matches);
                }
            }
            Pattern::App(op, sub_patterns) => {
                self.match_application(op, sub_patterns, term, goals, bindings, matches);
            }
        }
        goals.push(goal);
    }

    /// Tries every application of `op` that can match `op(sub_patterns)`: those in the class of
    /// `term` when there is one, otherwise the top-level candidates.
    fn match_application<'p>(
        &'p self,
        op: &Op,
        sub_patterns: &'p [Pattern],
        term: Option<u32>,
        goals: &mut Vec<Goal<'p>>,
        bindings: &mut Vec<(Local, u32)>,
        matches: &mut Vec<Substitution>,
    ) {
        let key = op.function_map_key();
        let Some(applications) = self.function_maps.get(key) else {
            return;
        };
        let mut considered = FastDeterministicHashSet::default();
        let mut try_position = |position: u32,
                                goals: &mut Vec<Goal<'p>>,
                                bindings: &mut Vec<(Local, u32)>,
                                matches: &mut Vec<Substitution>| {
            let children = &applications[position as usize].1;
            self.match_candidate(
                sub_patterns,
                children,
                &mut considered,
                goals,
                bindings,
                matches,
            );
        };
        match term {
            Some(term) => {
                let by_class = self.applications_by_class(key);
                for &position in by_class.get(&self.find(term)).into_iter().flatten() {
                    try_position(position, goals, bindings, matches);
                }
            }
            None => match self.top_level_candidates(key, sub_patterns) {
                Some(positions) => {
                    for position in positions {
                        try_position(position, goals, bindings, matches);
                    }
                }
                None => {
                    for position in 0..applications.len() as u32 {
                        try_position(position, goals, bindings, matches);
                    }
                }
            },
        }
    }

    /// Matches the children of one candidate application against `sub_patterns`, then the
    /// remaining goals.
    fn match_candidate<'p>(
        &'p self,
        sub_patterns: &'p [Pattern],
        children: &[u32],
        considered: &mut FastDeterministicHashSet<Vec<u32>>,
        goals: &mut Vec<Goal<'p>>,
        bindings: &mut Vec<(Local, u32)>,
        matches: &mut Vec<Substitution>,
    ) {
        if children.len() != sub_patterns.len() {
            return;
        }
        // Candidates with the same canonical children give the same matches; like the top-down
        // matcher, keep the first one.
        if !considered.insert(children.iter().map(|&child| self.find(child)).collect()) {
            return;
        }
        let depth = goals.len();
        goals.extend(
            sub_patterns
                .iter()
                .zip(children)
                .rev()
                .map(|(sub_pattern, &child)| Goal::Sub(sub_pattern, child)),
        );
        self.match_goals(goals, bindings, matches);
        goals.truncate(depth);
    }

    /// Positions, ascending, of the only applications of `key` that can match `key(sub_patterns)`
    /// with no class constraint, judged from the single most selective child: a ground child, or a
    /// nested application with [`Egraph::pattern_roots`]. `None` when no child leaves fewer than
    /// all applications of `key`.
    fn top_level_candidates(&self, key: &str, sub_patterns: &[Pattern]) -> Option<Vec<u32>> {
        let total = self.function_maps.get(key).map_or(0, Vec::len);
        let mut best: Option<Vec<u32>> = None;
        for (k, sub_pattern) in sub_patterns.iter().enumerate() {
            let candidates: Vec<u32> = match sub_pattern {
                Pattern::Var(_) => continue,
                Pattern::Ground(ground) => self
                    .applications_by_child(key, k)
                    .get(&self.find(*ground))
                    .cloned()
                    .unwrap_or_default(),
                Pattern::App(op, nested) => {
                    let Some(roots) = self.pattern_roots(sub_pattern, op, nested, total) else {
                        continue;
                    };
                    let by_child = self.applications_by_child(key, k);
                    // Each application has one root for child k, so the positions are distinct.
                    let mut positions: Vec<u32> = roots
                        .iter()
                        .filter_map(|root| by_child.get(root))
                        .flatten()
                        .copied()
                        .collect();
                    positions.sort_unstable();
                    positions
                }
            };
            if best.as_ref().is_none_or(|b| candidates.len() < b.len()) {
                let none_left = candidates.is_empty();
                best = Some(candidates);
                if none_left {
                    break;
                }
            }
        }
        best.filter(|b| b.len() < total)
    }

    /// Class roots of the applications that the application pattern `op(nested)` (the node
    /// `pattern`, a child of a pattern for a symbol with `parent_total` applications) can match:
    /// the roots of its [`Egraph::top_level_candidates`], or of all applications of `op` with the
    /// right arity when `op` has fewer applications than the parent symbol. `None` otherwise.
    /// Cached per pattern node for as long as the index is fresh.
    fn pattern_roots(
        &self,
        pattern: &Pattern,
        op: &Op,
        nested: &[Pattern],
        parent_total: usize,
    ) -> Option<Rc<Vec<u32>>> {
        let address = std::ptr::from_ref(pattern).addr();
        if let Some(roots) = self.match_index.borrow().roots.get(&address) {
            return roots.clone();
        }
        let key = op.function_map_key();
        let applications = self.function_maps.get(key).map_or(&[][..], Vec::as_slice);
        let roots = match self.top_level_candidates(key, nested) {
            Some(positions) => Some(
                positions
                    .iter()
                    .map(|&position| self.find(applications[position as usize].0))
                    .collect::<Vec<u32>>(),
            ),
            None if applications.len() < parent_total => Some(
                applications
                    .iter()
                    .filter(|(_, children)| children.len() == nested.len())
                    .map(|&(application, _)| self.find(application))
                    .collect(),
            ),
            None => None,
        };
        let roots = roots.map(|mut roots| {
            roots.sort_unstable();
            roots.dedup();
            Rc::new(roots)
        });
        self.match_index
            .borrow_mut()
            .roots
            .insert(address, roots.clone());
        roots
    }

    /// The applications of `key` grouped by their class root.
    fn applications_by_class(&self, key: &str) -> Rc<PositionsByRoot> {
        if let Some(by_class) = self.match_index.borrow().by_class.get(key) {
            return Rc::clone(by_class);
        }
        let mut by_class = PositionsByRoot::default();
        for (position, (application, _)) in self
            .function_maps
            .get(key)
            .into_iter()
            .flatten()
            .enumerate()
        {
            by_class
                .entry(self.find(*application))
                .or_default()
                .push(position as u32);
        }
        let by_class = Rc::new(by_class);
        self.match_index
            .borrow_mut()
            .by_class
            .insert(key.to_string(), Rc::clone(&by_class));
        by_class
    }

    /// The applications of `key` that have a k-th child, grouped by the class root of that child.
    fn applications_by_child(&self, key: &str, k: usize) -> Rc<PositionsByRoot> {
        if let Some(Some(by_child)) = self
            .match_index
            .borrow()
            .by_child
            .get(key)
            .and_then(|slots| slots.get(k))
        {
            return Rc::clone(by_child);
        }
        let mut by_child = PositionsByRoot::default();
        for (position, (_, children)) in self
            .function_maps
            .get(key)
            .into_iter()
            .flatten()
            .enumerate()
        {
            if let Some(&child) = children.get(k) {
                by_child
                    .entry(self.find(child))
                    .or_default()
                    .push(position as u32);
            }
        }
        let by_child = Rc::new(by_child);
        let mut index = self.match_index.borrow_mut();
        let slots = index.by_child.entry(key.to_string()).or_default();
        if slots.len() <= k {
            slots.resize(k + 1, None);
        }
        slots[k] = Some(Rc::clone(&by_child));
        by_child
    }
}

#[cfg(test)]
mod tests {
    use crate::egraphs::{EMatching, Egraph, EgraphTrait, Op, Pattern, PatternId};
    use crate::utils::DeterministicHashMap;
    use yaspar_ir::ast::{Context, Local, ObjectAllocatorExt as _, StrAllocator};

    type Substitution = DeterministicHashMap<Local, u32>;

    fn var(ctx: &mut Context, name: &str, id: usize) -> Local {
        let symbol = ctx.allocate_symbol(name);
        let sort = ctx.int_sort();
        Local { id, symbol, sort }
    }

    fn app(egraph: &mut Egraph, f: &str, children: &[u32]) -> u32 {
        egraph.register_term(Op::App(f.to_string()), children, false)
    }

    fn constant(egraph: &mut Egraph, name: &str) -> u32 {
        egraph.register_constant(Op::Constant(name.to_string()))
    }

    fn papp(f: &str, children: Vec<Pattern>) -> Pattern {
        Pattern::App(Op::App(f.to_string()), children)
    }

    fn pvar(local: &Local) -> Pattern {
        Pattern::Var(local.clone())
    }

    /// Runs both matchers on the same egraph and checks they agree, in order.
    fn both(egraph: &mut Egraph, triggers: &[(PatternId, Option<u32>)]) -> Vec<Substitution> {
        egraph.set_ematching(EMatching::TopDown);
        let top_down = egraph.match_triggers(triggers.to_vec());
        egraph.set_ematching(EMatching::Indexed);
        let indexed = egraph.match_triggers(triggers.to_vec());
        assert_eq!(top_down, indexed, "matchers disagree on {triggers:?}");
        top_down
    }

    fn bound(matches: &[Substitution], x: &Local) -> Vec<u32> {
        matches.iter().map(|m| m[x]).collect()
    }

    #[test]
    fn nested_patterns_match_through_classes() {
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x", 0);
        let mut egraph = Egraph::new();
        let a = constant(&mut egraph, "a");
        let b = constant(&mut egraph, "b");
        let ga = app(&mut egraph, "g", &[a]);
        let gb = app(&mut egraph, "g", &[b]);
        let h = app(&mut egraph, "h", &[]);
        app(&mut egraph, "f", &[h]);
        app(&mut egraph, "f", &[ga]);
        let pattern = egraph.compile_pattern(papp("f", vec![papp("g", vec![pvar(&x)])]));

        // f(g(x)) matches f(g(a)) only.
        assert_eq!(bound(&both(&mut egraph, &[(pattern, None)]), &x), vec![a]);

        // h = g(b): now f(h) matches with x = b, through the class of h.
        egraph.notify_new_decision_level();
        assert!(egraph.assert_equal(h, gb).conflict.is_none());
        assert_eq!(
            bound(&both(&mut egraph, &[(pattern, None)]), &x),
            vec![b, a]
        );

        // Undoing the merge must drop the indexes built on it.
        egraph.backtrack_to(0);
        assert_eq!(bound(&both(&mut egraph, &[(pattern, None)]), &x), vec![a]);
    }

    #[test]
    fn ground_children_repeated_variables_and_hints() {
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x", 0);
        let y = var(&mut ctx, "y", 1);
        let mut egraph = Egraph::new();
        let a = constant(&mut egraph, "a");
        let b = constant(&mut egraph, "b");
        let c = constant(&mut egraph, "c");
        let u = app(&mut egraph, "u", &[]);
        let v = app(&mut egraph, "v", &[]);
        app(&mut egraph, "f", &[a, b]);
        let fuv = app(&mut egraph, "f", &[u, v]);
        let fca = app(&mut egraph, "f", &[c, a]);
        app(&mut egraph, "f", &[c, u]);

        // Ground child: f(y, a) with `a` ground matches f(c, a).
        let ground = egraph.compile_pattern(papp("f", vec![pvar(&y), Pattern::Ground(a)]));
        assert_eq!(bound(&both(&mut egraph, &[(ground, None)]), &y), vec![c]);
        // u = a: f(c, u) matches too, but it is a congruent duplicate of f(c, a), so it is skipped.
        egraph.notify_new_decision_level();
        assert!(egraph.assert_equal(u, a).conflict.is_none());
        assert_eq!(bound(&both(&mut egraph, &[(ground, None)]), &y), vec![c]);

        // Repeated variable: f(x, x) needs equal children; v = u makes f(u, v) match.
        let repeated = egraph.compile_pattern(papp("f", vec![pvar(&x), pvar(&x)]));
        assert!(both(&mut egraph, &[(repeated, None)]).is_empty());
        assert!(egraph.assert_equal(v, u).conflict.is_none());
        assert_eq!(bound(&both(&mut egraph, &[(repeated, None)]), &x), vec![u]);

        // A hint restricts the top-level pattern to one class.
        egraph.notify_new_decision_level();
        assert!(egraph.assert_equal(fuv, fca).conflict.is_none());
        let any = egraph.compile_pattern(papp("f", vec![pvar(&x), pvar(&y)]));
        let hinted = both(&mut egraph, &[(any, Some(fca))]);
        assert_eq!(bound(&hinted, &x), vec![u, c]);
    }

    #[test]
    fn multipatterns_and_congruent_duplicates() {
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x", 0);
        let y = var(&mut ctx, "y", 1);
        let mut egraph = Egraph::new();
        let a = constant(&mut egraph, "a");
        let b = constant(&mut egraph, "b");
        let s = app(&mut egraph, "s", &[]);
        for children in [[a], [s], [b]] {
            app(&mut egraph, "g", &children);
        }
        for children in [[a, b], [s, b], [b, a]] {
            app(&mut egraph, "k", &children);
        }

        // [g(x), k(x, y)]: shared variable across the patterns of a multipattern.
        let g = egraph.compile_pattern(papp("g", vec![pvar(&x)]));
        let k = egraph.compile_pattern(papp("k", vec![pvar(&x), pvar(&y)]));
        let both_patterns = both(&mut egraph, &[(g, None), (k, None)]);
        assert_eq!(bound(&both_patterns, &x), vec![a, s, b]);
        assert_eq!(bound(&both_patterns, &y), vec![b, b, a]);

        // s = a makes g(s) and k(s, b) congruent duplicates, which both matchers skip.
        egraph.notify_new_decision_level();
        assert!(egraph.assert_equal(s, a).conflict.is_none());
        let merged = both(&mut egraph, &[(g, None), (k, None)]);
        assert_eq!(bound(&merged, &x), vec![a, b]);
    }

    #[test]
    fn selective_entry_through_a_rarer_nested_symbol() {
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x", 0);
        let y = var(&mut ctx, "y", 1);
        let mut egraph = Egraph::new();
        let leaves: Vec<u32> = (0..6)
            .map(|i| constant(&mut egraph, &format!("c{i}")))
            .collect();
        // Many h-applications, one r-application: h(r(x), y) is entered through r.
        let r = app(&mut egraph, "r", &[leaves[0]]);
        for &l in &leaves {
            app(&mut egraph, "h", &[l, l]);
        }
        app(&mut egraph, "h", &[r, leaves[1]]);
        let pattern = egraph.compile_pattern(papp("h", vec![papp("r", vec![pvar(&x)]), pvar(&y)]));
        let matches = both(&mut egraph, &[(pattern, None)]);
        assert_eq!(bound(&matches, &x), vec![leaves[0]]);
        assert_eq!(bound(&matches, &y), vec![leaves[1]]);
        // r(c0) = c2: h(c2, c2) now matches as well, through the class of c2.
        egraph.notify_new_decision_level();
        assert!(egraph.assert_equal(r, leaves[2]).conflict.is_none());
        assert_eq!(both(&mut egraph, &[(pattern, None)]).len(), 2);
    }

    /// xorshift64*, so the test needs no extra dependency.
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 >> 12;
            self.0 ^= self.0 << 25;
            self.0 ^= self.0 >> 27;
            self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
        }
        fn below(&mut self, n: usize) -> usize {
            (self.next() % n as u64) as usize
        }
    }

    const SYMBOLS: [(&str, usize); 5] = [("f", 1), ("g", 2), ("h", 2), ("k", 3), ("r", 1)];

    fn random_pattern(rng: &mut Rng, vars: &[Local], terms: &[u32], depth: usize) -> Pattern {
        let (name, arity) = SYMBOLS[rng.below(SYMBOLS.len())];
        let children = (0..arity)
            .map(|_| match rng.below(if depth == 0 { 4 } else { 6 }) {
                0..=2 => pvar(&vars[rng.below(vars.len())]),
                3 => Pattern::Ground(terms[rng.below(terms.len())]),
                _ => random_pattern(rng, vars, terms, depth - 1),
            })
            .collect();
        papp(name, children)
    }

    /// Random egraphs (terms, merges, backtracks) and random patterns with nesting, ground terms,
    /// repeated variables, multipatterns and hints: both matchers return the same list.
    #[test]
    fn matchers_agree_on_random_egraphs() {
        let mut ctx = Context::new();
        let vars: Vec<Local> = (0..3).map(|i| var(&mut ctx, &format!("x{i}"), i)).collect();
        let mut total_matches = 0;
        for seed in 1..=300u64 {
            let mut rng = Rng(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1);
            let mut egraph = Egraph::new();
            let mut terms: Vec<u32> = (0..4)
                .map(|i| constant(&mut egraph, &format!("c{i}")))
                .collect();
            terms.extend((0..3).map(|i| app(&mut egraph, &format!("a{i}"), &[])));
            for _ in 0..40 {
                let (name, arity) = SYMBOLS[rng.below(SYMBOLS.len())];
                let children: Vec<u32> =
                    (0..arity).map(|_| terms[rng.below(terms.len())]).collect();
                terms.push(app(&mut egraph, name, &children));
            }
            let patterns: Vec<PatternId> = (0..8)
                .map(|_| {
                    let pattern = random_pattern(&mut rng, &vars, &terms, 2);
                    egraph.compile_pattern(pattern)
                })
                .collect();
            let mut level = 0;
            for _ in 0..12 {
                // Merge two non-constant terms (merging two constants is a conflict).
                let t1 = terms[4 + rng.below(terms.len() - 4)];
                let t2 = terms[4 + rng.below(terms.len() - 4)];
                egraph.notify_new_decision_level();
                level += 1;
                let _ = egraph.assert_equal(t1, t2);
                if rng.below(4) == 0 {
                    level = rng.below(level + 1);
                    egraph.backtrack_to(level);
                }
                for _ in 0..3 {
                    let n = 1 + rng.below(3);
                    let triggers: Vec<(PatternId, Option<u32>)> = (0..n)
                        .map(|i| {
                            let hint = (i == 0 && rng.below(5) == 0)
                                .then(|| terms[rng.below(terms.len())]);
                            (patterns[rng.below(patterns.len())], hint)
                        })
                        .collect();
                    total_matches += both(&mut egraph, &triggers).len();
                }
            }
        }
        // The generator must produce matches, or the comparison above proves little.
        assert!(total_matches > 5000, "only {total_matches} matches");
    }
}
