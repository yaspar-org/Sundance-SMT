// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Lazy Z3 arithmetic backend.
//!
//! Design:
//! * Persistent `z3::Solver` lives for the whole search.
//! * Each egraph node with sort Int gets its own Z3 `Int` variable, keyed by
//!   its raw egraph id (NOT its union-find root). We never canonicalise at
//!   encoding time — merges are conveyed to Z3 as explicit `var_a == var_b`
//!   assertions.
//! * Every `z3::Solver::push` is recorded against the current SAT decision
//!   level so that `notify_backtrack(level)` can `pop` the matching count.
//! * Arithmetic literals from CaDiCaL's trail (`notify_assignment`) are
//!   translated once, cached by literal, and pushed with `assert_and_track`
//!   so that an unsat core maps back to SAT literals.
//! * Egraph merges from `Egraph::arithmetic_merge_queue` are drained by the
//!   propagator and pushed here as `Int::eq(var_a, var_b)`.
//! * `check()` runs `solver.check()` and returns either `ArithResult::Unsat`
//!   (with the SAT literals from the unsat core) or `ArithResult::Sat` (with
//!   the current arithmetic-term roots grouped by model value, for the
//!   downstream Nelson-Oppen model-based probe).

use crate::arithmetic::lia::stats::Stats as LiaStats;
use crate::arithmetic::lp::{ArithResult, Coefficient, FunctionType, LinearConstraint};
use crate::debug_println;
use crate::egraphs::traits::EgraphTrait;
use crate::solver_state::SolverState;
use crate::utils::{DeterministicHashMap, DeterministicHashSet};
use dashu::Integer;
use dashu::integer::IBig;
use yaspar_ir::ast::{
    ATerm::{self, App, Eq, Global, Not},
    FetchSort, HasArena, Repr,
    alg::Constant as AlgConstant,
};
use z3::{
    SatResult, Solver,
    ast::{Bool, Int},
};

/// Convert a dashu IBig to num::BigInt (Z3 uses num::BigInt).
fn ibig_to_bigint(n: &IBig) -> num::BigInt {
    num::BigInt::parse_bytes(n.to_string().as_bytes(), 10).unwrap()
}

/// Parse a Z3 model value string like "3" or "(- 4)" into an IBig.
fn parse_z3_model_int(s: &str) -> IBig {
    if let Some(inner) = s.strip_prefix("(- ").and_then(|t| t.strip_suffix(')')) {
        -inner.parse::<IBig>().unwrap_or_else(|e| {
            panic!("Failed to parse Z3 model value inner '{inner}' from '{s}': {e}")
        })
    } else {
        s.parse::<IBig>()
            .unwrap_or_else(|e| panic!("Failed to parse Z3 model value '{s}': {e}"))
    }
}

/// State for the lazy Z3 arithmetic backend.
pub struct Z3LazyState {
    /// The persistent Z3 solver.
    solver: Solver,
    /// egraph_id -> its Z3 Int variable. Populated on demand.
    var_map: DeterministicHashMap<u32, Int>,
    /// SAT literal (unsigned, positive) -> its tracker Bool used by
    /// `assert_and_track`, so that an unsat core recovers the literal.
    /// Present iff the literal has been encoded into the solver at least once.
    tracker_by_lit: DeterministicHashMap<i32, Bool>,
    /// tracker string name -> signed SAT literal that produced it. Populated
    /// alongside `tracker_by_lit`; we use `to_string()` to look up in the
    /// unsat core because z3-rs `Bool` doesn't hash by identity.
    lit_by_tracker_name: DeterministicHashMap<String, i32>,
    /// Absolute value of literals for which we've already decided
    /// "not arithmetic" — skip re-parsing on every re-assignment.
    non_arithmetic_lits: DeterministicHashSet<i32>,
    /// Signed literals currently pushed into the persistent Z3 solver.
    /// Prevents duplicate pushes when CaDiCaL notifies the same literal
    /// more than once at the same level (e.g. after simplification).
    active_lits: DeterministicHashSet<i32>,
    /// For each decision level, the signed lits that were pushed at that
    /// level. Used by `notify_backtrack` to remove them from `active_lits`.
    lits_by_level: Vec<Vec<i32>>,
    /// Signed SAT literals whose notify_assignment triggered at least one
    /// egraph merge we've asserted into Z3 (per decision level). Used as an
    /// over-approximate conflict clause when Z3 returns UNSAT with an empty
    /// core (i.e. the contradiction lives entirely in unconditional merge
    /// assertions).
    merge_provoker_lits: DeterministicHashSet<i32>,
    /// Per-level list of merge provokers, so backtrack can shrink the set.
    merge_provokers_by_level: Vec<Vec<i32>>,
    /// Stack of push counts per decision level. Entry `i` is how many
    /// `z3::push`es we've done at level `i`; on `notify_backtrack(level)`
    /// we pop everything above `level`.
    /// Indexed by decision level; grows as decision level grows.
    push_counts: Vec<u32>,
    /// Definitional pinnings (e.g. `var_5 == 5`, `var_{(+xy)} == var_x + var_y`).
    /// These are theory facts that hold globally, so we replay them as
    /// assumptions on every `check_assumptions` rather than asserting them into
    /// a specific scope (where a later `pop` would erase them).
    pinned_defs: Vec<Bool>,
    /// Current SAT decision level, tracked internally to match the propagator.
    current_level: usize,
}

impl Z3LazyState {
    pub fn new() -> Self {
        Self {
            solver: Solver::new(),
            var_map: DeterministicHashMap::new(),
            tracker_by_lit: DeterministicHashMap::new(),
            lit_by_tracker_name: DeterministicHashMap::new(),
            non_arithmetic_lits: DeterministicHashSet::default(),
            active_lits: DeterministicHashSet::default(),
            lits_by_level: vec![Vec::new()],
            merge_provoker_lits: DeterministicHashSet::default(),
            merge_provokers_by_level: vec![Vec::new()],
            push_counts: vec![0],
            pinned_defs: Vec::new(),
            current_level: 0,
        }
    }

    /// Ensure `push_counts` and per-level tracking vectors are indexed up to
    /// `self.current_level`.
    fn ensure_level_slot(&mut self) {
        while self.push_counts.len() <= self.current_level {
            self.push_counts.push(0);
        }
        while self.lits_by_level.len() <= self.current_level {
            self.lits_by_level.push(Vec::new());
        }
        while self.merge_provokers_by_level.len() <= self.current_level {
            self.merge_provokers_by_level.push(Vec::new());
        }
    }

    /// Get or create the Z3 Int variable for an egraph id.
    fn var_for(&mut self, egraph_id: u32) -> Int {
        self.var_map
            .entry(egraph_id)
            .or_insert_with(|| Int::new_const(format!("var_{egraph_id}")))
            .clone()
    }

    /// Ensure the Z3 var for `egraph_id` exists AND that, on first sight, we
    /// pushed a **definitional** equality tying it to its term structure
    /// (`var_{id} == <constant>` for numeric constants, `var_{id} == <linear
    /// combination in child vars>` for arithmetic applications like `+ - *`).
    /// This makes egraph-derived merges informative without a normalization
    /// pass: e.g. once `x==y` is asserted, Z3 sees `var_{f(x)} == var_{f(y)}`
    /// via the egraph merge callback AND both `var_{f(x)} == def(f, x)` and
    /// `var_{f(y)} == def(f, y)` pinned at load time, giving the theory
    /// combination its usual power.
    ///
    /// Uses `extract_lazy_expression` (no `find()`) so the pinning is stable
    /// across egraph backtracks — merges are conveyed separately via
    /// `drain_merge_queue`.
    ///
    /// Pins live in `pinned_defs` and get replayed as assumptions on every
    /// `check_assumptions` — the `Solver::assert` route would land them in
    /// the top scope and get popped on backtrack.
    fn var_for_with_pinning(
        &mut self,
        egraph_id: u32,
        solver_state: &mut SolverState,
    ) -> Int {
        let is_new = !self.var_map.contains_key(&egraph_id);
        let v = self.var_for(egraph_id);
        if is_new {
            let solver_uid = solver_state.to_solver_uid(egraph_id);
            if let Some(expr) = extract_lazy_expression(solver_uid, solver_state) {
                // If the expression is exactly `var_{egraph_id}` (a plain
                // Global or an uninterpreted-function App), skip pinning.
                let is_self_reference = expr.len() == 2
                    && expr.get(&Coefficient::Constant) == Some(&IBig::from(0))
                    && expr.get(&Coefficient::Term(egraph_id)) == Some(&IBig::from(1));
                if !is_self_reference {
                    let mut rhs = Int::from_i64(0);
                    let entries: Vec<(Coefficient, IBig)> =
                        expr.iter().map(|(k, v)| (*k, v.clone())).collect();
                    for (k, c) in &entries {
                        if let Some(e) = self.coeff_to_z3(k, c, solver_state) {
                            rhs += e;
                        }
                    }
                    let v_final = self.var_map[&egraph_id].clone();
                    let def = Int::eq(&v_final, rhs);
                    self.pinned_defs.push(def);
                    debug_println!(
                        21,
                        0,
                        "[z3lazy] def var_{}=={:?}",
                        egraph_id,
                        entries
                    );
                    return v_final;
                }
            }
        }
        v
    }

    /// Translate a coefficient key to a Z3 Int expression scaled by `coeff`.
    /// Uses raw egraph ids as variables — no `find()`. Pins numeric constants.
    fn coeff_to_z3(
        &mut self,
        key: &Coefficient,
        coeff: &IBig,
        solver_state: &mut SolverState,
    ) -> Option<Int> {
        match key {
            Coefficient::Constant => Some(Int::from_big_int(&ibig_to_bigint(coeff))),
            Coefficient::Term(id) => {
                let v = self.var_for_with_pinning(*id, solver_state);
                Some(Int::from_big_int(&ibig_to_bigint(coeff)) * v)
            }
            Coefficient::Div(a, b) => {
                let av = self.var_for_with_pinning(*a, solver_state);
                let bv = self.var_for_with_pinning(*b, solver_state);
                Some(Int::from_big_int(&ibig_to_bigint(coeff)) * av.div(bv))
            }
            Coefficient::Mod(a, b) => {
                let av = self.var_for_with_pinning(*a, solver_state);
                let bv = self.var_for_with_pinning(*b, solver_state);
                Some(Int::from_big_int(&ibig_to_bigint(coeff)) * av.modulo(bv))
            }
        }
    }

    /// Encode a LinearConstraint as a Z3 Bool.
    fn constraint_to_z3(
        &mut self,
        c: &LinearConstraint,
        solver_state: &mut SolverState,
    ) -> Bool {
        let mut left = Int::from_i64(0);
        for (k, v) in &c.left_expr {
            if let Some(e) = self.coeff_to_z3(k, v, solver_state) {
                left += e;
            }
        }
        let mut right = Int::from_i64(0);
        for (k, v) in &c.right_expr {
            if let Some(e) = self.coeff_to_z3(k, v, solver_state) {
                right += e;
            }
        }
        match c.function {
            FunctionType::Leq => Int::le(&left, &right),
            FunctionType::Lt => Int::lt(&left, &right),
            FunctionType::Eq => Int::eq(&left, right),
        }
    }

    /// Try to build a LinearConstraint for a signed SAT literal.
    /// Returns None if the underlying term is not an arithmetic atom.
    /// Uses raw egraph ids (no `find()`) — no additional_constraints are
    /// generated, since egraph merges are conveyed as explicit equalities.
    fn extract_lazy_constraint(
        lit: i32,
        solver_state: &mut SolverState,
    ) -> Option<LinearConstraint> {
        let (term_id, polarity) = solver_state.get_u64_from_lit_with_polarity(lit);
        let term = solver_state.get_term(term_id);
        let (term, polarity) = match term.repr() {
            Not(t) => (t.clone(), !polarity),
            _ => (term, polarity),
        };
        match term.repr() {
            App(identifier, args, _) => {
                if args.len() != 2 {
                    return None;
                }
                // Use the lazy extractor (no find()) so the encoding of a
                // literal is stable — Z3 push/pop mirrors the assignment
                // stack precisely, without depending on egraph state.
                let left_expr = extract_lazy_expression(args[0].uid(), solver_state)?;
                let right_expr = extract_lazy_expression(args[1].uid(), solver_state)?;
                let sym = identifier.0.symbol.as_str();
                let (le, re, func) = match (sym, polarity) {
                    ("<=", true) => (left_expr, right_expr, FunctionType::Leq),
                    ("<=", false) => (right_expr, left_expr, FunctionType::Lt),
                    (">=", true) => (right_expr, left_expr, FunctionType::Leq),
                    (">=", false) => (left_expr, right_expr, FunctionType::Lt),
                    ("<", true) => (left_expr, right_expr, FunctionType::Lt),
                    ("<", false) => (right_expr, left_expr, FunctionType::Leq),
                    (">", true) => (right_expr, left_expr, FunctionType::Lt),
                    (">", false) => (left_expr, right_expr, FunctionType::Leq),
                    _ => return None,
                };
                Some(LinearConstraint::new(le, re, func, vec![]))
            }
            Eq(a, b) if polarity => {
                // Only encode into Z3 if both sides are Int-sorted. Poly /
                // datatype equalities collapse to fresh Int variables under
                // our encoding, which is unsound (it forces theories that
                // don't intersect on integers to behave as if they did).
                let a_sort = a.get_sort(solver_state.context.arena()).to_string();
                let b_sort = b.get_sort(solver_state.context.arena()).to_string();
                if a_sort != "Int" || b_sort != "Int" {
                    return None;
                }
                let le = extract_lazy_expression(a.uid(), solver_state)?;
                let re = extract_lazy_expression(b.uid(), solver_state)?;
                Some(LinearConstraint::new(le, re, FunctionType::Eq, vec![]))
            }
            _ => None,
        }
    }

    /// Called when the SAT solver enters a new decision level.
    pub fn notify_new_decision_level(&mut self) {
        self.current_level += 1;
        self.ensure_level_slot();
    }

    /// Called on backtrack. Pops all `z3::push`es done at levels > `level`.
    pub fn notify_backtrack(&mut self, level: usize) {
        while self.current_level > level {
            let n = self.push_counts.pop().unwrap_or(0);
            if n > 0 {
                self.solver.pop(n);
            }
            if let Some(lits) = self.lits_by_level.pop() {
                for l in lits {
                    self.active_lits.remove(&l);
                }
            }
            if let Some(lits) = self.merge_provokers_by_level.pop() {
                for l in lits {
                    self.merge_provoker_lits.remove(&l);
                }
            }
            self.current_level -= 1;
        }
        self.ensure_level_slot();
    }

    /// Called for each SAT literal newly assigned by CaDiCaL. If the
    /// literal corresponds to an arithmetic atom, push its constraint into
    /// the persistent solver at the current level (tracked so the unsat
    /// core recovers the literal).
    pub fn on_literal_assignment(
        &mut self,
        lit: i32,
        solver_state: &mut SolverState,
    ) {
        let abs_lit = lit.abs();
        if self.non_arithmetic_lits.contains(&abs_lit) {
            return;
        }
        // CaDiCaL may re-notify the same literal (e.g. it appears both as an
        // individual notify_assignment and again in the initial-trail batch).
        // Guard against a duplicate push.
        if self.active_lits.contains(&lit) {
            return;
        }
        let Some(constraint) = Self::extract_lazy_constraint(lit, solver_state) else {
            self.non_arithmetic_lits.insert(abs_lit);
            return;
        };
        let ast = self.constraint_to_z3(&constraint, solver_state);
        let tracker_name = format!("lit_{lit}");
        let tracker = Bool::new_const(tracker_name.clone());
        self.tracker_by_lit.insert(lit, tracker.clone());
        self.lit_by_tracker_name.insert(tracker_name, lit);
        self.ensure_level_slot();
        self.solver.push();
        self.push_counts[self.current_level] += 1;
        self.active_lits.insert(lit);
        self.lits_by_level[self.current_level].push(lit);
        self.solver.assert_and_track(ast, &tracker);
        debug_println!(
            21,
            0,
            "[z3lazy] pushed atom lit={} at level {}",
            lit,
            self.current_level
        );
    }

    /// Drain the egraph's arithmetic merge queue into the persistent Z3 solver.
    /// Each merge becomes `var_a == var_b` asserted at the current level.
    /// `provoker` is the SAT literal (if any) whose `notify_assignment` produced
    /// these merges — recorded so that if Z3 later reports UNSAT with an empty
    /// core, we can blame it in the fallback conflict clause.
    pub fn drain_merge_queue(
        &mut self,
        solver_state: &mut SolverState,
        provoker: Option<i32>,
    ) {
        // Take ownership of the queue to avoid a borrow conflict.
        let merges = std::mem::take(&mut solver_state.egraph.arithmetic_merge_queue);
        if merges.is_empty() {
            return;
        }
        self.ensure_level_slot();
        if let Some(lit) = provoker
            && !self.merge_provoker_lits.contains(&lit)
        {
            self.merge_provoker_lits.insert(lit);
            self.merge_provokers_by_level[self.current_level].push(lit);
        }
        for (a, b) in merges {
            let va = self.var_for_with_pinning(a, solver_state);
            let vb = self.var_for_with_pinning(b, solver_state);
            let eq = Int::eq(&va, vb);
            self.solver.push();
            self.push_counts[self.current_level] += 1;
            self.solver.assert(&eq);
            debug_println!(
                21,
                0,
                "[z3lazy] pushed egraph merge var_{}==var_{} at level {}",
                a,
                b,
                self.current_level
            );
        }
    }

    /// Run `solver.check()`. On SAT, group current arithmetic-term roots by
    /// model value so the caller's model-based Nelson-Oppen probe can run.
    /// On UNSAT, translate the unsat core back into SAT literals.
    pub fn check(&mut self, solver_state: &mut SolverState) -> ArithResult {
        debug_println!(
            21,
            0,
            "[z3lazy] check() at level {}",
            self.current_level
        );
        // Ensure every arithmetic-term class root has been introduced to Z3
        // with its definitional equality pinned. If we defer this until the
        // model-evaluation loop below, Z3 has already produced a model
        // without seeing the definitions and the buckets are meaningless.
        let n_arith = solver_state.arithmetic_terms.len();
        for idx in 0..n_arith {
            let term_id = solver_state.arithmetic_terms[idx];
            let egraph_id = solver_state.to_egraph_id(term_id);
            let _ = self.var_for_with_pinning(egraph_id, solver_state);
        }
        // Every arithmetic literal was pushed via `assert_and_track(constraint,
        // tracker)`, which encodes `tracker => constraint`. Z3 would happily
        // satisfy that by picking tracker=false unless we tell it the tracker
        // is true — so we run `check_assumptions` with the currently-active
        // trackers. Include the definitional pinnings too — those live outside
        // any push scope so they'd otherwise be pop'd.
        let mut assumptions: Vec<Bool> = self
            .active_lits
            .iter()
            .filter_map(|lit| self.tracker_by_lit.get(lit).cloned())
            .collect();
        assumptions.extend(self.pinned_defs.iter().cloned());
        match self.solver.check_assumptions(&assumptions) {
            SatResult::Sat => {
                let model = self.solver.get_model().unwrap();
                let mut buckets: DeterministicHashMap<IBig, DeterministicHashSet<u64>> =
                    DeterministicHashMap::new();
                for idx in 0..solver_state.arithmetic_terms.len() {
                    let term_id = solver_state.arithmetic_terms[idx];
                    let egraph_id = solver_state.to_egraph_id(term_id);
                    // Only report one representative per union-find class —
                    // otherwise the model-based probe wastes work merging
                    // pairs that are already equal.
                    if solver_state.egraph.find(egraph_id) != egraph_id {
                        continue;
                    }
                    let v = self.var_for_with_pinning(egraph_id, solver_state);
                    if let Some(val) = model.eval(&v, true) {
                        let ibig = parse_z3_model_int(&val.to_string());
                        buckets.entry(ibig).or_default().insert(term_id);
                    }
                }
                debug_println!(21, 0, "[z3lazy] SAT buckets={:?}", buckets);
                ArithResult::Sat(buckets, LiaStats::new())
            }
            SatResult::Unsat => {
                let core = self.solver.get_unsat_core();
                let mut lits: DeterministicHashSet<i32> = DeterministicHashSet::default();
                for ast in &core {
                    let name = ast.to_string();
                    if let Some(&lit) = self.lit_by_tracker_name.get(&name) {
                        lits.insert(-lit);
                    } else {
                        debug_println!(
                            21,
                            0,
                            "[z3lazy] unsat core contained unknown tracker: {}",
                            name
                        );
                    }
                }
                // The unsat core can be empty when the inconsistency lives
                // entirely in unconditionally-asserted merges/defs. That's
                // unsound to report as `Unsat([])` (CaDiCaL would treat it as
                // a global contradiction). Fall back to blaming EVERY active
                // arithmetic literal AND every "merge-provoker" (a SAT lit
                // whose assignment triggered an egraph merge we pushed).
                if lits.is_empty() {
                    lits.extend(self.active_lits.iter().map(|l| -l));
                    lits.extend(self.merge_provoker_lits.iter().map(|l| -l));
                }
                ArithResult::Unsat(lits.into_iter().collect(), LiaStats::new())
            }
            SatResult::Unknown => panic!("z3lazy: Z3 returned unknown"),
        }
    }
}

impl Default for Z3LazyState {
    fn default() -> Self {
        Self::new()
    }
}

/// Version of `extract_linear_expression` that never calls `egraph.find()`.
/// Returns None if the term is not an arithmetic term of a supported shape.
/// Every `Coefficient::Term(id)` in the returned map refers to the term's
/// own raw egraph id — merges are conveyed to Z3 separately.
fn extract_lazy_expression(
    term_id: u64,
    solver_state: &mut SolverState,
) -> Option<DeterministicHashMap<Coefficient, Integer>> {
    let term = solver_state.get_term(term_id);
    let mut expr: DeterministicHashMap<Coefficient, Integer> = DeterministicHashMap::new();
    expr.insert(Coefficient::Constant, IBig::from(0));
    match term.repr() {
        ATerm::Constant(c, _) => {
            if let AlgConstant::Numeral(num) = c
                && let Ok(value) = num.to_string().parse::<Integer>()
            {
                *expr.get_mut(&Coefficient::Constant).unwrap() = value;
            }
            Some(expr)
        }
        Global(..) => {
            expr.insert(
                Coefficient::Term(solver_state.to_egraph_id(term_id)),
                IBig::from(1),
            );
            Some(expr)
        }
        App(identifier, args, _) => match identifier.0.symbol.as_str() {
            "+" => {
                for arg in args.iter() {
                    let sub = extract_lazy_expression(arg.uid(), solver_state)?;
                    for (k, c) in sub {
                        if k == Coefficient::Constant {
                            *expr.get_mut(&Coefficient::Constant).unwrap() += c;
                        } else {
                            *expr.entry(k).or_insert(IBig::from(0)) += c;
                        }
                    }
                }
                Some(expr)
            }
            "-" => {
                if args.is_empty() {
                    return None;
                }
                if args.len() == 1 {
                    let sub = extract_lazy_expression(args[0].uid(), solver_state)?;
                    for (k, c) in sub {
                        expr.insert(k, -c);
                    }
                    Some(expr)
                } else {
                    let first = extract_lazy_expression(args[0].uid(), solver_state)?;
                    for (k, c) in first {
                        if k == Coefficient::Constant {
                            *expr.get_mut(&Coefficient::Constant).unwrap() += c;
                        } else {
                            *expr.entry(k).or_insert(IBig::from(0)) += c;
                        }
                    }
                    for arg in args.iter().skip(1) {
                        let sub = extract_lazy_expression(arg.uid(), solver_state)?;
                        for (k, c) in sub {
                            if k == Coefficient::Constant {
                                *expr.get_mut(&Coefficient::Constant).unwrap() -= c;
                            } else {
                                *expr.entry(k).or_insert(IBig::from(0)) -= c;
                            }
                        }
                    }
                    Some(expr)
                }
            }
            "*" => {
                if args.len() != 2 {
                    return None;
                }
                let left = extract_lazy_expression(args[0].uid(), solver_state)?;
                let right = extract_lazy_expression(args[1].uid(), solver_state)?;
                if left.len() == 1 && left.contains_key(&Coefficient::Constant) {
                    let cst = left[&Coefficient::Constant].clone();
                    for (k, c) in right {
                        expr.insert(k, &cst * c);
                    }
                    Some(expr)
                } else if right.len() == 1 && right.contains_key(&Coefficient::Constant) {
                    let cst = right[&Coefficient::Constant].clone();
                    for (k, c) in left {
                        expr.insert(k, &cst * c);
                    }
                    Some(expr)
                } else {
                    // Nonlinear — treat the whole App as an opaque term.
                    let id = solver_state.to_egraph_id(term_id);
                    expr.insert(Coefficient::Term(id), IBig::from(1));
                    Some(expr)
                }
            }
            "div" => {
                if args.len() != 2 {
                    return None;
                }
                let a = solver_state.to_egraph_id(args[0].uid());
                let b = solver_state.to_egraph_id(args[1].uid());
                expr.insert(Coefficient::Div(a, b), IBig::from(1));
                Some(expr)
            }
            "mod" => {
                if args.len() != 2 {
                    return None;
                }
                let a = solver_state.to_egraph_id(args[0].uid());
                let b = solver_state.to_egraph_id(args[1].uid());
                expr.insert(Coefficient::Mod(a, b), IBig::from(1));
                Some(expr)
            }
            _ => {
                // Uninterpreted function application — treat as opaque.
                let id = solver_state.to_egraph_id(term_id);
                expr.insert(Coefficient::Term(id), IBig::from(1));
                Some(expr)
            }
        },
        _ => {
            let id = solver_state.to_egraph_id(term_id);
            expr.insert(Coefficient::Term(id), IBig::from(1));
            Some(expr)
        }
    }
}
