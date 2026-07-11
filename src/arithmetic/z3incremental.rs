// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Incremental Z3 arithmetic backend.
//!
//! Keeps a persistent `z3::Solver` in sync with CaDiCaL's trail: each
//! arithmetic literal is pushed via `assert_and_track` so its abs-lit
//! recovers from an unsat core, and each egraph merge is asserted as
//! `var_a == var_b` under the SAT lit produced by `make_eq(a, b)`.
//! Z3 `Int` vars are keyed by raw egraph id (not union-find root), so
//! definitional pinnings are stable across backtracks.

use crate::arithmetic::lia::stats::Stats as LiaStats;
use crate::arithmetic::lp::{ArithResult, Coefficient, FunctionType, LinearConstraint};
use crate::debug_println;
use crate::egraphs::traits::EgraphTrait;
use crate::solver_state::SolverState;
use crate::utils::{DeterministicHashMap, DeterministicHashSet};
use dashu::Integer;
use dashu::integer::IBig;
use yaspar_ir::ast::{
    ATerm::{self, App, Global, Not},
    Repr,
    alg::Constant as AlgConstant,
};
use z3::{
    SatResult, Solver,
    ast::{Bool, Int},
};

fn ibig_to_bigint(n: &IBig) -> num::BigInt {
    num::BigInt::parse_bytes(n.to_string().as_bytes(), 10).unwrap()
}

/// Parse a Z3 model value string like "3" or "(- 4)" into an IBig.
fn parse_z3_model_int(s: &str) -> IBig {
    if let Some(inner) = s.strip_prefix("(- ").and_then(|t| t.strip_suffix(')')) {
        -inner.parse::<IBig>().unwrap()
    } else {
        s.parse::<IBig>().unwrap()
    }
}

pub struct Z3IncrementalState {
    solver: Solver,
    var_map: DeterministicHashMap<u32, Int>,
    /// abs(lit) -> tracker Bool for `assert_and_track`. CaDiCaL's trail has
    /// at most one polarity of each var on it at a time, so one tracker per
    /// abs-lit is enough — the asserted body flips with the polarity.
    tracker_by_abs_lit: DeterministicHashMap<i32, Bool>,
    /// Abs-lits already known to be non-arithmetic; skip re-parsing.
    non_arithmetic_lits: DeterministicHashSet<i32>,
    /// Signed lits currently in Z3's scope. Guards against duplicate pushes
    /// when CaDiCaL re-notifies a literal at the same level.
    active_lits: DeterministicHashSet<i32>,
    /// Per-level record of pushed lits, mirrored on backtrack.
    lits_by_level: Vec<Vec<i32>>,
    /// Per-level `z3::push` count, popped on backtrack.
    push_counts: Vec<u32>,
    /// Definitional equalities (e.g. `var_5 == 5`, `var_{(+xy)} == var_x + var_y`).
    /// Global theory facts — replayed as assumptions since asserting them
    /// would tie them to a push scope that later gets popped.
    pinned_defs: Vec<Bool>,
    current_level: usize,
}

impl Z3IncrementalState {
    pub fn new() -> Self {
        Self {
            solver: Solver::new(),
            var_map: DeterministicHashMap::new(),
            tracker_by_abs_lit: DeterministicHashMap::new(),
            non_arithmetic_lits: DeterministicHashSet::default(),
            active_lits: DeterministicHashSet::default(),
            lits_by_level: vec![Vec::new()],
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
    }

    /// Get or create the Z3 `Int` variable for an egraph id, pinning its
    /// structural definition on first creation (e.g. `var_5 == 5`,
    /// `var_{(+xy)} == var_x + var_y`). Uninterpreted apps and Globals get
    /// no pin. Pins are stored in `pinned_defs` and replayed as assumptions
    /// on every `check_assumptions` — `Solver::assert` would tie them to
    /// the current push scope and lose them on `pop`.
    ///
    /// This is the only var-materialization entry point.
    fn var_for(&mut self, egraph_id: u32, solver_state: &mut SolverState) -> Int {
        if let Some(v) = self.var_map.get(&egraph_id) {
            return v.clone();
        }
        let v = Int::new_const(format!("var_{egraph_id}"));
        self.var_map.insert(egraph_id, v.clone());

        let solver_uid = solver_state.to_solver_uid(egraph_id);
        if let Some(expr) = extract_lazy_expression(solver_uid, solver_state) {
            // Skip pinning `var_i == 0 + 1*var_i` (plain Global or uninterp App).
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
                self.pinned_defs.push(Int::eq(&v, rhs));
                debug_println!(21, 0, "[z3inc] def var_{}=={:?}", egraph_id, entries);
            }
        }
        v
    }

    fn coeff_to_z3(
        &mut self,
        key: &Coefficient,
        coeff: &IBig,
        solver_state: &mut SolverState,
    ) -> Option<Int> {
        match key {
            Coefficient::Constant => Some(Int::from_big_int(&ibig_to_bigint(coeff))),
            Coefficient::Term(id) => {
                let v = self.var_for(*id, solver_state);
                Some(Int::from_big_int(&ibig_to_bigint(coeff)) * v)
            }
            Coefficient::Div(a, b) => {
                let av = self.var_for(*a, solver_state);
                let bv = self.var_for(*b, solver_state);
                Some(Int::from_big_int(&ibig_to_bigint(coeff)) * av.div(bv))
            }
            Coefficient::Mod(a, b) => {
                let av = self.var_for(*a, solver_state);
                let bv = self.var_for(*b, solver_state);
                Some(Int::from_big_int(&ibig_to_bigint(coeff)) * av.modulo(bv))
            }
        }
    }

    fn constraint_to_z3(&mut self, c: &LinearConstraint, solver_state: &mut SolverState) -> Bool {
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

    /// Build a LinearConstraint for a signed SAT literal, or None if the
    /// underlying term isn't an arithmetic inequality. Equality atoms are
    /// intentionally rejected — the egraph is the single source of truth for
    /// equalities (positive → merges via `drain_merge_queue`; negative →
    /// egraph disequalities).
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
        let App(identifier, args, _) = term.repr() else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }
        let left_expr = extract_lazy_expression(args[0].uid(), solver_state)?;
        let right_expr = extract_lazy_expression(args[1].uid(), solver_state)?;
        let (le, re, func) = match (identifier.0.symbol.as_str(), polarity) {
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

    pub fn notify_new_decision_level(&mut self) {
        self.current_level += 1;
        self.ensure_level_slot();
    }

    /// Pop everything pushed above `level`.
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
            self.current_level -= 1;
        }
        self.ensure_level_slot();
    }

    /// Push a newly-assigned SAT literal's arithmetic constraint (if any),
    /// tracked so the unsat core recovers it.
    pub fn on_literal_assignment(&mut self, lit: i32, solver_state: &mut SolverState) {
        let abs_lit = lit.abs();
        if self.non_arithmetic_lits.contains(&abs_lit) || self.active_lits.contains(&lit) {
            return;
        }
        let Some(constraint) = Self::extract_lazy_constraint(lit, solver_state) else {
            self.non_arithmetic_lits.insert(abs_lit);
            return;
        };
        let ast = self.constraint_to_z3(&constraint, solver_state);
        let tracker = self
            .tracker_by_abs_lit
            .entry(abs_lit)
            .or_insert_with(|| Bool::new_const(format!("lit_{abs_lit}")))
            .clone();
        self.ensure_level_slot();
        self.solver.push();
        self.push_counts[self.current_level] += 1;
        self.active_lits.insert(lit);
        self.lits_by_level[self.current_level].push(lit);
        self.solver.assert_and_track(ast, &tracker);
        debug_println!(
            21,
            0,
            "[z3inc] pushed atom lit={} at level {}",
            lit,
            self.current_level
        );
    }

    /// Drain the egraph's arithmetic merge queue, pushing each merge as a
    /// tracked `var_a == var_b` assertion. Returns SAT lits that
    /// `make_eq` created here (so the caller can register them as observed).
    pub fn drain_merge_queue(&mut self, solver_state: &mut SolverState) -> Vec<i32> {
        let merges = solver_state.egraph.drain_arithmetic_equalities();
        if merges.is_empty() {
            return Vec::new();
        }
        self.ensure_level_slot();
        let mut new_lits: Vec<i32> = Vec::new();
        for (a, b) in merges {
            let lit = solver_state.make_eq(a, b);
            let abs_lit = lit.abs();
            if !self.tracker_by_abs_lit.contains_key(&abs_lit) {
                new_lits.push(lit);
            }
            if self.active_lits.contains(&lit) {
                continue;
            }
            let va = self.var_for(a, solver_state);
            let vb = self.var_for(b, solver_state);
            let tracker = self
                .tracker_by_abs_lit
                .entry(abs_lit)
                .or_insert_with(|| Bool::new_const(format!("lit_{abs_lit}")))
                .clone();
            self.solver.push();
            self.push_counts[self.current_level] += 1;
            self.active_lits.insert(lit);
            self.lits_by_level[self.current_level].push(lit);
            self.solver.assert_and_track(Int::eq(&va, vb), &tracker);
            debug_println!(
                21,
                0,
                "[z3inc] pushed egraph merge var_{}==var_{} as lit {} at level {}",
                a,
                b,
                lit,
                self.current_level
            );
        }
        new_lits
    }

    /// Run `check_assumptions` under the currently-active trackers plus the
    /// pinned defs. On SAT, bucket each arithmetic term whose egraph id is
    /// its own class root by model value for the caller's Nelson-Oppen
    /// probe. On UNSAT, recover the SAT lits from the unsat core.
    pub fn check(&mut self, solver_state: &mut SolverState) -> ArithResult {
        debug_println!(21, 0, "[z3inc] check() at level {}", self.current_level);
        // Materialize every arithmetic term's var + pin before checking, so
        // `check_assumptions` sees all definitional equalities in the model.
        let arithmetic_terms = solver_state.arithmetic_terms.clone();
        for term_id in &arithmetic_terms {
            let egraph_id = solver_state.to_egraph_id(*term_id);
            let _ = self.var_for(egraph_id, solver_state);
        }
        // `assert_and_track` asserts `tracker => constraint`, so we need to
        // include each active tracker in the assumptions.
        let mut assumptions: Vec<Bool> = self
            .active_lits
            .iter()
            .filter_map(|lit| self.tracker_by_abs_lit.get(&lit.abs()).cloned())
            .collect();
        assumptions.extend(self.pinned_defs.iter().cloned());
        match self.solver.check_assumptions(&assumptions) {
            SatResult::Sat => {
                let model = self.solver.get_model().unwrap();
                let mut buckets: DeterministicHashMap<IBig, DeterministicHashSet<u64>> =
                    DeterministicHashMap::new();
                for term_id in &arithmetic_terms {
                    let egraph_id = solver_state.to_egraph_id(*term_id);
                    if solver_state.egraph.find(egraph_id) != egraph_id {
                        continue;
                    }
                    let v = self.var_for(egraph_id, solver_state);
                    if let Some(val) = model.eval(&v, true) {
                        let ibig = parse_z3_model_int(&val.to_string());
                        buckets.entry(ibig).or_default().insert(*term_id);
                    }
                }
                debug_println!(21, 0, "[z3inc] SAT buckets={:?}", buckets);
                ArithResult::Sat(buckets, LiaStats::new())
            }
            SatResult::Unsat => {
                let core = self.solver.get_unsat_core();
                // Trackers are named `lit_{abs_lit}` (possibly `|...|`-quoted).
                // Pinned-def asts also appear in the core; filter them out.
                // Recover the signed lit via `active_lits`.
                let mut lits: DeterministicHashSet<i32> = core
                    .iter()
                    .filter_map(|ast| {
                        let raw = ast.to_string();
                        let abs_lit: i32 =
                            raw.trim_matches('|').strip_prefix("lit_")?.parse().ok()?;
                        let signed = if self.active_lits.contains(&abs_lit) {
                            abs_lit
                        } else {
                            -abs_lit
                        };
                        Some(-signed)
                    })
                    .collect();
                // Empty core would mean the contradiction lies entirely in
                // pinned defs — that's a bug. Fall back to blaming every
                // active lit rather than reporting an unsound `Unsat([])`.
                if lits.is_empty() {
                    lits.extend(self.active_lits.iter().map(|l| -l));
                }
                ArithResult::Unsat(lits.into_iter().collect(), LiaStats::new())
            }
            SatResult::Unknown => panic!("z3incremental: Z3 returned unknown"),
        }
    }
}

impl Default for Z3IncrementalState {
    fn default() -> Self {
        Self::new()
    }
}

/// `find()`-free version of `extract_linear_expression`: every
/// `Coefficient::Term(id)` refers to the term's own raw egraph id.
/// Merges are conveyed to Z3 separately via `drain_merge_queue`.
/// Returns None on unsupported shapes.
fn extract_lazy_expression(
    term_id: u64,
    solver_state: &mut SolverState,
) -> Option<DeterministicHashMap<Coefficient, Integer>> {
    let term = solver_state.get_term(term_id);
    let mut expr: DeterministicHashMap<Coefficient, Integer> = DeterministicHashMap::new();
    expr.insert(Coefficient::Constant, IBig::from(0));

    let opaque = |ss: &mut SolverState, expr: &mut DeterministicHashMap<Coefficient, Integer>| {
        expr.insert(Coefficient::Term(ss.to_egraph_id(term_id)), IBig::from(1));
    };
    // Add `sub` to `expr`, optionally negating.
    let accumulate = |expr: &mut DeterministicHashMap<Coefficient, Integer>,
                      sub: DeterministicHashMap<Coefficient, Integer>,
                      negate: bool| {
        for (k, c) in sub {
            let c = if negate { -c } else { c };
            *expr.entry(k).or_insert(IBig::from(0)) += c;
        }
    };

    match term.repr() {
        ATerm::Constant(AlgConstant::Numeral(num), _) => {
            if let Ok(value) = num.to_string().parse::<Integer>() {
                *expr.get_mut(&Coefficient::Constant).unwrap() = value;
            }
            Some(expr)
        }
        ATerm::Constant(..) => Some(expr),
        Global(..) => {
            opaque(solver_state, &mut expr);
            Some(expr)
        }
        App(identifier, args, _) => match (identifier.0.symbol.as_str(), args.len()) {
            ("+", _) => {
                for arg in args.iter() {
                    accumulate(
                        &mut expr,
                        extract_lazy_expression(arg.uid(), solver_state)?,
                        false,
                    );
                }
                Some(expr)
            }
            ("-", 0) => None,
            ("-", 1) => {
                accumulate(
                    &mut expr,
                    extract_lazy_expression(args[0].uid(), solver_state)?,
                    true,
                );
                Some(expr)
            }
            ("-", _) => {
                accumulate(
                    &mut expr,
                    extract_lazy_expression(args[0].uid(), solver_state)?,
                    false,
                );
                for arg in args.iter().skip(1) {
                    accumulate(
                        &mut expr,
                        extract_lazy_expression(arg.uid(), solver_state)?,
                        true,
                    );
                }
                Some(expr)
            }
            ("*", 2) => {
                let left = extract_lazy_expression(args[0].uid(), solver_state)?;
                let right = extract_lazy_expression(args[1].uid(), solver_state)?;
                let (cst, other) = if left.len() == 1 && left.contains_key(&Coefficient::Constant) {
                    (left[&Coefficient::Constant].clone(), right)
                } else if right.len() == 1 && right.contains_key(&Coefficient::Constant) {
                    (right[&Coefficient::Constant].clone(), left)
                } else {
                    // Nonlinear — opaque.
                    opaque(solver_state, &mut expr);
                    return Some(expr);
                };
                for (k, c) in other {
                    expr.insert(k, &cst * c);
                }
                Some(expr)
            }
            ("div", 2) => {
                let a = solver_state.to_egraph_id(args[0].uid());
                let b = solver_state.to_egraph_id(args[1].uid());
                expr.insert(Coefficient::Div(a, b), IBig::from(1));
                Some(expr)
            }
            ("mod", 2) => {
                let a = solver_state.to_egraph_id(args[0].uid());
                let b = solver_state.to_egraph_id(args[1].uid());
                expr.insert(Coefficient::Mod(a, b), IBig::from(1));
                Some(expr)
            }
            ("*" | "div" | "mod", _) => None,
            _ => {
                opaque(solver_state, &mut expr);
                Some(expr)
            }
        },
        _ => {
            opaque(solver_state, &mut expr);
            Some(expr)
        }
    }
}
