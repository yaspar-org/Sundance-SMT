// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Z3-based implementation of `IncrementalArithSolver`.
//!
//! Keeps a persistent `z3::Solver` in sync with CaDiCaL's trail, separating
//! internalization from assignment: the translator registers and internalizes
//! the arithmetic known before the search at level 0, and a constraint pushed
//! later only adds a bound. Each pushed constraint or equality is asserted via
//! `assert_and_track` so its abs-lit recovers from an unsat core.
//! Each decision level has its own Z3 scope, popped when CaDiCaL backtracks
//! below it. Pushed lits are queued and asserted together in their level's
//! scope before the next check or decision.
//! VarIds are never recycled. A definition asserted in a scope that a
//! backtrack pops is re-asserted when its var is next used.

use crate::arithmetic::incremental_solver::{
    ArithCheckResult, ArithConstraint, ArithExpr, IncrementalArithSolver, PartialCheckResult, VarId,
};
use crate::debug_println;
use crate::utils::{DeterministicHashMap, DeterministicHashSet};
use dashu::integer::IBig;
use z3::{
    SatResult, Solver,
    ast::{Bool, Int},
};

fn ibig_to_bigint(n: &IBig) -> num::BigInt {
    num::BigInt::parse_bytes(n.to_string().as_bytes(), 10).unwrap()
}

fn parse_z3_model_int(s: &str) -> IBig {
    if let Some(inner) = s.strip_prefix("(- ").and_then(|t| t.strip_suffix(')')) {
        -inner.parse::<IBig>().unwrap()
    } else {
        s.parse::<IBig>().unwrap()
    }
}

/// The vars an expression refers to.
fn expr_vars(expr: &ArithExpr) -> Vec<VarId> {
    let mut vars: Vec<VarId> = expr.terms.iter().map(|(v, _)| *v).collect();
    for (a, b, _) in expr.divs.iter().chain(&expr.mods) {
        vars.push(*a);
        vars.push(*b);
    }
    vars
}

/// What a decision level added, undone when CaDiCaL backtracks below it.
#[derive(Default)]
struct Level {
    /// Lits assigned at this level, removed from `active_lits` on backtrack.
    lits: Vec<i32>,
    /// Vars whose definitions are in this level's scope; marked undefined on
    /// backtrack.
    vars: Vec<VarId>,
}

pub struct Z3IncrementalState {
    solver: Solver,
    /// VarId -> Z3 Int variable.
    vars: Vec<Int>,
    /// VarId -> the RHS of its definition, kept to re-assert it after a
    /// backtrack pops it.
    definitions: Vec<Option<ArithExpr>>,
    /// VarId -> whether its definition (if any) is asserted in a live scope.
    defined: Vec<bool>,
    /// VarIds whose model values should be reported in check() SAT buckets.
    model_vars: Vec<VarId>,
    /// VarId -> whether it is in `model_vars`.
    is_model_var: Vec<bool>,
    /// abs(lit) -> tracker Bool for `assert_and_track`.
    tracker_by_abs_lit: DeterministicHashMap<i32, Bool>,
    /// Signed lits on the trail, asserted or queued. Guards against duplicate
    /// assertions when CaDiCaL re-notifies a literal at the same level.
    active_lits: DeterministicHashSet<i32>,
    /// One entry per decision level, from level 0 up to the current level.
    /// Every level above 0 has its own Z3 scope.
    levels: Vec<Level>,
    /// Lits pushed at the current level since the last check, with their
    /// constraints, in push order. Asserted by `flush_queued`.
    queued: Vec<(i32, Bool)>,
    /// Whether lits were queued or scopes popped since the last check, i.e.
    /// whether the next check could be any different from the last one.
    changed_since_check: bool,
    /// Tracked assertions added since the last (partial or full) check.
    pending_partial_assertions: usize,
    /// Checks run so far, numbering the `--trace-z3-queries` log.
    checks: usize,
}

impl Z3IncrementalState {
    pub fn new() -> Self {
        Self {
            solver: Solver::new(),
            vars: Vec::new(),
            definitions: Vec::new(),
            defined: Vec::new(),
            model_vars: Vec::new(),
            is_model_var: Vec::new(),
            tracker_by_abs_lit: DeterministicHashMap::new(),
            active_lits: DeterministicHashSet::default(),
            levels: vec![Level::default()],
            queued: Vec::new(),
            changed_since_check: false,
            pending_partial_assertions: 0,
            checks: 0,
        }
    }

    fn current_level(&self) -> usize {
        self.levels.len() - 1
    }

    fn top_level(&mut self) -> &mut Level {
        self.levels.last_mut().unwrap()
    }

    fn unsat_core_clause(&self) -> Vec<i32> {
        let lits: DeterministicHashSet<i32> = self
            .solver
            .get_unsat_core()
            .iter()
            .filter_map(|ast| {
                let raw = ast.to_string();
                let abs_lit: i32 = raw.trim_matches('|').strip_prefix("lit_")?.parse().ok()?;
                let signed = if self.active_lits.contains(&abs_lit) {
                    abs_lit
                } else {
                    -abs_lit
                };
                Some(-signed)
            })
            .collect();
        assert!(
            !lits.is_empty(),
            "z3incremental: unsat core contained no tracked lits"
        );
        lits.into_iter().collect()
    }

    fn get_var(&self, id: VarId) -> &Int {
        &self.vars[id as usize]
    }

    fn expr_to_z3(&self, expr: &ArithExpr) -> Int {
        let mut result = Int::from_big_int(&ibig_to_bigint(&expr.constant));
        for (var, coeff) in &expr.terms {
            let v = self.get_var(*var);
            result += Int::from_big_int(&ibig_to_bigint(coeff)) * v.clone();
        }
        for (a, b, coeff) in &expr.divs {
            let av = self.get_var(*a).clone();
            let bv = self.get_var(*b).clone();
            result += Int::from_big_int(&ibig_to_bigint(coeff)) * av.div(bv);
        }
        for (a, b, coeff) in &expr.mods {
            let av = self.get_var(*a).clone();
            let bv = self.get_var(*b).clone();
            result += Int::from_big_int(&ibig_to_bigint(coeff)) * av.modulo(bv);
        }
        result
    }

    fn constraint_to_z3(&self, c: &ArithConstraint) -> Bool {
        match c {
            ArithConstraint::Leq(l, r) => Int::le(&self.expr_to_z3(l), self.expr_to_z3(r)),
            ArithConstraint::Lt(l, r) => Int::lt(&self.expr_to_z3(l), self.expr_to_z3(r)),
            ArithConstraint::Eq(l, r) => Int::eq(&self.expr_to_z3(l), self.expr_to_z3(r)),
        }
    }

    /// Assert the definition of `var`, and of the vars it refers to, in the
    /// current level's scope unless a live scope already holds it.
    fn define(&mut self, var: VarId) {
        if self.defined[var as usize] {
            return;
        }
        self.defined[var as usize] = true;
        let rhs_expr = self.definitions[var as usize]
            .clone()
            .expect("z3incremental: only vars with definitions are undefined");
        self.define_expr(&rhs_expr);
        let rhs = self.expr_to_z3(&rhs_expr);
        self.solver.assert(Int::eq(self.get_var(var), rhs));
        self.top_level().vars.push(var);
        debug_println!(21, 0, "[z3inc] def var_{}", var);
    }

    fn define_expr(&mut self, expr: &ArithExpr) {
        for var in expr_vars(expr) {
            self.define(var);
        }
    }

    fn define_constraint(&mut self, c: &ArithConstraint) {
        let (ArithConstraint::Leq(l, r) | ArithConstraint::Lt(l, r) | ArithConstraint::Eq(l, r)) =
            c;
        self.define_expr(l);
        self.define_expr(r);
    }

    /// Queue `ast` for `lit`, pushed at the current level, until the next
    /// check or decision.
    fn queue(&mut self, lit: i32, ast: Bool) {
        let abs_lit = lit.abs();
        self.tracker_by_abs_lit
            .entry(abs_lit)
            .or_insert_with(|| Bool::new_const(format!("lit_{abs_lit}")));
        self.active_lits.insert(lit);
        self.top_level().lits.push(lit);
        self.queued.push((lit, ast));
        self.changed_since_check = true;
        self.pending_partial_assertions = self.pending_partial_assertions.saturating_add(1);
    }

    /// Assert the queued lits in the current level's scope, tracked so the
    /// unsat core recovers them.
    fn flush_queued(&mut self) {
        for (lit, ast) in std::mem::take(&mut self.queued) {
            let tracker = self.tracker_by_abs_lit[&lit.abs()].clone();
            self.solver.assert_and_track(ast, &tracker);
        }
    }

    /// A cumulative Z3 statistic. Z3 leaves a counter out until it is nonzero.
    fn z3_stat(&self, key: &str) -> u32 {
        match self.solver.get_statistics().value(key) {
            Some(z3::StatisticsValue::UInt(n)) => n,
            _ => 0,
        }
    }

    /// Assert the queued lits and check the tracked assertions;
    /// `assert_and_track` already makes Z3 assume the trackers of the scopes
    /// still open, so none are passed.
    fn check_active(&mut self, kind: &str) -> SatResult {
        self.flush_queued();
        self.changed_since_check = false;
        self.checks += 1;
        let result = self.solver.check();
        // Every Boolean Z3 sees is assigned by Sundance's trail, through the
        // trackers. A decision means Z3 searched on its own, which this
        // backend is meant to rule out.
        debug_assert_eq!(
            self.z3_stat("decisions"),
            0,
            "z3incremental: Z3 made decisions by {kind} check {}",
            self.checks
        );
        result
    }
}

impl Default for Z3IncrementalState {
    fn default() -> Self {
        Self::new()
    }
}

impl IncrementalArithSolver for Z3IncrementalState {
    fn register_var(&mut self, definition: Option<ArithExpr>, report_in_model: bool) -> VarId {
        let id = self.vars.len() as VarId;
        self.vars.push(Int::new_const(format!("var_{id}")));
        self.is_model_var.push(false);
        if report_in_model {
            self.mark_model_var(id);
        }
        self.defined.push(definition.is_none());
        self.definitions.push(definition);
        if self.definitions[id as usize].is_some() {
            self.define(id);
        }
        id
    }

    fn mark_model_var(&mut self, var: VarId) {
        if !self.is_model_var[var as usize] {
            self.is_model_var[var as usize] = true;
            self.model_vars.push(var);
        }
    }

    fn internalize_var(&mut self, var: VarId) {
        self.define(var);
        self.solver.internalize(self.get_var(var));
    }

    fn internalize_constraint(&mut self, constraint: &ArithConstraint) {
        self.define_constraint(constraint);
        self.solver.internalize(&self.constraint_to_z3(constraint));
    }

    /// Open the new level's scope. The lits queued at the level below are
    /// asserted first, so that they belong to its scope.
    fn notify_new_decision_level(&mut self) {
        self.flush_queued();
        self.solver.push();
        self.levels.push(Level::default());
    }

    /// Pop the scopes of the levels above `level`, and drop the lits queued
    /// at the current level, which is one of them.
    fn notify_backtrack(&mut self, level: usize) {
        if self.current_level() <= level {
            return;
        }
        self.queued.clear();
        self.changed_since_check = true;
        self.solver.pop((self.current_level() - level) as u32);
        for popped in self.levels.drain(level + 1..) {
            for lit in popped.lits {
                self.active_lits.remove(&lit);
            }
            for var in popped.vars {
                self.defined[var as usize] = false;
            }
        }
    }

    fn push_constraint(&mut self, constraint: ArithConstraint, lit: i32) {
        if self.active_lits.contains(&lit) {
            return;
        }
        self.define_constraint(&constraint);
        let ast = self.constraint_to_z3(&constraint);
        self.queue(lit, ast);
        debug_println!(
            21,
            0,
            "[z3inc] queued constraint lit={} at level {}",
            lit,
            self.current_level()
        );
    }

    fn push_equality(&mut self, a: VarId, b: VarId, lit: i32) {
        if self.active_lits.contains(&lit) {
            return;
        }
        self.define(a);
        self.define(b);
        let ast = Int::eq(self.get_var(a), self.get_var(b));
        self.queue(lit, ast);
        debug_println!(
            21,
            0,
            "[z3inc] queued equality var_{}==var_{} lit={} at level {}",
            a,
            b,
            lit,
            self.current_level()
        );
    }

    /// Check the tracked assertions. On SAT, bucket each model var by value.
    /// On UNSAT, recover the SAT lits from the unsat core.
    fn check(&mut self) -> ArithCheckResult {
        debug_println!(21, 0, "[z3inc] check() at level {}", self.current_level());
        // Every model var needs its definition before checking
        for var in self.model_vars.clone() {
            self.define(var);
        }
        self.pending_partial_assertions = 0;
        match self.check_active("final") {
            SatResult::Sat => {
                let model = self.solver.get_model().unwrap();
                let mut buckets: DeterministicHashMap<IBig, DeterministicHashSet<VarId>> =
                    DeterministicHashMap::new();
                for &var_id in &self.model_vars {
                    if let Some(val) = model.eval(self.get_var(var_id), true) {
                        let ibig = parse_z3_model_int(&val.to_string());
                        buckets.entry(ibig).or_default().insert(var_id);
                    }
                }
                debug_println!(21, 0, "[z3inc] SAT");
                ArithCheckResult::Sat(buckets)
            }
            SatResult::Unsat => ArithCheckResult::Unsat(self.unsat_core_clause()),
            SatResult::Unknown => panic!("z3incremental: Z3 returned unknown"),
        }
    }

    /// Check only the current tracked arithmetic trail, without constructing
    /// a model.
    fn check_partial_trail(&mut self) -> PartialCheckResult {
        // Nothing to learn from repeating the last query
        if !self.changed_since_check {
            return PartialCheckResult::Unchanged;
        }
        self.pending_partial_assertions = 0;
        debug_println!(
            21,
            0,
            "[z3inc] partial check at level {}",
            self.current_level()
        );
        match self.check_active("partial") {
            SatResult::Sat => PartialCheckResult::Sat,
            SatResult::Unsat => PartialCheckResult::Unsat(self.unsat_core_clause()),
            SatResult::Unknown => panic!("z3incremental: Z3 returned unknown"),
        }
    }
}
