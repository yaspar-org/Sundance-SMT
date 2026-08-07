// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Z3-based implementation of `IncrementalArithSolver`.

use crate::arithmetic::incremental_solver::{
    ArithCheckResult, ArithConstraint, ArithExpr, IncrementalArithSolver, VarId,
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

pub struct Z3IncrementalState {
    solver: Solver,
    /// VarId -> Z3 Int variable.
    vars: Vec<Int>,
    /// VarIds whose model values should be reported in check() SAT buckets.
    model_vars: Vec<VarId>,
    /// abs(lit) -> tracker Bool for `assert_and_track`.
    tracker_by_abs_lit: DeterministicHashMap<i32, Bool>,
    /// Signed lits currently in Z3's scope.
    active_lits: DeterministicHashSet<i32>,
    /// Per-level record of pushed lits.
    lits_by_level: Vec<Vec<i32>>,
    /// Per-level `z3::push` count.
    push_counts: Vec<u32>,
    /// VarIds registered per level. VarIds are never recycled, but this records
    /// which level a var was born at for bookkeeping.
    vars_by_level: Vec<Vec<VarId>>,
    /// Definitional asserts (`var_N == rhs`) recorded per level. A definition is
    /// a structural fact true at every level, but `solver.assert` lands it in the
    /// current push scope, so `notify_backtrack`'s `pop` would drop it. On
    /// backtrack we re-assert popped definitions at the surviving level so they
    /// persist for the whole solve.
    defs_by_level: Vec<Vec<Bool>>,
    current_level: usize,
}

impl Z3IncrementalState {
    pub fn new() -> Self {
        Self {
            solver: Solver::new(),
            vars: Vec::new(),
            model_vars: Vec::new(),
            tracker_by_abs_lit: DeterministicHashMap::new(),
            active_lits: DeterministicHashSet::default(),
            lits_by_level: vec![Vec::new()],
            push_counts: vec![0],
            vars_by_level: vec![Vec::new()],
            defs_by_level: vec![Vec::new()],
            current_level: 0,
        }
    }

    fn ensure_level_slot(&mut self) {
        while self.push_counts.len() <= self.current_level {
            self.push_counts.push(0);
        }
        while self.lits_by_level.len() <= self.current_level {
            self.lits_by_level.push(Vec::new());
        }
        while self.vars_by_level.len() <= self.current_level {
            self.vars_by_level.push(Vec::new());
        }
        while self.defs_by_level.len() <= self.current_level {
            self.defs_by_level.push(Vec::new());
        }
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

    fn get_or_create_tracker(&mut self, lit: i32) -> Bool {
        let abs_lit = lit.abs();
        self.tracker_by_abs_lit
            .entry(abs_lit)
            .or_insert_with(|| Bool::new_const(format!("lit_{abs_lit}")))
            .clone()
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
        let v = Int::new_const(format!("var_{id}"));
        self.vars.push(v.clone());
        self.ensure_level_slot();
        self.vars_by_level[self.current_level].push(id);

        if report_in_model {
            self.model_vars.push(id);
        }

        if let Some(rhs_expr) = definition {
            let rhs = self.expr_to_z3(&rhs_expr);
            let def = Int::eq(&v, rhs);
            self.solver.assert(&def);
            // Record so backtrack can re-assert it if its push scope is popped.
            self.defs_by_level[self.current_level].push(def);
            debug_println!(21, 0, "[z3inc] def var_{}", id);
        }
        id
    }

    fn mark_model_var(&mut self, var: VarId) {
        if !self.model_vars.contains(&var) {
            self.model_vars.push(var);
        }
    }

    fn notify_new_decision_level(&mut self) {
        self.current_level += 1;
        self.ensure_level_slot();
    }

    fn notify_backtrack(&mut self, level: usize) {
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
            // VarIds are never recycled. Each `var_N` constant is a distinct Z3
            // symbol whose definitional assert (`var_N == rhs`) is a structural
            // fact true at every level, so it is sound to keep across backtracks.
            // Popping `self.vars` here would let a later `register_var` reuse the
            // index `N` for a *different* term, colliding two contradictory
            // definitions on the same `var_N` and yielding a spurious empty-core
            // unsat, so `self.vars` is left intact.
            self.vars_by_level.pop();
            // The `solver.pop` above also discarded the definitional asserts made
            // at this level (they land in the current push scope). Re-assert them
            // at the surviving level so `var_N` keeps its definition — otherwise
            // the var becomes unconstrained and check() spuriously returns SAT.
            if let Some(defs) = self.defs_by_level.pop() {
                self.current_level -= 1;
                for def in defs {
                    self.solver.assert(&def);
                    self.defs_by_level[self.current_level].push(def);
                }
            } else {
                self.current_level -= 1;
            }
        }
        self.ensure_level_slot();
    }

    fn push_constraint(&mut self, constraint: ArithConstraint, lit: i32) {
        if self.active_lits.contains(&lit) {
            return;
        }
        let ast = self.constraint_to_z3(&constraint);
        let tracker = self.get_or_create_tracker(lit);
        self.ensure_level_slot();
        self.solver.push();
        self.push_counts[self.current_level] += 1;
        self.active_lits.insert(lit);
        self.lits_by_level[self.current_level].push(lit);
        self.solver.assert_and_track(ast, &tracker);
        debug_println!(
            21,
            0,
            "[z3inc] pushed constraint lit={} at level {}",
            lit,
            self.current_level
        );
    }

    fn push_equality(&mut self, a: VarId, b: VarId, lit: i32) {
        if self.active_lits.contains(&lit) {
            return;
        }
        let va = self.get_var(a).clone();
        let vb = self.get_var(b).clone();
        let ast = Int::eq(&va, vb);
        let tracker = self.get_or_create_tracker(lit);
        self.ensure_level_slot();
        self.solver.push();
        self.push_counts[self.current_level] += 1;
        self.active_lits.insert(lit);
        self.lits_by_level[self.current_level].push(lit);
        self.solver.assert_and_track(ast, &tracker);
        debug_println!(
            21,
            0,
            "[z3inc] pushed equality var_{}==var_{} lit={} at level {}",
            a,
            b,
            lit,
            self.current_level
        );
    }

    fn check(&mut self) -> ArithCheckResult {
        debug_println!(21, 0, "[z3inc] check() at level {}", self.current_level);
        let assumptions: Vec<Bool> = self
            .active_lits
            .iter()
            .filter_map(|lit| self.tracker_by_abs_lit.get(&lit.abs()).cloned())
            .collect();
        match self.solver.check_assumptions(&assumptions) {
            SatResult::Sat => {
                let model = self.solver.get_model().unwrap();
                let mut buckets: DeterministicHashMap<IBig, DeterministicHashSet<VarId>> =
                    DeterministicHashMap::new();
                for &var_id in &self.model_vars {
                    if let Some(v) = self.vars.get(var_id as usize)
                        && let Some(val) = model.eval(v, true) {
                            let ibig = parse_z3_model_int(&val.to_string());
                            buckets.entry(ibig).or_default().insert(var_id);
                        }
                }
                debug_println!(21, 0, "[z3inc] SAT");
                ArithCheckResult::Sat(buckets)
            }
            SatResult::Unsat => {
                let core = self.solver.get_unsat_core();
                let lits: Vec<i32> = core
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
                assert!(
                    !lits.is_empty(),
                    "z3incremental: empty unsat core (definitions alone are contradictory)"
                );
                ArithCheckResult::Unsat(lits)
            }
            SatResult::Unknown => panic!("z3incremental: Z3 returned unknown"),
        }
    }
}
