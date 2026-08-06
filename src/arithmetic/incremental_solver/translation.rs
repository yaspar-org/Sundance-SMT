// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Translation layer between the egraph/solver-state world and the abstract
//! `IncrementalArithSolver` trait. Owns the bidirectional mapping between
//! egraph ids and solver VarIds.

use crate::arithmetic::incremental_solver::{
    ArithCheckResult, ArithConstraint, ArithExpr, IncrementalArithSolver, VarId,
};
use crate::arithmetic::lp::{ArithResult, Coefficient};
use crate::arithmetic::lia::stats::Stats as LiaStats;
use crate::egraphs::EgraphTrait;
use crate::solver_state::SolverState;
use crate::utils::{DeterministicHashMap, DeterministicHashSet};
use dashu::Integer;
use dashu::integer::IBig;
use yaspar_ir::ast::{
    ATerm::{self, App, Global, Not},
    Repr,
    alg::Constant as AlgConstant,
};

/// Bridges the propagator's egraph/term world and the abstract arithmetic solver.
pub struct ArithTranslator {
    pub solver: Box<dyn IncrementalArithSolver>,
    /// egraph_id -> VarId.
    egraph_to_var: DeterministicHashMap<u32, VarId>,
    /// VarId -> Some(solver_uid) for translating check results back.
    var_to_solver_uid: Vec<Option<u64>>,
    /// Per-level: egraph_ids registered at that level. Cleared on backtrack.
    vars_by_level: Vec<Vec<u32>>,
    /// Abs-lits known to be non-arithmetic.
    non_arithmetic_lits: DeterministicHashSet<i32>,
}

impl ArithTranslator {
    pub fn new(solver: Box<dyn IncrementalArithSolver>) -> Self {
        Self {
            solver,
            egraph_to_var: DeterministicHashMap::new(),
            var_to_solver_uid: Vec::new(),
            vars_by_level: vec![Vec::new()],
            non_arithmetic_lits: DeterministicHashSet::default(),
        }
    }

    /// Get or register a VarId for an egraph_id.
    pub fn get_or_register_var(
        &mut self,
        egraph_id: u32,
        decision_level: usize,
        solver_state: &mut SolverState,
    ) -> VarId {
        if let Some(&var_id) = self.egraph_to_var.get(&egraph_id) {
            return var_id;
        }
        let solver_uid = solver_state.to_solver_uid(egraph_id);
        let definition = self.build_var_definition(egraph_id, solver_state);
        let var_id = self.solver.register_var(definition, false);
        self.egraph_to_var.insert(egraph_id, var_id);
        while self.var_to_solver_uid.len() <= var_id as usize {
            self.var_to_solver_uid.push(None);
        }
        self.var_to_solver_uid[var_id as usize] = Some(solver_uid);
        while self.vars_by_level.len() <= decision_level {
            self.vars_by_level.push(Vec::new());
        }
        self.vars_by_level[decision_level].push(egraph_id);
        var_id
    }

    /// Build the RHS of a definitional equality for a var. None for free vars.
    fn build_var_definition(
        &mut self,
        egraph_id: u32,
        solver_state: &mut SolverState,
    ) -> Option<ArithExpr> {
        let solver_uid = solver_state.to_solver_uid(egraph_id);
        let expr_map = extract_lazy_expression(solver_uid, solver_state)?;
        let is_self_reference = expr_map.len() == 2
            && expr_map.get(&Coefficient::Constant) == Some(&IBig::from(0))
            && expr_map.get(&Coefficient::Term(egraph_id)) == Some(&IBig::from(1));
        if is_self_reference {
            return None;
        }
        Some(self.coeff_map_to_expr(&expr_map, solver_state))
    }

    /// Convert a Coefficient map to an ArithExpr, registering referenced vars.
    fn coeff_map_to_expr(
        &mut self,
        map: &DeterministicHashMap<Coefficient, Integer>,
        solver_state: &mut SolverState,
    ) -> ArithExpr {
        let mut terms = Vec::new();
        let mut constant = IBig::from(0);
        let mut divs = Vec::new();
        let mut mods = Vec::new();
        for (k, c) in map {
            match k {
                Coefficient::Constant => {
                    constant = c.clone();
                }
                Coefficient::Term(eid) => {
                    // Note: this may recursively register vars via get_or_register_var.
                    // We pass decision_level=0 for definition-time registrations since
                    // definitions are structural facts.
                    let var_id = self.get_or_register_var_internal(*eid, solver_state);
                    terms.push((var_id, c.clone()));
                }
                Coefficient::Div(a, b) => {
                    let va = self.get_or_register_var_internal(*a, solver_state);
                    let vb = self.get_or_register_var_internal(*b, solver_state);
                    divs.push((va, vb, c.clone()));
                }
                Coefficient::Mod(a, b) => {
                    let va = self.get_or_register_var_internal(*a, solver_state);
                    let vb = self.get_or_register_var_internal(*b, solver_state);
                    mods.push((va, vb, c.clone()));
                }
            }
        }
        ArithExpr {
            terms,
            constant,
            divs,
            mods,
        }
    }

    /// Internal helper — registers with report_in_model=false.
    fn get_or_register_var_internal(
        &mut self,
        egraph_id: u32,
        solver_state: &mut SolverState,
    ) -> VarId {
        self.register_var_impl(egraph_id, solver_state, false)
    }

    /// Register a var that should appear in model buckets on SAT.
    /// If already registered, upgrades it to model-reporting.
    fn get_or_register_model_var(
        &mut self,
        egraph_id: u32,
        solver_state: &mut SolverState,
    ) -> VarId {
        if let Some(&var_id) = self.egraph_to_var.get(&egraph_id) {
            self.solver.mark_model_var(var_id);
            return var_id;
        }
        self.register_var_impl(egraph_id, solver_state, true)
    }

    fn register_var_impl(
        &mut self,
        egraph_id: u32,
        solver_state: &mut SolverState,
        report_in_model: bool,
    ) -> VarId {
        if let Some(&var_id) = self.egraph_to_var.get(&egraph_id) {
            return var_id;
        }
        let solver_uid = solver_state.to_solver_uid(egraph_id);
        let definition = self.build_var_definition(egraph_id, solver_state);
        let var_id = self.solver.register_var(definition, report_in_model);
        self.egraph_to_var.insert(egraph_id, var_id);
        while self.var_to_solver_uid.len() <= var_id as usize {
            self.var_to_solver_uid.push(None);
        }
        self.var_to_solver_uid[var_id as usize] = Some(solver_uid);
        let level = self.vars_by_level.len().saturating_sub(1);
        self.vars_by_level[level].push(egraph_id);
        var_id
    }

    /// Extract an ArithConstraint from a SAT literal. None if not arithmetic.
    pub fn extract_constraint(
        &mut self,
        lit: i32,
        solver_state: &mut SolverState,
    ) -> Option<ArithConstraint> {
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
        let left_map = extract_lazy_expression(args[0].uid(), solver_state)?;
        let right_map = extract_lazy_expression(args[1].uid(), solver_state)?;
        let left = self.coeff_map_to_expr(&left_map, solver_state);
        let right = self.coeff_map_to_expr(&right_map, solver_state);
        let constraint = match (identifier.0.symbol.as_str(), polarity) {
            ("<=", true) => ArithConstraint::Leq(left, right),
            ("<=", false) => ArithConstraint::Lt(right, left),
            (">=", true) => ArithConstraint::Leq(right, left),
            (">=", false) => ArithConstraint::Lt(left, right),
            ("<", true) => ArithConstraint::Lt(left, right),
            ("<", false) => ArithConstraint::Leq(right, left),
            (">", true) => ArithConstraint::Lt(right, left),
            (">", false) => ArithConstraint::Leq(left, right),
            _ => return None,
        };
        Some(constraint)
    }

    /// Push a SAT literal into the solver if it's arithmetic.
    pub fn on_literal(&mut self, lit: i32, solver_state: &mut SolverState) {
        let abs_lit = lit.abs();
        if self.non_arithmetic_lits.contains(&abs_lit) {
            return;
        }
        let Some(constraint) = self.extract_constraint(lit, solver_state) else {
            self.non_arithmetic_lits.insert(abs_lit);
            return;
        };
        self.solver.push_constraint(constraint, lit);
    }

    /// Drain egraph merge queue and push equalities. Returns new SAT lits.
    pub fn drain_merges(&mut self, solver_state: &mut SolverState) -> Vec<i32> {
        let merges = solver_state.egraph.drain_arithmetic_equalities();
        if merges.is_empty() {
            return Vec::new();
        }
        let mut new_lits = Vec::new();
        for (a, b) in merges {
            let lit = solver_state.make_eq(a, b);
            let va = self.get_or_register_var_internal(a, solver_state);
            let vb = self.get_or_register_var_internal(b, solver_state);
            new_lits.push(lit);
            self.solver.push_equality(va, vb, lit);
        }
        new_lits
    }

    /// Register all arithmetic terms (with report_in_model=true), call check,
    /// and translate the result back.
    pub fn check(&mut self, solver_state: &mut SolverState) -> ArithResult {
        let arith_terms = solver_state.arithmetic_terms.clone();
        for term_id in &arith_terms {
            let egraph_id = solver_state.to_egraph_id(*term_id);
            let _ = self.get_or_register_model_var(egraph_id, solver_state);
        }
        let result = self.solver.check();
        self.translate_result(result, solver_state)
    }

    fn translate_result(
        &self,
        result: ArithCheckResult,
        solver_state: &SolverState,
    ) -> ArithResult {
        match result {
            ArithCheckResult::Unsat(lits) => ArithResult::Unsat(lits, LiaStats::new()),
            ArithCheckResult::Sat(buckets) => {
                let mut translated: DeterministicHashMap<IBig, DeterministicHashSet<u64>> =
                    DeterministicHashMap::new();
                for (value, var_ids) in buckets {
                    let mut set = DeterministicHashSet::default();
                    for var_id in var_ids {
                        if let Some(Some(solver_uid)) =
                            self.var_to_solver_uid.get(var_id as usize)
                        {
                            let egraph_id = solver_state.to_egraph_id(*solver_uid);
                            if solver_state.egraph.find(egraph_id) == egraph_id {
                                set.insert(*solver_uid);
                            }
                        }
                    }
                    if !set.is_empty() {
                        translated.insert(value, set);
                    }
                }
                ArithResult::Sat(translated, LiaStats::new())
            }
        }
    }

    /// Notify the solver of a new decision level.
    pub fn notify_new_decision_level(&mut self) {
        self.solver.notify_new_decision_level();
        self.vars_by_level.push(Vec::new());
    }

    /// Notify backtrack and evict vars registered at higher levels.
    pub fn notify_backtrack(&mut self, level: usize) {
        self.solver.notify_backtrack(level);
        while self.vars_by_level.len() > level + 1 {
            if let Some(egraph_ids) = self.vars_by_level.pop() {
                for eid in egraph_ids {
                    self.egraph_to_var.remove(&eid);
                }
            }
        }
    }
}

/// `find()`-free linear expression extractor. Returns a map of
/// Coefficient → IBig, or None if the term isn't arithmetic.
pub fn extract_lazy_expression(
    term_id: u64,
    solver_state: &mut SolverState,
) -> Option<DeterministicHashMap<Coefficient, Integer>> {
    let term = solver_state.get_term(term_id);
    let mut expr: DeterministicHashMap<Coefficient, Integer> = DeterministicHashMap::new();
    expr.insert(Coefficient::Constant, IBig::from(0));

    let opaque = |ss: &mut SolverState, expr: &mut DeterministicHashMap<Coefficient, Integer>| {
        expr.insert(Coefficient::Term(ss.to_egraph_id(term_id)), IBig::from(1));
    };
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
