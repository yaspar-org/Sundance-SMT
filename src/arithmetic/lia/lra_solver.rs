// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Linear rational arithmetic solver
//!
//! The main object here is the [LRASolver] which manages solver state, implements
//! the rational solver methods and contains data like variable info and an underlying
//! tableau representing a linear system.

use log;
use std::collections::BTreeMap;
use std::fmt;

use crate::arithmetic::lia::bounds::Bounds;
use crate::arithmetic::lia::context::ConvContext;
use crate::arithmetic::lia::qdelta::QDelta;
use crate::arithmetic::lia::solver_result::{
    Assignment, Conflict, SolverDecision, SolverError, SolverResult,
};
use crate::arithmetic::lia::tableau::Tableau;
use crate::arithmetic::lia::tableau_dense::TableauDense;
use crate::arithmetic::lia::types::Rational;
use crate::arithmetic::lia::variables::{Owner, Var, VarInfo};
use dashu::base::{Abs, Inverse};

/// Linear arithmetic solver state
///
/// TODO: not clear if solver state is useful at this point
#[derive(Debug)]
enum LRASolverState {
    /// system satisfiability is currently unknown (default state upon init)
    Unknown,
    /// solver has concluded SAT
    Sat,
    /// solver has concluded UNSAT
    Unsat,
}

/// Intermediate simplex result
#[derive(Debug)]
enum SimplexStepResult {
    /// Simplex problem is feasible
    Feasible,
    /// Simplex problem is infeasible; conflict occurs because of the given variable
    Infeasible(Var),
    /// Simplex problem status is still unknown
    Unknown,
}

/// Linear real arithmetic solver
pub struct LRASolver<T: Tableau + fmt::Debug> {
    /// Variable info for all original and slack variables. The vector itself should be immutable,
    /// but VarInfo pointed to are mutated during solving.
    ///
    /// Ordering of this vector determines the overall fixed variable order used for example
    /// in Bland's selection rule.
    variables: Vec<VarInfo<QDelta>>,
    /// Basic variables: a mapping from row -> index in self.variables
    basic: Vec<usize>,
    /// Non-basic variables: a mapping from column -> index in self.variables
    non_basic: Vec<usize>,
    /// Low-level tableau representing equations b/w basic and non-basic variables. The tableau has
    /// rows and columns corresponding to the basic and non-basic variable vectors, not in the
    /// fixed variable order.
    tableau: T,

    // -- Non-variable solver state --
    /// Solver decision state
    state: LRASolverState,
    /// old asserted lower bounds and the level they were asserted at
    old_lower_bounds: Vec<(
        /* var */ Var,
        /* bound, None = -inf */ Option<QDelta>,
        /* bt level */ usize,
    )>,
    /// old asserted upper bounds and the level they were asserted at
    old_upper_bounds: Vec<(
        /* var */ Var,
        /* bound, None = +inf */ Option<QDelta>,
        /* bt level */ usize,
    )>,
    /// backtracking level
    backtrack_level: usize,
    /// backup copy of the solver's assignment at some backtracking point
    old_assignment: Option<BTreeMap<Var, QDelta>>,

    // -- Mappings for bookkeeping --
    /// mapping from Var to index in `self.variables`
    var_to_idx: BTreeMap<Var, usize>,
    /// Conversion context from the frontend including the name <-> Var mapping
    ctx: ConvContext,
}

impl<T> fmt::Debug for LRASolver<T>
where
    T: Tableau + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = String::new();
        s.push_str("Variables:\n  [\n");
        for v in self.variables.iter() {
            let name = self.ctx.get_name(v.var).unwrap_or("None");
            s.push_str(&format!("    {v} (name: {name}),\n"));
        }
        s.push_str("  ]\n");
        s.push_str(&format!("Basic pointers:\n  {0:?}\n", self.basic));
        s.push_str(&format!("Non-Basic pointers:\n  {0:?}\n", self.non_basic));
        s.push_str(&format!("Tableau:\n  {0:?}\n", self.tableau));
        s.push_str(&format!("State: {:?}\n", self.state));
        // TODO: add the rest of the solver state, including backtracking info
        write!(f, "{}", s)
    }
}

/// Shared functionality among all concrete instances of LRASolver
impl<T: Tableau> LRASolver<T> {
    /// Perform a low-level swap of variable info between a basic and a non-basic variable.
    ///
    /// - `row` is the tableau row owned by the basic variable
    /// - `col` is the tableau col owned by the non-basic variable
    fn swap(&mut self, row: usize, col: usize) {
        // Swap ownership of row/col
        self.variables[self.basic[row]].owner = Owner::NonBasic(col);
        self.variables[self.non_basic[col]].owner = Owner::Basic(row);
        // at the end, we've maintained the invariant that self.basic (self.non_basic resp.)
        // point to variables in row (column resp.) order
        //
        // e.g. if
        //
        // variables = [var(4, NB(0)), var(5, NB(1)), var(1, B(0)), var(2, B(1)), var(3, B(2))]
        // basic = [2, 3, 4]
        // non_basic = [0, 1]
        //
        // step 1: var(1, B(0)) is below lower bound
        //   pivot_and_update(0, 0, ..)
        //     swap: - update owners [var(4, B(0)), var(5, NB(1)), var(1, NB(0)), var(2, B(1)), var(3, B(2))]
        //           - mem swap basic[row], non_basic[col]
        //             basic = [0, 3, 4]
        //             non_basic = [2, 1]
        //
        std::mem::swap(&mut self.basic[row], &mut self.non_basic[col]);
    }

    /// Update a non-basic variable assignment and adjust basic variable assignments to maintain the tableau equations
    ///
    /// Given x_j in N:
    ///
    /// for x_i in B \ {skip}, assign(x_i) <- assign(x_i) + a_j_i * (val - assign(x_j))
    /// assign(x_j) <- val
    ///
    /// This a low-level operation which may break the non-basic variable bounds invariant.
    ///
    /// Note that no loop over the tableau columns is required.
    pub fn update(&mut self, col: usize, val: &QDelta) {
        let adjustment = val - &self.variables[self.non_basic[col]].val;
        for (row, basic_idx) in self.basic.iter().enumerate() {
            let a_j_i = self.tableau.get(row, col).unwrap();
            let new_val = self.variables[*basic_idx].val.clone() + &adjustment * a_j_i;
            self.variables[*basic_idx].update_assignment(new_val);
        }
        self.variables[self.non_basic[col]].update_assignment(val.clone());
    }

    /// Pivot a basic/non-basic variable pair and update original basic (after non-basic) variable
    /// assignment as well as all the other basic variable assignments so that the tableau
    /// equations are satisfied.
    ///
    /// This procedure maintains the tableau equation invariant but may break the non-basic
    /// variable bounds invariant, so `val` must be chosen correctly by the caller.
    ///
    /// Parameters:
    /// - pivot_row: tableau row / basic variable to pivot
    /// - pivot_col: tableau column / non-basic variable to pivot
    /// - val: value to assign the new non-basic variable (basics are all updated correspondingly
    ///   according to the tableau)
    pub fn pivot_and_update(
        &mut self,
        pivot_row: usize,
        pivot_col: usize,
        val: &QDelta,
    ) -> SolverResult<()> {
        log::debug!(
            "  pivot_and_update row={}, col={}, val={}",
            pivot_row,
            pivot_col,
            val
        );
        let a_row_col_inv = self.tableau.get(pivot_row, pivot_col).unwrap().inv();
        let non_basic_adjustment =
            (val - &self.variables[self.basic[pivot_row]].val) * &a_row_col_inv; // "theta"

        // Update basic var assignment
        self.variables[self.basic[pivot_row]].update_assignment(val.clone());

        // Update non-basic var assignment and re-compute all basic variable assignments except for
        // the one corresponding to `basic_index`
        let new_non_basic_val =
            &self.variables[self.non_basic[pivot_col]].val + &non_basic_adjustment; // assign(x_j) + theta

        self.variables[self.non_basic[pivot_col]].update_assignment(new_non_basic_val);

        for (row, basic_idx) in self.basic.iter().enumerate() {
            if row != pivot_row {
                let a_i_col = self.tableau.get(row, pivot_col)?;
                // TODO: a lot of this variable reference arithmetic is awkward
                let new_val = &self.variables[*basic_idx].val + &(&non_basic_adjustment * a_i_col);
                self.variables[*basic_idx].update_assignment(new_val);
            }
        }

        // Pivot the tableau
        //
        // Note: low-level pivot will panic if (row, col) are out of bounds but by construction
        // they will be in-bounds if there are no construction bugs.
        self.tableau.pivot(pivot_row, pivot_col)?;

        // swap variable row/col owner info
        self.swap(pivot_row, pivot_col);
        Ok(())
    }

    /// Assert a new lower bound for `x`
    ///
    /// Three possible returns:
    /// - Some(false): the new bound conflicts with current bounds, i.e. U(x) < l
    /// - Some(true): the new bound is consistent with existing bounds and the current assignment
    ///   to `x` satisfies it
    /// - None: the new bound is consistent with existing bounds, but satisfiability of the new
    ///   system is unknown
    ///
    /// TODO: assert_lower: check at all call sites whether l is constructed new or cloned and then a ref passed
    /// in here
    pub fn assert_lower(&mut self, x: &Var, l: &QDelta) -> SolverResult<Option<bool>> {
        let idx = self
            .var_to_idx
            .get(x)
            .ok_or(SolverError(format!("variable {0:?} does not exist", x)))?;
        let v = &mut self.variables[*idx];
        log::debug!(
            "assert_lower on variable {0:?}, lower={1}, non_basic?={2}",
            v,
            l,
            v.is_non_basic().is_some()
        );

        let bs = &v.bounds;
        if bs.above_upper(l) {
            // new lower bound is inconsistent with current upper bound
            log::debug!("assert_lower: trivially inconsistent");
            return Ok(Some(false));
        } else if bs.above_lower(l) {
            // `l` is a tighter lower bound
            log::debug!("assert_lower: new lower bound is an improvement");
            self.old_lower_bounds
                .push((v.var, v.bounds.lower.clone(), self.backtrack_level));
            v.update_lower(l.clone());
            log::debug!("assert_lower: new variable state: {v}");
        }
        // Note: in this check, l can be infinitesimally (in the QDelta sense) less or
        // equal to v.val
        if *l <= v.val {
            log::debug!("assert_lower: current assignment satisfies new lower bound");
            return Ok(Some(true));
        }
        // if v.val is now outside the new lower bound, and v is a non-basic variable,
        // update v.val and adjust the basic variable values to maintain the tableau
        // invariant
        if let Some(col) = v.is_non_basic() {
            log::debug!("assert_lower: updating tableaux");
            self.update(col, l);
        }
        Ok(None)
    }

    /// Assert a new upper bound for `x`
    ///
    /// Three possible returns:
    /// - Some(false): the new bound conflicts with current bounds, i.e. u < L(x)
    /// - Some(true): the new bound is consistent with existing bounds and the current assignment
    ///   to `x` satisfies it
    /// - None: the new bound is consistent with existing bounds, but satisfiability of the new
    ///   system is unknown
    pub fn assert_upper(&mut self, x: &Var, u: &QDelta) -> SolverResult<Option<bool>> {
        let idx = self
            .var_to_idx
            .get(x)
            .ok_or(SolverError(format!("variable {0:?} does not exist", x)))?;
        let v = &mut self.variables[*idx];
        log::debug!(
            "assert_upper on variable {0:?}, upper={1}, non_basic?={2}",
            v,
            u,
            v.is_non_basic().is_some()
        );

        let bs = &v.bounds;
        if bs.below_lower(u) {
            // new lower bound is inconsistent with current upper bound
            return Ok(Some(false));
        } else if bs.below_upper(u) {
            // `u` is a tighter upper bound
            self.old_upper_bounds
                .push((v.var, v.bounds.upper.clone(), self.backtrack_level));
            v.update_upper(u.clone());
        }
        // Note: in this check, v.val can be infinitesimally greater or equal to u
        if v.val <= *u {
            return Ok(Some(true));
        }
        // if v.val is now above the new upper bound, and v is a non-basic variable,
        // update v.val and adjust the basic variable values to maintain the tableau
        // invariant
        if let Some(col) = v.is_non_basic() {
            self.update(col, u);
        }
        Ok(None)
    }

    /// Backup the current assignment for use in backtracking
    ///
    /// panic if the solver state is not SAT | UNKNOWN
    fn backup_assignment(&mut self) {
        let model = self
            .get_qdelta_model()
            .expect("cannot backup assignment: solver state is not SAT | UNKNOWN");
        self.old_assignment = Some(model);
    }

    /// Restore a previous assignment when backtracking
    fn restore_assignment(&mut self) {
        let previous_model = self
            .old_assignment
            .as_ref()
            .expect("cannot restore assignment: no previous assignment exists");
        for (var, ass) in previous_model.iter() {
            let var_info_idx = self.var_to_idx.get(var).unwrap(); // if var isn't a key, it's is a bug
            self.variables[*var_info_idx].val = ass.clone();
        }
    }

    /// Set a backtrack point and return the new backtrack level
    ///
    /// Calling `let level = self.backtrack(); ...; self.backtrack(level)` restores the
    /// solver to it's prior state.
    ///
    /// If the solver state is UNSAT, this does nothing. Otherwise it increases
    /// the backtrack level, makes a backup of the current assignment, and returns the
    /// new backtrack level.
    pub fn set_backtrack(&mut self) -> usize {
        if matches!(self.state, LRASolverState::Unsat) {
            return self.backtrack_level;
        }
        let old_level = self.backtrack_level;
        self.backtrack_level += 1;
        self.backup_assignment();
        old_level
    }

    /// Backtrack asserted upper/lower bounds to a previous level
    pub fn backtrack(&mut self, level: usize) {
        if level >= self.backtrack_level {
            return;
        }
        while let Some((var, bound, _)) = self.old_lower_bounds.pop_if(|(_, _, l)| *l > level) {
            let var_info_idx = self.var_to_idx.get(&var).unwrap();
            self.variables[*var_info_idx].bounds.lower = bound;
        }
        while let Some((var, bound, _)) = self.old_upper_bounds.pop_if(|(_, _, l)| *l > level) {
            let var_info_idx = self.var_to_idx.get(&var).unwrap();
            self.variables[*var_info_idx].bounds.upper = bound;
        }
        self.restore_assignment();
    }

    /// If the solver is in a SAT state, Get the current assignment of variables to QDelta
    /// values
    //
    pub fn get_qdelta_model(&self) -> Option<BTreeMap<Var, QDelta>> {
        if matches!(self.state, LRASolverState::Sat | LRASolverState::Unknown) {
            let mut assg = BTreeMap::new();
            for v in self.variables.iter() {
                assg.insert(v.var, v.val.clone());
            }
            return Some(assg);
        }
        None
    }

    /// If the solver is in a SAT state, Get the current assignment of variables to Rational
    /// values
    //
    // TODO: add model validation
    pub fn get_rational_model(&self) -> Option<BTreeMap<Var, Rational>> {
        if matches!(self.state, LRASolverState::Sat | LRASolverState::Unknown) {
            let mut model = BTreeMap::new();
            let d0 = self.calculate_d0();
            // instantiate δ <- δ_0 in all variable assignments
            for v in self.variables.iter() {
                model.insert(v.var, v.val.instantiate(&d0));
            }
            return Some(model);
        }
        None
    }

    /// Convert the current assignment to an Assignment
    pub fn compute_assignment(&self) -> Assignment<Var> {
        let d0 = self.calculate_d0();
        let mut assignments = BTreeMap::new();
        for v in self.variables.iter() {
            let new_val = v.val.instantiate(&d0);
            assignments.insert(v.var, new_val);
        }
        Assignment::new(assignments)
    }

    /// Calculate a currently valid value for δ_0, a rational instantiation of
    /// the infinitesimal δ that may be part of the current variable assignment.
    ///
    /// δ_0 is used in converting a feasible assignment over Q_δ to an assignment over Q.
    ///
    /// ```text
    /// Variables w/ bounds w/ non-zero delta had strict bounds originally and
    /// were re-written to
    ///
    ///   l_i + δ <= x_i <= u_i - δ, where now x_i is an element in Q_δ.
    ///
    /// So, if the solver has concluded that
    ///
    ///   l_i + δ <= x_i^rat + x_i^inf δ
    ///
    /// then we want to find a positive rational value for δ_0 such that
    ///
    ///   l_i + δ_0 < x_i^rat + x_i^inf δ_0
    ///
    /// The minimum of these over all i will then satisfy all constraints.
    ///
    /// ex/      1 + δ <= x + y δ <= 2 - δ
    ///
    ///      Lower bound:
    ///
    ///      --> 0 <= (x + (-1)) +     (y - 1) δ and
    ///        --> if (x + (-1)) = 0, then (y - 1) >= 0
    ///            choose any δ_0: 0 < δ_0 to obtain 0 < (x + (-1)) + (y - 1) δ_0
    ///        --> if 0 < (x + (-1)), then we need to have |(y - 1) δ| < (x + (-1))
    ///            choose any δ_0: 0 < δ_0 <= (x + (-1)) / |2*(y - 1)|
    ///
    ///     Note in the last case, if y = 1, then any δ satisfies |(y - 1) δ| < (x + (-1)).
    ///
    ///      Upper bound:
    ///
    ///      --> 0 <= (2 + (-x)) + (-1 + (-y)) δ
    ///        --> if (2 + (-x)) = 0, then we know 0 <= (-1 + (-y))
    ///            choose any δ_0: 0 < δ_0
    ///        --> if 0 < (2 + (-x)), then we need to have 0 <= |(-1 + (-y))| δ < (2 + (-x))
    ///            choose any δ_0: 0 < δ_0 <= (2 + (-x)) / |2*(-1 + (-y))|
    ///
    /// On the other hand, if a bound is purely rational (i.e. non-strict in the original system),
    /// but the assigned value is not, we must ensure that instantiating δ_0 doesn't cause the
    /// assigned value to stray outside the inclusive bounds.
    ///
    ///   l_i <= x_i^rat + x_i^inf δ_0
    ///   0 <= (x_i^rat - l_i) + x_i^inf δ_0
    ///
    /// If x_i^rat = l_i but x_i^inf < 0 the Q_δ inequality would be violated, so WLOG x_i^rat -
    /// l_i > 0. If x_i^inf > 0 there is no constraint on δ_0 and finally if it's < 0 we can
    /// choose:
    ///
    ///   δ_0 <= (l_i - x_i^rat) / abs(x_i^inf)
    ///
    /// The upper bound case is similar.
    /// ```text
    ///
    /// TODO: move compute_assignment out of the solver?
    fn calculate_d0(&self) -> Rational {
        let mut delta_ub: Vec<Rational> = Vec::new(); // set of positive upper bounds for δ_0
        for v in self.variables.iter() {
            // for each definite lower bound:
            if let Some(l) = v.bounds.lower.as_ref() {
                if !(l.inf().is_zero())
                    && l.rat() < v.val.rat()
                    && !(v.val.inf() - Rational::ONE).is_zero()
                {
                    // original lower bound was strict and the Q_δ assignment for v has rational part
                    // strictly above the original lower bound
                    let d0 = (v.val.rat() - l.rat())
                        / (Rational::from(2) * (v.val.inf() - Rational::ONE).abs());
                    log::debug!("d0 for var {} is {}", v, d0);
                    delta_ub.push(d0);
                } else if l.inf().is_zero() && v.val.inf() < &Rational::ZERO {
                    // lower bound is non-strict, but assigned value is infinitesimally smaller
                    // than some rational value
                    let d0 = (l.rat() - v.val.rat()) / v.val.inf().clone().abs();
                    delta_ub.push(d0);
                }
            }
            // for each definite upper bound:
            if let Some(u) = v.bounds.upper.as_ref() {
                if !(u.inf().is_zero())
                    && v.val.rat() < u.rat()
                    && !(Rational::ONE + v.val.inf()).is_zero()
                {
                    // original upper bound was strict and the Q_δ assignment for v has rational part
                    // strictly below the original upper bound
                    let d0 = (u.rat() - v.val.rat())
                        / (Rational::from(2) * (Rational::ONE + v.val.inf()).abs());
                    log::debug!("d0 for var {} is {}", v, d0);
                    delta_ub.push(d0);
                } else if u.inf().is_zero() && v.val.inf() > &Rational::ZERO {
                    // upper bound is non-strict, but assigned value is infinitesimally greater
                    // than some rational value
                    let d0 = (u.rat() - v.val.rat()) / v.val.inf().clone();
                    delta_ub.push(d0);
                }
            }
        }
        let d0 = delta_ub.into_iter().min().unwrap_or(Rational::ONE); // choose δ_0 = 1 if there are no positive upper bounds
        log::debug!("δ_0 = {d0}");
        d0
    }

    /// Perform one simplex step on self.
    ///
    /// Roughly, find the first (in order) basic variable that doesn't satisfy its
    /// bounds. If none, we're done and the current assignment is SAT. Otherwise,
    /// find the first non-basic variable that can bring the basic into its bounds
    /// range and make the adjustment, pivoting the two variables in the process.
    /// Otherwise, the system of inequalities is UNSAT.
    ///
    /// TODO: simplify step_simplex
    fn step_simplex(&mut self) -> SolverResult<SimplexStepResult> {
        // TODO: step_simplex: Use the violated-variable priority queue technique
        // TODO: step_simplex: The way the variable loops are setup here implicitly implements
        //   Bland's selection rule. The SPASS-SATT heuristic perform much better on SMT-LIB
        //   benchmarks however, and should not be hard to add here.
        //
        //   SPASS-SATT heuristic: perform greedy pivots for violated basic variables up to some number of iterations,
        //     e.g. #iterations = #(basic variables).
        //   1. (greedy) For basic variables, prefer smallest one violated in the fixed variable order.
        //     For non-basic variables, prefer unbounded first, then vars w/ smallest # of non-zero
        //     coefficients in the tableau, finally by smallest in the order.
        //   2. Switch to Bland's rule
        //
        for var in self.variables.iter() {
            log::debug!("CONSIDER {}", var);
            let row = match var.is_basic() {
                Some(r) => r,
                None => continue,
            };

            // three cases in order:
            // 1. v is already in bounds
            // 2. v.val is less than the lower bound
            // 3. v.val is greater than the upper bound
            if var.in_bounds() {
                log::debug!("basic var (row {}) is in bounds: {}", row, var,);
                continue;
            } else if var.below_lower() {
                log::debug!("basic var (row {}) is below its lower bound: {}", row, var,);

                // TODO: factor out loop code and simpler helper functions
                // Try to increase basic_var's assignment to its lower bound
                for (col, non_basic_idx) in self.non_basic.iter().enumerate() {
                    let non_basic_var = &self.variables[*non_basic_idx];
                    let a_i_j = self.tableau.get(row, col).unwrap();
                    if (a_i_j > &Rational::ZERO && !non_basic_var.at_upper())
                        || (a_i_j < &Rational::ZERO && !non_basic_var.at_lower())
                    {
                        // unwrap is safe because basic_var is below its lower bound
                        let basic_lower_bound = var.bounds.lower.as_ref().unwrap().clone();
                        log::debug!(
                            "pivot basic (row {}) {} and non-basic (col {}) {}, update non-basic val to {}",
                            row,
                            var,
                            col,
                            self.variables[self.non_basic[col]],
                            basic_lower_bound
                        );
                        self.pivot_and_update(row, col, &basic_lower_bound)?;
                        return Ok(SimplexStepResult::Unknown);
                    }
                }
                // if no suitable non-basic variable is found, the system is infeasible
                self.state = LRASolverState::Unsat;
                return Ok(SimplexStepResult::Infeasible(var.var));
            } else {
                log::debug!("basic var (row {}) is above its upper bound: {}", row, var);
                debug_assert!(var.bounds.upper.is_some() && var.above_upper());
                // Try to decrease basic_var's assignment to its upper bound
                for (col, non_basic_idx) in self.non_basic.iter().enumerate() {
                    let non_basic_var = &self.variables[*non_basic_idx];
                    let a_i_j = self.tableau.get(row, col).unwrap();
                    // this condition is dual to the one above
                    if (a_i_j > &Rational::ZERO && !non_basic_var.at_lower())
                        || (a_i_j < &Rational::ZERO && !non_basic_var.at_upper())
                    {
                        // unwrap is safe because basic_var is above its upper bound
                        let basic_upper_bound = var.bounds.upper.as_ref().unwrap().clone();
                        // pivot basic_var and non_basic_var, update assignment of
                        // (previously) basic_var to its lower bound and then adjust all
                        // basic assignments so the equations hold
                        log::debug!(
                            "pivot basic (row {}) {} and non-basic (col {}) {}, update non-basic val to {}",
                            row,
                            var,
                            col,
                            self.variables[self.non_basic[col]],
                            basic_upper_bound
                        );
                        self.pivot_and_update(row, col, &basic_upper_bound)?;
                        return Ok(SimplexStepResult::Unknown);
                    }
                }
                self.state = LRASolverState::Unsat;
                return Ok(SimplexStepResult::Infeasible(var.var));
            }
        }
        // No more pivots are required, so the system is feasible.
        self.state = LRASolverState::Sat;
        Ok(SimplexStepResult::Feasible)
    }

    /// Perform the general simplex algorithm to find a feasible solution.
    ///
    /// TODO: add configuration options for termination
    pub fn solve(&mut self) -> SolverResult<SolverDecision> {
        let mut i: usize = 0;
        loop {
            log::debug!("Stepping simplex, iteration {}", i);
            match self.step_simplex() {
                Ok(SimplexStepResult::Unknown) => {
                    i += 1;
                }
                Ok(SimplexStepResult::Feasible) => {
                    let assg = self.compute_assignment();
                    return Ok(SolverDecision::FEASIBLE(assg));
                }
                Ok(SimplexStepResult::Infeasible(v)) => {
                    let conflict = self.compute_conflict(v)?;
                    return Ok(SolverDecision::INFEASIBLE(conflict));
                }
                Err(e) => return Err(e), // error
            }
        }
    }

    /// If the solver is in an INFEASIBLE state, return a set of literals
    /// that implies the conflict.
    ///
    /// The conflict produced is guaranteed to be minimal by Farkas' Lemma.
    pub fn compute_conflict(&self, var: Var) -> SolverResult<Conflict<Var>> {
        // TODO: get_conflict: implement
        let var_info = &self.variables[*self.var_to_idx.get(&var).unwrap()];
        let row = match var_info.is_basic() {
            Some(r) => r,
            None => {
                return Err(SolverError(
                    "compute_conflict: expected basic variable".to_string(),
                ));
            }
        };
        if var_info.below_lower() || var_info.above_upper() {
            let mut conflicts = vec![var_info.var];
            for (col, non_basic_idx) in self.non_basic.iter().enumerate() {
                let a_i_j = self.tableau.get(row, col).unwrap();
                if a_i_j != &Rational::ZERO {
                    let non_basic_var = &self.variables[*non_basic_idx];
                    conflicts.push(non_basic_var.var);
                }
            }
            Ok(conflicts.into_iter().collect())
        } else {
            Err(SolverError(
                "compute_conflict: expected basic variable that violates its bounds".to_string(),
            ))
        }
    }

    /// Check the two tableau invariants
    pub fn is_valid(&self) -> bool {
        self.assert_basic_assignments() && self.assert_non_basic_in_bounds()
    }

    /// Return the name associated with a given Variable
    pub fn get_name(&self, var: Var) -> Option<String> {
        self.ctx.get_name(var).map(|name| name.to_owned())
    }

    /// Get the currently assigned bounds for a variable
    pub fn get_bounds(&self, var: &Var) -> Option<Bounds<QDelta>> {
        self.var_to_idx
            .get(var)
            .map(|i| self.variables[*i].bounds.clone())
    }

    /// Return the [Var]iable associated with a given name
    pub fn get_var(&self, name: &str) -> Option<Var> {
        self.ctx.get_var(name).map(|var| var.to_owned())
    }

    // -------------------------------------------------------------
    // Helper methods for testing the internal state of an LRASolver

    /// Calculate the assignment to a basic variable at `row` required in order to make its
    /// corresponding row equation true.
    #[allow(dead_code)]
    fn calculate_assignment(&self, row: usize) -> QDelta {
        let mut rhs = QDelta::ZERO;
        for (col, non_basic_idx) in self.non_basic.iter().enumerate() {
            // TODO: getting the whole row at once may be faster here
            rhs = rhs + &self.variables[*non_basic_idx].val * self.tableau.get(row, col).unwrap();
        }
        rhs
    }

    /// Determine if the current basic variables assignments satisfy the tableau invariant
    #[allow(dead_code)]
    fn assert_basic_assignments(&self) -> bool {
        self.basic
            .iter()
            .enumerate()
            .all(|(row, idx)| self.variables[*idx].val == self.calculate_assignment(row))
    }

    /// Determine if the current **non-basic** variable assignments satisfy their bounds
    #[allow(dead_code)]
    fn assert_non_basic_in_bounds(&self) -> bool {
        self.non_basic
            .iter()
            .all(|idx| self.variables[*idx].in_bounds())
    }

    /// Determine if the current **basic** variable assignments satisfy their bounds
    #[allow(dead_code)]
    fn assert_basic_in_bounds(&self) -> bool {
        self.basic
            .iter()
            .all(|idx| self.variables[*idx].in_bounds())
    }
}

impl LRASolver<TableauDense> {
    /// Construct a new high-level tableau from:
    ///
    /// - basic variables, given in row order
    /// - non-basic variables, given in column order
    /// - equations: a vector of vectors that represent coefficients in equations of the form
    ///
    /// row i:
    /// basic_var_i = a_i_1 * non_basic_var_1 + a_i_2 * non_basic_var_2 + ... + a_i_n * non_basic_var_n
    pub fn from_eqs(
        basic_info: Vec<VarInfo<QDelta>>,
        non_basic_info: Vec<VarInfo<QDelta>>,
        equations: Vec<Vec<Rational>>,
        ctx: ConvContext,
    ) -> SolverResult<Self> {
        let ncols = non_basic_info.len();
        let nrows = basic_info.len();
        // validate the inputs
        if basic_info.is_empty() {
            return Err(SolverError(
                "Expected at least one basic variable".to_string(),
            ));
        }
        if nrows != equations.len() {
            return Err(SolverError(format!(
                "Expected {} equations, but got {}",
                nrows,
                equations.len()
            )));
        }
        log::debug!("LRASolver::from_eqs: nrows = {}", nrows);
        // at this point: nrows == equations.len() > 0
        if equations[0].len() != ncols {
            return Err(SolverError(format!(
                "Expected {} non-basic variables, but got {}",
                equations[0].len(),
                ncols,
            )));
        }
        log::debug!("LRASolver::from_eqs: non_basic.len() = {}", ncols);

        // Arrange non-basic (original) variables first, followed by basic (slack) variables
        let mut var_to_idx = BTreeMap::new();
        for (i, v) in non_basic_info.iter().enumerate() {
            var_to_idx.insert(v.var, i); // intended to be immutable during solving
        }
        for (i, v) in basic_info.iter().enumerate() {
            var_to_idx.insert(v.var, ncols + i);
        }
        let mut variables = Vec::with_capacity(nrows + ncols);
        variables.extend(non_basic_info);
        variables.extend(basic_info);

        // initial indices into `variables`
        // e.g. col 0 variable <=> variables[non_basic[0]]
        let non_basic: Vec<usize> = (0..ncols).collect();
        let basic: Vec<usize> = (ncols..ncols + nrows).collect();

        Ok(Self {
            variables,
            basic,
            non_basic,
            tableau: TableauDense::from_rows(&equations)?,
            state: LRASolverState::Unknown,
            old_lower_bounds: vec![],
            old_upper_bounds: vec![],
            backtrack_level: 0,
            old_assignment: None,
            var_to_idx,
            ctx,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arithmetic::lia::bounds::Bounds;
    use crate::arithmetic::lia::context::ConvContext;
    use crate::arithmetic::lia::variables::{Var, VarInfo};
    use dashu::rbig;
    use env_logger;

    #[test]
    fn initial_hl_tableau_invariants() {
        // basic variables in fixed order here, but interleaved w/ non-basic overall
        let basic = vec![
            VarInfo::new(Var::real(0), Owner::Basic(0)),
            VarInfo::new(Var::real(1), Owner::Basic(0)),
        ];
        let non_basic = vec![
            VarInfo::new(Var::real(2), Owner::NonBasic(0))
                .with_bounds(Bounds::new(Some(rbig!(-1).into()), Some(rbig!(1).into()))),
            VarInfo::new(Var::real(3), Owner::NonBasic(1))
                .with_bounds(Bounds::new(Some(rbig!(0).into()), Some(rbig!(0).into()))),
        ];
        let equations = vec![vec![Rational::ONE; 2]; 2];
        let ctx = ConvContext::default();
        let tableau = LRASolver::from_eqs(basic, non_basic, equations, ctx).unwrap();
        assert!(tableau.assert_basic_assignments());
        assert!(tableau.assert_non_basic_in_bounds());
    }

    /// An example tableau to test manual operations on
    ///
    /// Details:
    ///
    /// Original system before slacking: { 2 <= x + y,  0 <= 2*x - y, 1 <= -x + 2*y }
    ///                                  { y >= -x + 2, y <= 2*x,     y >= (1/2)*x + 1/2 }
    ///
    ///      Y
    ///       ^
    ///       │
    ///       │
    ///       │
    ///       │         /
    ///       │        //     .
    ///       │        /     .
    ///       ─       //    .
    ///  //   │      //oooooooooo//
    ///   ////│     //oooooooooo//
    ///      ///   //oooooooo//
    ///       │/////ooooo/////
    ///       │  ///o/////
    ///       ─  /////
    ///       │ //// //
    ///       ///     //
    /// ──────┼/───│───//────│──────────────>
    ///       │         ///                X
    ///       │           //
    ///                    //
    ///                      /
    ///
    ///
    /// Variable ordering: {x, y, s1, s2, s3}
    /// `s_i` are basic initially and have bounds, `x` and `y` are non-basic and are initially unbounded
    ///
    /// Note: unlike the solver construction in LRASolver::from_eqs, this system has variable IDs
    /// for non-basic variables that are greater than those of the basic in numerical order. This
    /// doesn't affect the solver at all, but may lead to confusion when inspecting assignments in
    /// the tests below.
    ///
    /// Tableau is:
    ///    | x  y
    /// ---+------
    /// s1 | 1  1    2 <= s1
    /// s2 | 2 -1    0 <= s2
    /// s3 |-1  2    1 <= s3
    ///
    fn ex_5_6_tableau() -> LRASolver<TableauDense> {
        let basic = vec![
            VarInfo::new(Var::real(1), Owner::Basic(0)).with_bounds(Bounds::above_of(2)), // 2 <= s1
            VarInfo::new(Var::real(2), Owner::Basic(1)).with_bounds(Bounds::above_of(0)), // 0 <= s2
            VarInfo::new(Var::real(3), Owner::Basic(2)).with_bounds(Bounds::above_of(1)), // 1 <= s3
        ];
        let non_basic = vec![
            VarInfo::new(Var::real(4), Owner::NonBasic(0)), // x
            VarInfo::new(Var::real(5), Owner::NonBasic(1)), // y
        ];
        let equations = vec![
            vec![rbig!(1), rbig!(1)],
            vec![rbig!(2), rbig!(-1)],
            vec![rbig!(-1), rbig!(2)],
        ];
        let ctx = ConvContext::default();
        LRASolver::from_eqs(basic, non_basic, equations, ctx).unwrap()
    }

    /// A simple infeasible tableau to test
    ///
    /// x <= 0, y <= 0, y >= -x + 1 --> (x, y) in 3rd quadrant and also above y = -x + 1
    ///
    /// Variable ordering: {s1, s2, s3, x, y}
    /// `s_i` are basic initially and have bounds, `x` and `y` are non-basic and are initially unbounded
    ///
    /// Tableau is:
    ///    |  x  y
    /// ---+-------
    /// s1 |  1  0    s1 <= 0
    /// s2 |  0  1    s2 <= 0
    /// s3 | -1 -1    s3 <= -1
    ///
    /// Initially, when all variables are assigned 0, the bounds on `s3` are violated.
    ///
    fn ex_triangle_hole_infeasible() -> LRASolver<TableauDense> {
        let basic = vec![
            VarInfo::new(Var::real(1), Owner::Basic(0)).with_bounds(Bounds::below_of(0)),
            VarInfo::new(Var::real(2), Owner::Basic(1)).with_bounds(Bounds::below_of(0)),
            VarInfo::new(Var::real(3), Owner::Basic(2)).with_bounds(Bounds::below_of(-1)),
        ];

        let non_basic = vec![
            VarInfo::new(Var::real(4), Owner::NonBasic(0)),
            VarInfo::new(Var::real(5), Owner::NonBasic(1)),
        ];

        let equations = vec![
            vec![rbig!(1), rbig!(0)],
            vec![rbig!(0), rbig!(1)],
            vec![rbig!(-1), rbig!(-1)],
        ];
        LRASolver::from_eqs(basic, non_basic, equations, ConvContext::default()).unwrap()
    }

    #[test]
    fn ex_5_6_tableau_initial_invariants() {
        let tableau = ex_5_6_tableau();
        assert!(tableau.assert_basic_assignments());
        assert!(tableau.assert_non_basic_in_bounds());
    }

    #[test]
    fn ex_5_6_update_x() {
        let mut tableau = ex_5_6_tableau();
        let orig_lltab = tableau.tableau.clone();

        // Increase x by 2 and then update the basic variables
        tableau.update(0, &rbig!(2).into());
        assert!(tableau.assert_basic_assignments());
        assert!(tableau.assert_non_basic_in_bounds()); // -inf <= 2 <= inf
        assert_eq!(orig_lltab, tableau.tableau); // no pivot occurred
    }

    #[test]
    fn ex_5_6_tableau_pivot_s1_x() {
        // In the initial state, s1's value (0) doesn't satisfy it's bounds (2 <= s1)
        let mut solver = ex_5_6_tableau();

        // Pivot s1 (row 0) and x (col 0). We increase s1's value to 2 by increasing x by 2 and
        // then pivoting.
        solver.pivot_and_update(0, 0, &rbig!(2).into()).unwrap();

        assert!(solver.assert_basic_assignments());
        assert!(solver.assert_non_basic_in_bounds()); // -inf <= 2 <= inf

        // Check underlying tableau
        let expected_lldata = [
            vec![rbig!(1), rbig!(-1)],
            vec![rbig!(2), rbig!(-3)],
            vec![rbig!(-1), rbig!(3)],
        ];
        let expected_lltab = TableauDense::from_rows(&expected_lldata).unwrap();
        assert_eq!(solver.tableau, expected_lltab);

        // Check post pivot_and_update variable assignments
        assert_eq!(solver.variables[0].val, 2.into()); // x
        assert_eq!(solver.variables[1].val, 0.into()); // y, satisfies it's bounds
        assert_eq!(solver.variables[2].val, 2.into()); // s1, satisfies it's bounds
        assert_eq!(solver.variables[3].val, 4.into()); // s2
        assert_eq!(solver.variables[4].val, (-2).into()); // s3
    }

    #[test]
    fn ex_5_6_tableau_pivot_s1_x_then_s3_y() {
        // In the initial state, s1's value (0) doesn't satisfy it's bounds (2 <= s1)
        let mut solver = ex_5_6_tableau();
        // Increase s1's value to 2 by increasing x by 2 and then pivoting
        solver.pivot_and_update(0, 0, &2.into()).unwrap();
        // Increase s3's value to 1 by increasing y by 1 and then pivoting
        // In the basic/non-basic vector ordering, s3 is now at index 1 and y is at index 1.
        solver.pivot_and_update(2, 1, &1.into()).unwrap();

        assert!(solver.assert_basic_assignments());
        assert!(solver.assert_non_basic_in_bounds());
        let expected_lldata = [
            vec![rbig!(2 / 3), rbig!(-1 / 3)],
            vec![rbig!(1), rbig!(-1)],
            vec![rbig!(1 / 3), rbig!(1 / 3)],
        ];
        let expected_lltab = TableauDense::from_rows(&expected_lldata).unwrap();
        assert_eq!(solver.tableau, expected_lltab);

        // Check post pivot_and_update variable assignments
        assert_eq!(solver.variables[0].val, 1.into()); // x, -inf <= 1 <= +inf
        assert_eq!(solver.variables[1].val, 1.into()); // y, -inf <= 1 <= +inf
        assert_eq!(solver.variables[2].val, 2.into()); // s1, 2 <= 2
        assert_eq!(solver.variables[3].val, 1.into()); // s2, 0 <= 1
        assert_eq!(solver.variables[4].val, 1.into()); // s3, 1 <= 1
    }

    #[test]
    fn ex_5_6_tableau_step_simplex() {
        // In the initial state, s1's value (0) doesn't satisfy it's bounds (2 <= s1)
        // The simplex step should increase s1's value to its lower bound of 2 by increasing x by 2
        // and then pivoting
        let mut solver = ex_5_6_tableau();
        let result1 = solver.step_simplex().expect("Failed to step simplex 1");
        assert!(matches!(result1, SimplexStepResult::Unknown)); // we don't know that status yet
        assert!(solver.assert_basic_assignments());
        assert!(solver.assert_non_basic_in_bounds());

        // Check underlying tableau after first step
        let expected_lldata = [
            vec![rbig!(1), rbig!(-1)],
            vec![rbig!(2), rbig!(-3)],
            vec![rbig!(-1), rbig!(3)],
        ];
        let expected_lltab = TableauDense::from_rows(&expected_lldata).unwrap();
        assert_eq!(solver.tableau, expected_lltab);

        // Check post pivot_and_update variable assignments
        assert_eq!(solver.variables[0].val, 2.into()); // x
        assert_eq!(solver.variables[1].val, 0.into()); // y, satisfies it's bounds
        assert_eq!(solver.variables[2].val, 2.into()); // s1, satisfies it's bounds
        assert_eq!(solver.variables[3].val, 4.into()); // s2
        assert_eq!(solver.variables[4].val, (-2).into()); // s3

        // now do two more steps to reach feasibility
        let result2 = solver.step_simplex().expect("Failed to step simplex 2");
        assert!(matches!(result2, SimplexStepResult::Unknown)); // we don't know that status yet
        assert!(solver.assert_basic_assignments());
        assert!(solver.assert_non_basic_in_bounds());
        let result3 = solver.step_simplex().expect("Failed to step simplex 3");
        assert!(matches!(result3, SimplexStepResult::Feasible));

        // Check that the current assignment satisfies all constraints
        assert!(solver.assert_basic_assignments());
        assert!(solver.assert_basic_in_bounds()); // this assertion only holds here after the last step
        assert!(solver.assert_non_basic_in_bounds());
    }

    #[test]
    fn ex_triangle_hole_step_simplex() {
        // In the initial state, s3's value 0 doesn't satisfy it's bounds s3 <= -1
        // The first simplex step should decrease s3's value to its upper bound of -1
        // by increasing x by 1 and pivoting.
        let mut tableau = ex_triangle_hole_infeasible();
        let result1 = tableau.step_simplex().expect("Failed to step simplex 1");
        assert!(matches!(result1, SimplexStepResult::Unknown));
        assert!(tableau.assert_basic_assignments());
        assert!(!tableau.assert_basic_in_bounds()); // s1 is now basic and the only one out of bounds
        assert!(tableau.assert_non_basic_in_bounds());

        // s1 is out of bounds, set to it's upper bound 0 and pivot with y
        let result2 = tableau.step_simplex().expect("Failed to step simplex 2");
        assert!(matches!(result2, SimplexStepResult::Unknown));
        assert!(tableau.assert_basic_assignments());
        assert!(!tableau.assert_basic_in_bounds()); // s2 is now basic and out of bounds
        assert!(tableau.assert_non_basic_in_bounds());

        // s2 is out of bounds and now there is no non-basic variable adjustment that will help
        let result3 = tableau.step_simplex().expect("Failed to step simplex 3");
        assert!(matches!(result3, SimplexStepResult::Infeasible(_)));
        assert!(tableau.assert_basic_assignments());
        assert!(!tableau.assert_basic_in_bounds()); // s2 is still out of bounds
        assert!(tableau.assert_non_basic_in_bounds());

        // verify the infeasible assignment after three steps
        let assignment = tableau.compute_assignment();
        assert_eq!(assignment.get(&Var::real(4)), Some(&Rational::from(0))); // x
        assert_eq!(assignment.get(&Var::real(5)), Some(&Rational::from(1))); // y
        assert_eq!(assignment.get(&Var::real(1)), Some(&Rational::from(0))); // s1
        assert_eq!(assignment.get(&Var::real(2)), Some(&Rational::from(1))); // s2 --> out of bounds
        assert_eq!(assignment.get(&Var::real(3)), Some(&Rational::from(-1))); // s3
    }

    #[test]
    fn ex_5_6_run_simplex() {
        let _ = env_logger::builder().is_test(true).try_init();

        // s1 | 1  1    2 <= s1
        // s2 | 2 -1    0 <= s2
        // s3 |-1  2    1 <= s3
        let mut solver = ex_5_6_tableau();
        let result = solver.solve().expect("Failed to run simplex");
        assert!(matches!(result, SolverDecision::FEASIBLE(_)));
        if let SolverDecision::FEASIBLE(ass) = result {
            assert_eq!(ass.nvars(), 5);
            // In this example (and current simplex implementation, all values are integer
            // s1 = 2
            // s2 = 1
            // s3 = 1
            // x  = 1
            // y  = 1

            let model = solver.get_rational_model().unwrap(); // solver is SAT
            let x = model.get(&Var::real(4)).unwrap();
            let y = model.get(&Var::real(5)).unwrap();
            let s1 = model.get(&Var::real(1)).unwrap();
            let s2 = model.get(&Var::real(2)).unwrap();
            let s3 = model.get(&Var::real(3)).unwrap();
            // tableau constraints
            assert_eq!(*s1, x + y);
            assert_eq!(*s2, rbig!(2) * x - y);
            assert_eq!(*s3, -x + rbig!(2) * y);
            // slack bounds
            assert!(rbig!(2) <= *s1);
            assert!(rbig!(0) <= *s2);
            assert!(rbig!(1) <= *s3);
        } else {
            unreachable!("ex_5_6_run_simplex should be feasible");
        }
    }

    #[test]
    fn ex_triangle_hole_run_simplex() {
        let mut tableau = ex_triangle_hole_infeasible();
        let result = tableau.solve().expect("Failed to run simplex");
        assert!(matches!(result, SolverDecision::INFEASIBLE(_)));
    }

    #[test]
    fn ex_triangle_hole_run_simplex_conflict() {
        let _ = env_logger::builder().is_test(true).try_init();
        let mut tableau = ex_triangle_hole_infeasible();
        match tableau.solve().expect("Failed to run simplex") {
            SolverDecision::INFEASIBLE(conflict) => {
                assert_eq!(conflict.len(), 3);
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn ex_5_6_assert_lower() {
        let mut solver = ex_5_6_tableau();
        let result = solver.solve().expect("Failed to run simplex, first run");
        assert!(matches!(result, SolverDecision::FEASIBLE(_)));
        // x (Var(4, Real)) is assigned 1, so we expect asserting lower bound zero to satisfy the current
        // assignment
        assert_eq!(
            solver.assert_lower(&Var::real(4), &0i32.into()).unwrap(),
            Some(true)
        );

        let result = solver.solve().expect("Failed to run simplex");
        assert!(
            matches!(result, SolverDecision::FEASIBLE(_)),
            "unexpected result when x >= 0 is asserted"
        );

        // assert a much larger bound x >= 100; doesn't contradict the current bound on x (-inf)
        assert_eq!(
            solver.assert_lower(&Var::real(1), &100i32.into()).unwrap(),
            None
        );

        // still feasible: system has solutions where x is unbounded
        let result = solver.solve().expect("Failed to run simplex");
        assert!(
            matches!(result, SolverDecision::FEASIBLE(_)),
            "unexpected result when x >= 100 is asserted"
        );

        // finally, assert a large bound y >= 100; doesn't contradict the current bound on y (-inf)
        // and the system is still feasible
        assert_eq!(
            solver.assert_lower(&Var::real(2), &2i32.into()).unwrap(),
            Some(true)
        );
        let result = solver.solve().expect("Failed to run simplex");
        assert!(
            matches!(result, SolverDecision::FEASIBLE(_)),
            "unexpected result when y >= 100 is asserted"
        );
    }

    #[test]
    fn ex_5_6_backtrack_from_unsat() {
        let mut solver = ex_5_6_tableau();
        let result = solver.solve().unwrap();
        assert!(matches!(result, SolverDecision::FEASIBLE(_)));

        // set a backtrack point and assert x <= 0 which makes the system infeasible
        // because all solutions are strictly in the first quadrant
        let level = solver.set_backtrack();
        assert_eq!(level, 0);
        assert_eq!(
            solver.assert_upper(&Var::real(4), &0i32.into()).unwrap(),
            None
        );
        let result = solver.solve().unwrap();
        assert!(matches!(result, SolverDecision::INFEASIBLE(_)));

        // backtrack to level 0 and assert that the system is feasible again
        solver.backtrack(level);
        let result = solver.solve().unwrap();
        assert!(matches!(result, SolverDecision::FEASIBLE(_)));
    }
}
