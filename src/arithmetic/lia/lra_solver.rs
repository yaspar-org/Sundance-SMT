// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Linear rational arithmetic solver
//!
//! The main object here is the [LRASolver] which manages solver state, implements
//! the rational solver methods and contains data like variable info and an underlying
//! tableau representing a linear system.

use crate::debug_println;
use std::collections::BTreeMap;
use std::fmt;

use crate::arithmetic::lia::bounds::Bounds;
use crate::arithmetic::lia::context::ConvContext;
use crate::arithmetic::lia::linear_system::Rel;
use crate::arithmetic::lia::qdelta::QDelta;
use crate::arithmetic::lia::solver_result::{
    Assignment, Conflict, SolverDecision, SolverError, SolverResult, SolverReturn,
};
use crate::arithmetic::lia::stats::Stats;
use crate::arithmetic::lia::tableau::{Tableau, TableauImpl, TableauKind};
use crate::arithmetic::lia::types::Rational;
use crate::arithmetic::lia::variables::{Owner, Var, VarInfo, VarType};
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

/// Whether a basic variable needs to increase (below lower bound)
/// or decrease (above upper bound) to become feasible.
enum PivotDirection {
    Increase,
    Decrease,
}

/// Current pivot selection heuristic
#[derive(Debug)]
enum PivotHeuristic {
    /// prefers basic variables by order and non-basic variables that are unbounded
    Greedy,
    /// prefers both basic and non-basic variables by order
    Bland,
}

/// Linear real arithmetic solver
pub struct LRASolver {
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
    tableau: TableauImpl,

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
    /// Current pivot selection heuristic
    pivot_heuristic: PivotHeuristic,
    /// During `solve()`, the current number of simplex steps that have been performed
    num_simplex_steps: usize,

    // -- Mappings for bookkeeping --
    /// mapping from Var to index in `self.variables`
    var_to_idx: BTreeMap<Var, usize>,
    /// Conversion context from the frontend including the name <-> Var mapping
    ctx: ConvContext,
}

impl fmt::Debug for LRASolver {
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
        s.push_str(&format!("Pivot heuristic: {:?}\n", self.pivot_heuristic));
        s.push_str(&format!("Num simplex steps: {}\n", self.num_simplex_steps));
        // TODO: add the rest of the solver state, including backtracking info
        write!(f, "{}", s)
    }
}

/// Shared functionality among all concrete instances of LRASolver
impl LRASolver {
    /// Perform a low-level swap of variable info between a basic and a non-basic variable.
    ///
    /// - `row` is the tableau row owned by the basic variable
    /// - `col` is the tableau col owned by the non-basic variable
    //
    // Important Note: the order of variables in `self.variables` is not modified in this
    // procedure. This is neccessary for the implementation of Bland's pivot selection rule to
    // be correct.
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
        debug_println!(
            10,
            0,
            "lia::lra_solver:  pivot_and_update row={}, col={}, val={}",
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

    /// Incrementally extend a live, already-solved tableau with a new relation
    /// `Σ aᵢ xᵢ ⋈ c`, represented by the fresh slack variable `slack`.
    ///
    /// The tableau only ever grows: rows are never removed, only relaxed on backtrack.
    /// The slack is introduced as a **basic** variable owning a brand-new row, so it appears
    /// only in that row and disturbs no existing non-basic variable's in-bounds status. Only the
    /// homogeneous terms `Σ aᵢ xᵢ` are used to build the row; the slack is added **unbounded**.
    /// The bound implied by `rel`'s constant/constraint type is applied separately by the caller
    /// via [`Self::assert_lower`]/[`Self::assert_upper`].
    ///
    /// Because `rel` may mention variables that are currently basic (and rows must be expressed
    /// over non-basic columns only), each basic variable `xᵢ` owning row `r` is substituted using
    /// its own row: `xᵢ = Σ_c tableau[r][c]·nonbasicₖ`, so its contribution `aᵢ·xᵢ` adds
    /// `aᵢ·tableau[r][c]` to column `c`. Non-basic variables contribute their coefficient directly.
    /// Variables the solver has never seen are first introduced as unbounded non-basic columns.
    ///
    /// After this call the check-invariant holds (non-basics are in bounds; the new basic slack's
    /// row is satisfied by construction and the slack is unbounded), so [`Self::is_valid`] is true
    /// and feasibility of any subsequently asserted bound must be (re)checked via [`Self::solve`].
    ///
    /// `add_relation` does not touch the bound trail or backtrack level: the row persists across
    /// all backtracks. The slack starts unbounded, so the first `assert_*` on it records the old
    /// bound (`None`), and a later `backtrack` restores it to unbounded automatically.
    pub fn add_relation(&mut self, rel: Rel<Rational>, slack: Var) -> SolverResult<()> {
        if self.var_to_idx.contains_key(&slack) {
            return Err(SolverError(format!(
                "add_relation: slack variable {slack:?} already exists"
            )));
        }

        // Step 1: register any brand-new problem variables as unbounded non-basic columns.
        for term in rel.terms_ref() {
            let v = term.var();
            if !self.var_to_idx.contains_key(&v) {
                let new_col = self.tableau.add_col().map_err(|e| {
                    SolverError(format!("add_relation: failed to grow tableau column: {e}"))
                })?;
                let new_idx = self.variables.len();
                self.variables.push(VarInfo::new(v, Owner::NonBasic(new_col)));
                self.non_basic.push(new_idx);
                self.var_to_idx.insert(v, new_idx);
            }
        }

        // Step 2: build the new row over the current non-basic columns, substituting out any
        // basic variables. Accumulate with `+=` so duplicate/uncombined terms are handled.
        let ncols = self.non_basic.len();
        let mut row = vec![Rational::ZERO; ncols];
        for term in rel.terms_ref() {
            let a = term.coeff_ref();
            let idx = *self.var_to_idx.get(&term.var()).unwrap();
            match self.variables[idx].owner {
                Owner::NonBasic(c) => {
                    row[c] += a;
                }
                Owner::Basic(r) => {
                    for (c, entry) in row.iter_mut().enumerate() {
                        let t = self.tableau.get(r, c)?;
                        if !t.is_zero() {
                            *entry += a * t;
                        }
                    }
                }
            }
        }

        // Step 3: grow the tableau by one row and write the non-zero coefficients.
        let new_row = self.tableau.add_row().map_err(|e| {
            SolverError(format!("add_relation: failed to grow tableau row: {e}"))
        })?;
        debug_assert_eq!(new_row, self.basic.len());
        for (c, coeff) in row.iter().enumerate() {
            if !coeff.is_zero() {
                self.tableau.set_entry(new_row, c, coeff.clone())?;
            }
        }

        // Step 4: compute β(slack) = Σ_c row[c]·β(nonbasic_c), so the new row is satisfied.
        let mut beta = QDelta::ZERO;
        for (c, coeff) in row.iter().enumerate() {
            if !coeff.is_zero() {
                beta += &(&self.variables[self.non_basic[c]].val * coeff);
            }
        }

        // Step 5: register the slack as a new basic variable owning `new_row`.
        let new_idx = self.variables.len();
        let mut vinfo = VarInfo::new(slack, Owner::Basic(new_row));
        vinfo.update_assignment(beta);
        self.variables.push(vinfo);
        self.basic.push(new_idx);
        self.var_to_idx.insert(slack, new_idx);

        // Feasibility of the extended system must be re-established by solve().
        self.state = LRASolverState::Unknown;
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
        debug_println!(
            10,
            0,
            "lia::lra_solver: assert_lower on variable {0:?}, lower={1}, non_basic?={2}",
            v,
            l,
            v.is_non_basic().is_some()
        );

        let bs = &v.bounds;
        if bs.above_upper(l) {
            // new lower bound is inconsistent with current upper bound
            return Ok(Some(false));
        } else if bs.above_lower(l) {
            // `l` is a tighter lower bound
            self.old_lower_bounds
                .push((v.var, v.bounds.lower.clone(), self.backtrack_level));
            v.update_lower(l.clone());
        }
        // Note: in this check, l can be infinitesimally (in the QDelta sense) less or
        // equal to v.val
        if *l <= v.val {
            return Ok(Some(true));
        }
        // if v.val is now outside the new lower bound, and v is a non-basic variable,
        // update v.val and adjust the basic variable values to maintain the tableau
        // invariant
        if let Some(col) = v.is_non_basic() {
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

    /// Restore a previous assignment when backtracking.
    ///
    /// Restores each **non-basic** variable's value from the snapshot, then recomputes every
    /// **basic** variable's value from the current tableau structure so the row equations hold by
    /// construction. This is pivot-invariant: recomputing basics from the restored non-basics
    /// reproduces the snapshot point exactly on the unchanged-structure case (so it is
    /// behavior-preserving for the existing branch-and-bound usage), while also remaining correct
    /// when rows/columns were added since the snapshot was taken (`add_relation`). Variables that
    /// post-date the snapshot are absent from the map and default to zero; their basic slack rows
    /// are then made consistent by the recomputation step.
    fn restore_assignment(&mut self) {
        let previous_model = self
            .old_assignment
            .clone()
            .expect("cannot restore assignment: no previous assignment exists");
        // Non-basics: take the snapshot value, or zero for variables added after the snapshot.
        for &idx in self.non_basic.iter() {
            let var = self.variables[idx].var;
            self.variables[idx].val = previous_model.get(&var).cloned().unwrap_or(QDelta::ZERO);
        }
        // Basics: recompute from the (possibly re-pivoted / grown) tableau so equations hold.
        for row in 0..self.basic.len() {
            let val = self.calculate_assignment(row);
            self.variables[self.basic[row]].val = val;
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

    /// Clear a terminal `Unsat` state back to `Unknown`, so the solver can be reused after a
    /// conflicting [`Self::solve`] — e.g. by an incremental frontend that re-checks feasibility
    /// once the SAT layer has backtracked and relaxed bounds. Does nothing unless the solver is
    /// currently `Unsat`.
    ///
    /// This is deliberately *not* folded into [`Self::backtrack`]: the branch-and-bound layer
    /// relies on [`Self::set_backtrack`] being a no-op while `Unsat`, so [`Self::backtrack`] must
    /// leave that state intact. Callers that want the state cleared opt in explicitly.
    pub fn clear_unsat_state(&mut self) {
        if matches!(self.state, LRASolverState::Unsat) {
            self.state = LRASolverState::Unknown;
        }
    }

    /// Restore the tableau structure (basis, non-basis, coefficients, and variable owners)
    /// from a saved snapshot. Used by try_unit_cube_test to undo pivots performed during
    /// speculative solving.
    fn restore_tableau(
        &mut self,
        tableau: &TableauImpl,
        basic: &[usize],
        non_basic: &[usize],
        owners: &[Owner],
    ) {
        self.tableau = tableau.clone();
        self.basic = basic.to_vec();
        self.non_basic = non_basic.to_vec();
        for (i, owner) in owners.iter().enumerate() {
            self.variables[i].owner = owner.clone();
        }
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
    /// By definition of <= on Q_δ, either a) 0 < x_i^rat - l_i or b) it is zero and 0 <= x_i^inf.
    /// In the zero case, there is no constraint on δ_0 other than non-negativity. Otherwise, if
    /// 0 <= x_i^inf there is again no constraint on δ_0. So finally, without loss of generality
    /// assume 0 < (x_i^rat - l_i) and x_i^inf < 0:
    ///
    ///   0 <= (x_i^rat - l_i) + x_i^inf δ_0
    ///   -x_i^inf δ_0 <= (x_i^rat - l_i)
    ///   δ_0 <= (x_i^rat - l_i)/abs(x_i^inf)
    ///
    /// The last step is justified by x_i^inf < 0.
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
                    delta_ub.push(d0);
                } else if l.inf().is_zero() && v.val.inf() < &Rational::ZERO {
                    // lower bound is non-strict, but assigned value is infinitesimally smaller
                    // than some rational value
                    //
                    // Note: `v.val.rat() - l.rat() >= 0` in this branch because the assignment to
                    // `v` satisfies all bounds.
                    let d0 = (v.val.rat() - l.rat()) / v.val.inf().clone().abs();
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
                    delta_ub.push(d0);
                } else if u.inf().is_zero() && v.val.inf() > &Rational::ZERO {
                    // upper bound is non-strict, but assigned value is infinitesimally greater
                    // than some rational value
                    //
                    // Note: `u.rat() - v.val.rat() >= 0` in this branch because the assignment to
                    // `v` satisfies all bounds.
                    let d0 = (u.rat() - v.val.rat()) / v.val.inf().clone().abs();
                    delta_ub.push(d0);
                }
            }
        }
        let d0 = delta_ub.into_iter().min().unwrap_or(Rational::ONE); // choose δ_0 = 1 if there are no positive upper bounds
        debug_assert!(d0 >= Rational::ZERO);
        debug_println!(10, 0, "lia::lra_solver: δ_0 = {d0}");
        d0
    }

    /// Implements the SPASS-SATT pivot hueristic: start with Greedy non-basic variable selection
    /// (see [`LRASolver::find_pivot_and_update`]) and switch to Bland's rule after a fixed number of pivot
    /// steps.
    fn update_pivot_heuristic(&mut self) {
        if let PivotHeuristic::Greedy = self.pivot_heuristic
            && self.num_simplex_steps > self.basic.len()
        {
            debug_println!(
                25,
                0,
                "lia::lra_solver: switching pivot heuristic to Bland's Rule"
            );
            self.pivot_heuristic = PivotHeuristic::Bland;
        }
    }

    /// Helper function for `step_simplex` that finds a non-basic variable to pivot on.
    fn find_pivot_and_update(
        &mut self,
        row: usize,
        row_var_idx: usize,
        direction: PivotDirection,
    ) -> SolverResult<SimplexStepResult> {
        let target_bound = match direction {
            PivotDirection::Increase => self.variables[row_var_idx]
                .bounds
                .lower
                .as_ref()
                .unwrap()
                .clone(),
            PivotDirection::Decrease => self.variables[row_var_idx]
                .bounds
                .upper
                .as_ref()
                .unwrap()
                .clone(),
        };

        let non_basics: Vec<_> = self
            .variables
            .iter()
            .filter(|v| v.is_non_basic().is_some())
            .collect();

        if let PivotHeuristic::Greedy = self.pivot_heuristic {
            let unbounded_non_basics: Vec<_> = non_basics
                .iter()
                .filter(|v| v.is_totally_unbounded())
                .collect();
            if !unbounded_non_basics.is_empty() {
                let col = unbounded_non_basics[0].is_non_basic().unwrap();
                let a_i_j = self.tableau.get(row, col).unwrap();
                // as long as a_i_j is non-zero, the non-basic variable is eligible
                if !a_i_j.is_zero() {
                    debug_println!(
                        15,
                        0,
                        "lia::lra_solver: (greedy) pivot basic (row {}) {} and non-basic (col {}) {}, update non-basic val to {}",
                        row,
                        self.variables[row_var_idx],
                        col,
                        self.variables[self.non_basic[col]],
                        target_bound
                    );
                    self.pivot_and_update(row, col, &target_bound)?;
                    // Invariant: in `step_simplex` or `find_pivot_and_update` => `self.state ==
                    // LRASolverState::Unknown`
                    return Ok(SimplexStepResult::Unknown);
                }
            }
            // No unbounded non-basic variable found. Select the eligible variable with the
            // smallest number of non-zero entries in its tableau column. Ties are broken by
            // the fixed self.variables ordering (iteration order).
            let mut best: Option<(usize, usize)> = None; // (col, nnz)
            for var in non_basics.iter() {
                let col = var.is_non_basic().unwrap();
                let a_i_j = self.tableau.get(row, col).unwrap();

                let eligible = match direction {
                    PivotDirection::Increase => {
                        (a_i_j > &Rational::ZERO && !var.at_upper())
                            || (a_i_j < &Rational::ZERO && !var.at_lower())
                    }
                    PivotDirection::Decrease => {
                        (a_i_j > &Rational::ZERO && !var.at_lower())
                            || (a_i_j < &Rational::ZERO && !var.at_upper())
                    }
                };

                if eligible {
                    let nnz = self.tableau.col_nnz(col);
                    if best.is_none_or(|(_, best_nnz)| nnz < best_nnz) {
                        best = Some((col, nnz));
                    }
                }
            }

            if let Some((col, _)) = best {
                debug_println!(
                    15,
                    0,
                    "lia::lra_solver: (greedy/col_nnz) pivot basic (row {}) {} and non-basic (col {}) {}, update non-basic val to {}",
                    row,
                    self.variables[row_var_idx],
                    col,
                    self.variables[self.non_basic[col]],
                    target_bound
                );
                self.pivot_and_update(row, col, &target_bound)?;
                return Ok(SimplexStepResult::Unknown);
            }
        }

        // Bland's rule fallback: iterate over non_basic (col) variables in the fixed variable
        // ordering and select the first eligible one.
        for var in non_basics.iter() {
            let col = match var.is_non_basic() {
                Some(c) => c,
                None => continue,
            };
            let a_i_j = self.tableau.get(row, col).unwrap();

            let eligible = match direction {
                PivotDirection::Increase => {
                    (a_i_j > &Rational::ZERO && !var.at_upper())
                        || (a_i_j < &Rational::ZERO && !var.at_lower())
                }
                PivotDirection::Decrease => {
                    (a_i_j > &Rational::ZERO && !var.at_lower())
                        || (a_i_j < &Rational::ZERO && !var.at_upper())
                }
            };

            if eligible {
                debug_println!(
                    15,
                    0,
                    "lia::lra_solver: pivot basic (row {}) {} and non-basic (col {}) {}, update non-basic val to {}",
                    row,
                    self.variables[row_var_idx],
                    col,
                    self.variables[self.non_basic[col]],
                    target_bound
                );
                self.pivot_and_update(row, col, &target_bound)?;
                // Invariant: in `step_simplex` or `find_pivot_and_update` => `self.state ==
                // LRASolverState::Unknown`
                return Ok(SimplexStepResult::Unknown);
            }
        }

        self.state = LRASolverState::Unsat;
        Ok(SimplexStepResult::Infeasible(
            self.variables[row_var_idx].var,
        ))
    }

    /// Perform one simplex step on self.
    ///
    /// Roughly, find the first (in order) basic variable that doesn't satisfy its
    /// bounds. If none, we're done and the current assignment is SAT. Otherwise,
    /// find the first non-basic variable that can bring the basic into its bounds
    /// range and make the adjustment, pivoting the two variables in the process.
    /// Otherwise, the system of inequalities is UNSAT.
    ///
    /// Find a suitable non-basic pivot variable and perform the pivot, or return
    /// `Infeasible` if no eligible non-basic variable exists.
    fn step_simplex(&mut self) -> SolverResult<SimplexStepResult> {
        // TODO: step_simplex: Use the violated-variable priority queue technique
        // TODO: step_simplex: The way the variable loops are setup here implicitly implements
        //   Bland's selection rule. The SPASS-SATT heuristic perform much better on SMT-LIB
        //   benchmarks however, and should not be hard to add here.
        //
        //   SPASS-SATT heuristic: perform greedy pivots for violated basic variables up to some number of iterations,
        //     e.g. #iterations = #(basic variables).
        //   1. (greedy) For basic variables, prefer smallest one violated in the fixed variable order.
        //     For non-basic variables, prefer totally unbounded first, then vars w/ smallest # of non-zero
        //     coefficients in the tableau, finally by smallest in the order.
        //   2. Switch to Bland's rule
        //
        // iterate over basic (row) variables in the fixed variable ordering
        for var_idx in 0..self.variables.len() {
            let row = match self.variables[var_idx].is_basic() {
                Some(r) => r,
                None => continue,
            };

            // three cases in order:
            // 1. v is already in bounds
            // 2. v.val is less than the lower bound
            // 3. v.val is greater than the upper bound
            if self.variables[var_idx].in_bounds() {
                continue;
            } else if self.variables[var_idx].below_lower() {
                return self.find_pivot_and_update(row, var_idx, PivotDirection::Increase);
            } else {
                // self.variables[var_idx].above_upper() is true
                return self.find_pivot_and_update(row, var_idx, PivotDirection::Decrease);
            }
        }
        // No more pivots are required, so the system is feasible.
        self.state = LRASolverState::Sat;
        Ok(SimplexStepResult::Feasible)
    }

    /// Perform the general simplex algorithm to find a feasible solution.
    pub fn solve(&mut self) -> SolverResult<SolverReturn> {
        self.num_simplex_steps = 0;
        loop {
            debug_println!(
                21,
                0,
                "lia::lra_solver: Stepping simplex, iteration {}",
                self.num_simplex_steps
            );

            self.update_pivot_heuristic(); // possibly switch heuristics based on the current solver state.
            match self.step_simplex() {
                Ok(SimplexStepResult::Unknown) => {
                    self.num_simplex_steps += 1;
                }
                Ok(SimplexStepResult::Feasible) => {
                    let assg = self.compute_assignment();
                    debug_println!(
                        21,
                        0,
                        "lia::lra_solver::solve: simplex complete, Feasible, num iterations = {}",
                        self.num_simplex_steps
                    );
                    let stats = Stats {
                        num_lra_solve: 1,
                        num_simplex_steps: self.num_simplex_steps,
                    };
                    return Ok(SolverReturn::new(SolverDecision::FEASIBLE(assg), stats));
                }
                Ok(SimplexStepResult::Infeasible(v)) => {
                    let conflict = self.compute_conflict(v)?;
                    debug_println!(
                        21,
                        0,
                        "lia::lra_solver::solve: simplex complete, Infeasible, num iterations = {}",
                        self.num_simplex_steps
                    );
                    let stats = Stats {
                        num_lra_solve: 1,
                        num_simplex_steps: self.num_simplex_steps,
                    };
                    return Ok(SolverReturn::new(
                        SolverDecision::INFEASIBLE(conflict),
                        stats,
                    ));
                }
                Err(e) => return Err(e),
            }
        }
    }

    /// If the solver is in an INFEASIBLE state, return a set of literals
    /// that implies the conflict.
    ///
    /// The conflict produced is guaranteed to be minimal by Farkas' Lemma.
    pub fn compute_conflict(&self, var: Var) -> SolverResult<Conflict<Var>> {
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

    /// Attempt to round non-basic integer variables to the nearest integer value and check
    /// whether the resulting assignment (propagated through the tableau) is still feasible.
    ///
    /// Returns `Some(assignment)` if rounding succeeds, `None` otherwise (original state restored).
    pub fn try_rounding_heuristic(&mut self) -> Option<Assignment<Var>> {
        let d0 = self.calculate_d0();

        // Identify non-basic integer variables with non-integer values and their rounded targets
        let rounds: Vec<(usize, QDelta)> = self
            .non_basic
            .iter()
            .enumerate()
            .flat_map(|(col, &var_idx)| {
                let v = &self.variables[var_idx];
                if v.var.typ != VarType::Int {
                    return None;
                }
                let val = v.val.instantiate(&d0);
                if val.is_int() {
                    return None;
                }
                let floor = Rational::from(val.floor());
                let ceil = Rational::from(val.ceil());
                let rounded = if (&val - &floor) <= (&ceil - &val) {
                    QDelta::from(floor)
                } else {
                    QDelta::from(ceil)
                };
                if !v.bounds.in_bounds(&rounded) {
                    return None;
                }
                Some((col, rounded))
            })
            .collect();

        if rounds.is_empty() {
            return None; // nothing to round, let caller handle normally
        }

        // Save snapshot of all variable assignments
        let snapshot: Vec<QDelta> = self.variables.iter().map(|v| v.val.clone()).collect();

        // Apply rounding via update (preserves tableau equations)
        for (col, rounded) in &rounds {
            self.update(*col, rounded);
        }

        // Check if all variables are still in bounds
        let feasible = self.variables.iter().all(|v| v.in_bounds());

        if feasible {
            let assg = self.compute_assignment();
            Some(assg)
        } else {
            // Restore original assignments
            for (i, val) in snapshot.into_iter().enumerate() {
                self.variables[i].update_assignment(val);
            }
            None
        }
    }

    /// Attempt the unit cube test
    ///
    /// The unit cube tests tightens basic variable bounds by (1/2)*|A_i|_1 and solves the rational
    /// relaxation of the system. Here, |A_i|_1 means the sum of absolute values along the original
    /// i-th tableau row. If the tightened system is feasible, rounding all integer variables to
    /// the nearest integer is guaranteed to produce a valid integer solution.
    pub fn try_unit_cube_test(&mut self) -> SolverResult<Option<Assignment<Var>>> {
        let level = self.set_backtrack();

        // Save tableau structure since solve() performs pivots that backtrack() does not undo
        let saved_tableau = self.tableau.clone();
        let saved_basic = self.basic.clone();
        let saved_non_basic = self.non_basic.clone();
        let saved_owners: Vec<Owner> = self.variables.iter().map(|v| v.owner.clone()).collect();

        let mut trivially_infeasible = false;
        for row in 0..self.basic.len() {
            let var_idx = self.basic[row];
            let v = &self.variables[var_idx];

            let lower = v.bounds.lower.clone();
            let upper = v.bounds.upper.clone();
            if lower.is_none() && upper.is_none() {
                continue;
            }

            let mut norm_1 = Rational::ZERO;
            for col in 0..self.non_basic.len() {
                let coeff = self.tableau.get(row, col).unwrap();
                norm_1 += coeff.clone().abs();
            }

            let half_norm = QDelta::from(norm_1 / Rational::from(2));
            let var = v.var;

            if let Some(l) = lower {
                let new_lower = l + half_norm.clone();
                if let Some(false) = self.assert_lower(&var, &new_lower)? {
                    trivially_infeasible = true;
                    break;
                }
            }

            if let Some(u) = upper {
                let new_upper = u - half_norm;
                if let Some(false) = self.assert_upper(&var, &new_upper)? {
                    trivially_infeasible = true;
                    break;
                }
            }
        }

        if trivially_infeasible {
            self.state = LRASolverState::Unknown;
            self.backtrack(level);
            self.restore_tableau(
                &saved_tableau,
                &saved_basic,
                &saved_non_basic,
                &saved_owners,
            );
            return Ok(None);
        }

        let ret = self.solve()?;

        match ret.decision {
            SolverDecision::FEASIBLE(_) => {
                let d0 = self.calculate_d0();
                let mut rounded_assignments = BTreeMap::new();
                for v in self.variables.iter() {
                    let val = v.val.instantiate(&d0);
                    let rounded = if v.var.typ == VarType::Int {
                        let floor = Rational::from(val.floor());
                        let ceil = Rational::from(val.ceil());
                        if (&val - &floor) <= (&ceil - &val) {
                            floor
                        } else {
                            ceil
                        }
                    } else {
                        val
                    };
                    rounded_assignments.insert(v.var, rounded);
                }

                // Verify the rounded assignment satisfies all original bounds
                for v in self.variables.iter() {
                    let rounded_val = &rounded_assignments[&v.var];
                    let rounded_qdelta = QDelta::from(rounded_val.clone());
                    if !v.bounds.in_bounds(&rounded_qdelta) {
                        self.state = LRASolverState::Unknown;
                        self.backtrack(level);
                        self.restore_tableau(
                            &saved_tableau,
                            &saved_basic,
                            &saved_non_basic,
                            &saved_owners,
                        );
                        return Ok(None);
                    }
                }

                self.state = LRASolverState::Sat;
                self.backtrack(level);
                self.restore_tableau(
                    &saved_tableau,
                    &saved_basic,
                    &saved_non_basic,
                    &saved_owners,
                );
                Ok(Some(Assignment::new(rounded_assignments)))
            }
            _ => {
                self.state = LRASolverState::Unknown;
                self.backtrack(level);
                self.restore_tableau(
                    &saved_tableau,
                    &saved_basic,
                    &saved_non_basic,
                    &saved_owners,
                );
                Ok(None)
            }
        }
    }

    /// Check the two tableau invariants. In particular, this validates that the current assignment
    /// to variables satisfies the Q_δ form of the original system of inequalities.
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
    fn calculate_assignment(&self, row: usize) -> QDelta {
        let mut rhs = QDelta::ZERO;
        for (col, non_basic_idx) in self.non_basic.iter().enumerate() {
            // TODO: getting the whole row at once may be faster here
            rhs += &self.variables[*non_basic_idx].val * self.tableau.get(row, col).unwrap();
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

impl LRASolver {
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
        tableau_kind: TableauKind,
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
        debug_println!(
            15,
            0,
            "lia::lra_solver: LRASolver::from_eqs: nrows = {}",
            nrows
        );
        // at this point: nrows == equations.len() > 0
        if equations[0].len() != ncols {
            return Err(SolverError(format!(
                "Expected {} non-basic variables, but got {}",
                equations[0].len(),
                ncols,
            )));
        }
        debug_println!(
            15,
            0,
            "lia::lra_solver: LRASolver::from_eqs: non_basic.len() = {}",
            ncols
        );

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

        // Convert dense row data to tuples for the Tableau constructor
        let mut tuples = Vec::new();
        for (r, row) in equations.iter().enumerate() {
            for (c, val) in row.iter().enumerate() {
                if !val.is_zero() {
                    tuples.push((r, c, val.clone()));
                }
            }
        }

        Ok(Self {
            variables,
            basic,
            non_basic,
            tableau: TableauImpl::new(tableau_kind, nrows, ncols, tuples)?,
            state: LRASolverState::Unknown,
            old_lower_bounds: vec![],
            old_upper_bounds: vec![],
            backtrack_level: 0,
            old_assignment: None,
            pivot_heuristic: PivotHeuristic::Greedy,
            num_simplex_steps: 0,
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
    use crate::arithmetic::lia::linear_system::Mon;
    use crate::arithmetic::lia::tableau::TableauKind;
    use crate::arithmetic::lia::tableau_dense::TableauDense;
    use crate::arithmetic::lia::variables::{Var, VarInfo};
    use dashu::rbig;

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
        let tableau =
            LRASolver::from_eqs(basic, non_basic, equations, ctx, TableauKind::Dense).unwrap();
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
    fn ex_5_6_tableau() -> LRASolver {
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
        LRASolver::from_eqs(basic, non_basic, equations, ctx, TableauKind::Dense).unwrap()
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
    fn ex_triangle_hole_infeasible() -> LRASolver {
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
        LRASolver::from_eqs(
            basic,
            non_basic,
            equations,
            ConvContext::default(),
            TableauKind::Dense,
        )
        .unwrap()
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
        let TableauImpl::Dense(ref orig_lltab) = tableau.tableau else {
            panic!("expected Dense tableau");
        };
        let orig_lltab = orig_lltab.clone();

        // Increase x by 2 and then update the basic variables
        tableau.update(0, &rbig!(2).into());
        assert!(tableau.assert_basic_assignments());
        assert!(tableau.assert_non_basic_in_bounds()); // -inf <= 2 <= inf
        assert_eq!(TableauImpl::Dense(orig_lltab), tableau.tableau); // no pivot occurred
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
        assert_eq!(solver.tableau, TableauImpl::Dense(expected_lltab));

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
        assert_eq!(solver.tableau, TableauImpl::Dense(expected_lltab));

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
        assert_eq!(solver.tableau, TableauImpl::Dense(expected_lltab));

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
        // s1 | 1  1    2 <= s1
        // s2 | 2 -1    0 <= s2
        // s3 |-1  2    1 <= s3
        let mut solver = ex_5_6_tableau();
        let result = solver.solve().expect("Failed to run simplex").decision;
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
        let result = tableau.solve().expect("Failed to run simplex").decision;
        assert!(matches!(result, SolverDecision::INFEASIBLE(_)));
    }

    #[test]
    fn ex_triangle_hole_run_simplex_conflict() {
        let mut tableau = ex_triangle_hole_infeasible();
        match tableau.solve().expect("Failed to run simplex").decision {
            SolverDecision::INFEASIBLE(conflict) => {
                assert_eq!(conflict.len(), 3);
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn ex_5_6_assert_lower() {
        let mut solver = ex_5_6_tableau();
        let result = solver
            .solve()
            .expect("Failed to run simplex, first run")
            .decision;
        assert!(matches!(result, SolverDecision::FEASIBLE(_)));
        // x (Var(4, Real)) is assigned 1, so we expect asserting lower bound zero to satisfy the current
        // assignment
        assert_eq!(
            solver.assert_lower(&Var::real(4), &0i32.into()).unwrap(),
            Some(true)
        );

        let result = solver.solve().expect("Failed to run simplex").decision;
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
        let result = solver.solve().expect("Failed to run simplex").decision;
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
        let result = solver.solve().expect("Failed to run simplex").decision;
        assert!(
            matches!(result, SolverDecision::FEASIBLE(_)),
            "unexpected result when y >= 100 is asserted"
        );
    }

    #[test]
    fn ex_5_6_backtrack_from_unsat() {
        let mut solver = ex_5_6_tableau();
        let result = solver.solve().unwrap().decision;
        assert!(matches!(result, SolverDecision::FEASIBLE(_)));

        // set a backtrack point and assert x <= 0 which makes the system infeasible
        // because all solutions are strictly in the first quadrant
        let level = solver.set_backtrack();
        assert_eq!(level, 0);
        assert_eq!(
            solver.assert_upper(&Var::real(4), &0i32.into()).unwrap(),
            None
        );
        let result = solver.solve().unwrap().decision;
        assert!(matches!(result, SolverDecision::INFEASIBLE(_)));

        // backtrack to level 0 and assert that the system is feasible again
        solver.backtrack(level);
        let result = solver.solve().unwrap().decision;
        assert!(matches!(result, SolverDecision::FEASIBLE(_)));
    }

    // ─── try_rounding_heuristic tests ───────────────────────────────────────────

    /// Simple system where rounding succeeds:
    ///   Tableau: s = x + y
    ///   x, y are integer non-basic with bounds [0, 10]
    ///   s is a real basic with bounds [0, 20]
    ///   Set x = 3/2, y = 5/2 => s = 4 (in bounds)
    ///   Rounding x to 2 and y to 2 (or 3) keeps s in [0,20]
    #[test]
    fn try_rounding_heuristic_succeeds() {
        let non_basic = vec![
            VarInfo::new(Var::int(0), Owner::NonBasic(0))
                .with_bounds(Bounds::new(Some(rbig!(0).into()), Some(rbig!(10).into()))),
            VarInfo::new(Var::int(1), Owner::NonBasic(1))
                .with_bounds(Bounds::new(Some(rbig!(0).into()), Some(rbig!(10).into()))),
        ];
        let basic = vec![
            VarInfo::new(Var::real(2), Owner::Basic(0))
                .with_bounds(Bounds::new(Some(rbig!(0).into()), Some(rbig!(20).into()))),
        ];
        // s = x + y
        let equations = vec![vec![rbig!(1), rbig!(1)]];
        let ctx = ConvContext::default();
        let mut solver =
            LRASolver::from_eqs(basic, non_basic, equations, ctx, TableauKind::Dense).unwrap();

        // Assign x = 3/2, y = 5/2
        solver.update(0, &QDelta::from(rbig!(3 / 2)));
        solver.update(1, &QDelta::from(rbig!(5 / 2)));

        let result = solver.try_rounding_heuristic();
        assert!(result.is_some(), "rounding should succeed");

        let assg = result.unwrap();
        let x_val = assg.get(&Var::int(0)).unwrap();
        let y_val = assg.get(&Var::int(1)).unwrap();
        assert!(x_val.is_int(), "x should be integer after rounding");
        assert!(y_val.is_int(), "y should be integer after rounding");

        // basic variable should still be in bounds
        let s_val = assg.get(&Var::real(2)).unwrap();
        assert!(*s_val >= rbig!(0) && *s_val <= rbig!(20));
    }

    /// Rounding fails because tight basic bounds make it infeasible.
    ///   Tableau: s = 2*x
    ///   x is integer non-basic with bounds [0, 10]
    ///   s is real basic with bounds [3, 3] (tight at 3)
    ///   Set x = 3/2 => s = 3 (feasible)
    ///   Rounding x to 1 => s = 2 (below lower bound), or x to 2 => s = 4 (above upper bound)
    ///   Rounding picks nearest (either direction) but result is infeasible => None
    #[test]
    fn try_rounding_heuristic_fails_infeasible() {
        let non_basic = vec![
            VarInfo::new(Var::int(0), Owner::NonBasic(0))
                .with_bounds(Bounds::new(Some(rbig!(0).into()), Some(rbig!(10).into()))),
        ];
        let basic = vec![
            VarInfo::new(Var::real(1), Owner::Basic(0))
                .with_bounds(Bounds::new(Some(rbig!(3).into()), Some(rbig!(3).into()))),
        ];
        // s = 2*x
        let equations = vec![vec![rbig!(2)]];
        let ctx = ConvContext::default();
        let mut solver =
            LRASolver::from_eqs(basic, non_basic, equations, ctx, TableauKind::Dense).unwrap();

        // Assign x = 3/2 => s = 3 (exactly at bounds)
        solver.update(0, &QDelta::from(rbig!(3 / 2)));
        assert!(solver.is_valid());

        let result = solver.try_rounding_heuristic();
        assert!(
            result.is_none(),
            "rounding should fail when basic var goes out of bounds"
        );

        // Solver state should be restored
        assert!(solver.is_valid());
    }

    /// Nothing to round: all non-basic integer variables already have integer values.
    #[test]
    fn try_rounding_heuristic_nothing_to_round() {
        let non_basic = vec![
            VarInfo::new(Var::int(0), Owner::NonBasic(0))
                .with_bounds(Bounds::new(Some(rbig!(0).into()), Some(rbig!(10).into()))),
            VarInfo::new(Var::int(1), Owner::NonBasic(1))
                .with_bounds(Bounds::new(Some(rbig!(0).into()), Some(rbig!(10).into()))),
        ];
        let basic = vec![
            VarInfo::new(Var::real(2), Owner::Basic(0))
                .with_bounds(Bounds::new(Some(rbig!(0).into()), Some(rbig!(20).into()))),
        ];
        // s = x + y
        let equations = vec![vec![rbig!(1), rbig!(1)]];
        let ctx = ConvContext::default();
        let mut solver =
            LRASolver::from_eqs(basic, non_basic, equations, ctx, TableauKind::Dense).unwrap();

        // Assign integer values: x = 3, y = 4
        solver.update(0, &QDelta::from(rbig!(3)));
        solver.update(1, &QDelta::from(rbig!(4)));

        let result = solver.try_rounding_heuristic();
        assert!(
            result.is_none(),
            "nothing to round when values are already integral"
        );
    }

    /// Rounding is skipped for variables whose rounded value would violate their own bounds.
    ///   x is integer non-basic with bounds [0, 1]
    ///   Set x = 1/2; floor = 0, ceil = 1 — both in bounds, so rounding proceeds.
    ///   But if bounds are (1/3, 2/3), neither 0 nor 1 is in bounds => skip that variable.
    #[test]
    fn try_rounding_heuristic_skips_out_of_bounds_round() {
        let non_basic =
            vec![
                VarInfo::new(Var::int(0), Owner::NonBasic(0)).with_bounds(Bounds::new(
                    Some(QDelta::from(rbig!(1 / 3))),
                    Some(QDelta::from(rbig!(2 / 3))),
                )),
            ];
        let basic = vec![
            VarInfo::new(Var::real(1), Owner::Basic(0))
                .with_bounds(Bounds::new(Some(rbig!(0).into()), Some(rbig!(10).into()))),
        ];
        // s = x
        let equations = vec![vec![rbig!(1)]];
        let ctx = ConvContext::default();
        let mut solver =
            LRASolver::from_eqs(basic, non_basic, equations, ctx, TableauKind::Dense).unwrap();

        // Assign x = 1/2 — fractional but floor(0) and ceil(1) are both outside [1/3, 2/3]
        solver.update(0, &QDelta::from(rbig!(1 / 2)));

        let result = solver.try_rounding_heuristic();
        assert!(
            result.is_none(),
            "should return None when rounded value is out of variable bounds"
        );
    }

    /// Mixed system: one integer variable needs rounding, one real variable does not.
    ///   Tableau: s = x + y
    ///   x is integer non-basic [0, 10], y is real non-basic [0, 10]
    ///   s is real basic [0, 20]
    ///   Set x = 7/2, y = 5/2 => s = 6
    ///   Only x gets rounded (to 4); y stays at 5/2 since it's real.
    #[test]
    fn try_rounding_heuristic_mixed_int_real() {
        let non_basic = vec![
            VarInfo::new(Var::int(0), Owner::NonBasic(0))
                .with_bounds(Bounds::new(Some(rbig!(0).into()), Some(rbig!(10).into()))),
            VarInfo::new(Var::real(1), Owner::NonBasic(1))
                .with_bounds(Bounds::new(Some(rbig!(0).into()), Some(rbig!(10).into()))),
        ];
        let basic = vec![
            VarInfo::new(Var::real(2), Owner::Basic(0))
                .with_bounds(Bounds::new(Some(rbig!(0).into()), Some(rbig!(20).into()))),
        ];
        // s = x + y
        let equations = vec![vec![rbig!(1), rbig!(1)]];
        let ctx = ConvContext::default();
        let mut solver =
            LRASolver::from_eqs(basic, non_basic, equations, ctx, TableauKind::Dense).unwrap();

        // x = 7/2, y = 5/2
        solver.update(0, &QDelta::from(rbig!(7 / 2)));
        solver.update(1, &QDelta::from(rbig!(5 / 2)));

        let result = solver.try_rounding_heuristic();
        assert!(
            result.is_some(),
            "rounding should succeed for the integer variable"
        );

        let assg = result.unwrap();
        let x_val = assg.get(&Var::int(0)).unwrap();
        assert!(x_val.is_int(), "integer variable x should be rounded");
        // 7/2 is equidistant from 3 and 4; the implementation picks floor when tied
        assert!(*x_val == rbig!(3), "7/2 rounds to floor (3) on tie");
    }

    // ─── try_unit_cube_test tests ───────────────────────────────────────────────

    /// Unit cube test succeeds:
    ///   Tableau: s1 = x + y, s2 = x - y
    ///   x, y are integer non-basic with bounds [0, 10]
    ///   s1 is integer basic with bounds [0, 20]
    ///   s2 is integer basic with bounds [-10, 10]
    ///
    ///   |A_1|_1 = |1| + |1| = 2, half = 1, tightened s1 bounds: [1, 19]
    ///   |A_2|_1 = |1| + |-1| = 2, half = 1, tightened s2 bounds: [-9, 9]
    ///
    ///   Initial assignment: x=0, y=0 => s1=0, s2=0.
    ///   After tightening, simplex should find a feasible rational solution
    ///   (e.g. x=5, y=5 => s1=10, s2=0) and rounding produces an integer solution.
    #[test]
    fn try_unit_cube_test_succeeds() {
        let non_basic = vec![
            VarInfo::new(Var::int(0), Owner::NonBasic(0))
                .with_bounds(Bounds::new(Some(rbig!(0).into()), Some(rbig!(10).into()))),
            VarInfo::new(Var::int(1), Owner::NonBasic(1))
                .with_bounds(Bounds::new(Some(rbig!(0).into()), Some(rbig!(10).into()))),
        ];
        let basic = vec![
            VarInfo::new(Var::int(2), Owner::Basic(0))
                .with_bounds(Bounds::new(Some(rbig!(0).into()), Some(rbig!(20).into()))),
            VarInfo::new(Var::int(3), Owner::Basic(1))
                .with_bounds(Bounds::new(Some(rbig!(-10).into()), Some(rbig!(10).into()))),
        ];
        // s1 = x + y, s2 = x - y
        let equations = vec![vec![rbig!(1), rbig!(1)], vec![rbig!(1), rbig!(-1)]];
        let ctx = ConvContext::default();
        let mut solver =
            LRASolver::from_eqs(basic, non_basic, equations, ctx, TableauKind::Dense).unwrap();

        // Solve first to get a feasible assignment
        // let result = solver.solve().unwrap().decision;
        // assert!(matches!(result, SolverDecision::FEASIBLE(_)));

        let result = solver.try_unit_cube_test().unwrap();
        assert!(result.is_some(), "unit cube test should succeed");

        let assg = result.unwrap();
        // All variables should have integer values
        for (var, val) in assg.iter() {
            assert!(
                val.is_int(),
                "variable {:?} should have integer value, got {}",
                var,
                val
            );
        }

        // Verify the tableau equations hold: s1 = x + y, s2 = x - y
        let x = assg.get(&Var::int(0)).unwrap();
        let y = assg.get(&Var::int(1)).unwrap();
        let s1 = assg.get(&Var::int(2)).unwrap();
        let s2 = assg.get(&Var::int(3)).unwrap();
        assert_eq!(*s1, x + y);
        assert_eq!(*s2, x - y);

        // Verify bounds
        assert!(*x >= rbig!(0) && *x <= rbig!(10));
        assert!(*y >= rbig!(0) && *y <= rbig!(10));
        assert!(*s1 >= rbig!(0) && *s1 <= rbig!(20));
        assert!(*s2 >= rbig!(-10) && *s2 <= rbig!(10));

        // Solver state should be restored after cube test
        assert!(solver.is_valid());
    }

    /// Unit cube test fails because tightened bounds make the system infeasible:
    ///   Tableau: s = 3*x + 3*y
    ///   x, y are integer non-basic and unbounded
    ///   s is integer basic with bounds [5, 7]
    ///
    ///   |A_1|_1 = |3| + |3| = 6, half = 3
    ///   Tightened s bounds: [5+3, 7-3] = [8, 4] which is empty (8 > 4)
    ///   So the cube test should immediately detect trivial infeasibility.
    #[test]
    fn try_unit_cube_test_fails_tight_bounds() {
        let non_basic = vec![
            VarInfo::new(Var::int(0), Owner::NonBasic(0)),
            VarInfo::new(Var::int(1), Owner::NonBasic(1)),
        ];
        let basic = vec![
            VarInfo::new(Var::int(2), Owner::Basic(0))
                .with_bounds(Bounds::new(Some(rbig!(5).into()), Some(rbig!(7).into()))),
        ];
        // s = 3*x + 3*y
        let equations = vec![vec![rbig!(3), rbig!(3)]];
        let ctx = ConvContext::default();
        let mut solver =
            LRASolver::from_eqs(basic, non_basic, equations, ctx, TableauKind::Dense).unwrap();

        // Solve first to get a feasible assignment

        let result = solver.try_unit_cube_test().unwrap();
        assert!(
            result.is_none(),
            "unit cube test should fail when tightened bounds are empty"
        );

        // Solver state should be restored
        assert!(solver.is_valid());
    }

    /// Unit cube test fails because the tightened system is infeasible (not trivially, but
    /// via simplex):
    ///   Tableau: s1 = 2*x, s2 = 2*y
    ///   x is integer non-basic with bounds [0, 3]
    ///   y is integer non-basic with bounds [0, 3]
    ///   s1 is integer basic with bounds [5, 6]
    ///   s2 is integer basic with bounds [5, 6]
    ///
    ///   |A_1|_1 = 2, half = 1, tightened s1 bounds: [6, 5] => trivially infeasible
    ///
    ///   Even though the original system is feasible (x=3, y=3 => s1=6, s2=6),
    ///   the tightened system has no solution.
    #[test]
    fn try_unit_cube_test_fails_simplex_infeasible() {
        let non_basic = vec![
            VarInfo::new(Var::int(0), Owner::NonBasic(0))
                .with_bounds(Bounds::new(Some(rbig!(0).into()), Some(rbig!(3).into()))),
            VarInfo::new(Var::int(1), Owner::NonBasic(1))
                .with_bounds(Bounds::new(Some(rbig!(0).into()), Some(rbig!(3).into()))),
        ];
        let basic = vec![
            VarInfo::new(Var::int(2), Owner::Basic(0))
                .with_bounds(Bounds::new(Some(rbig!(5).into()), Some(rbig!(6).into()))),
            VarInfo::new(Var::int(3), Owner::Basic(1))
                .with_bounds(Bounds::new(Some(rbig!(5).into()), Some(rbig!(6).into()))),
        ];
        // s1 = 2*x, s2 = 2*y
        let equations = vec![vec![rbig!(2), rbig!(0)], vec![rbig!(0), rbig!(2)]];
        let ctx = ConvContext::default();
        let mut solver =
            LRASolver::from_eqs(basic, non_basic, equations, ctx, TableauKind::Dense).unwrap();

        let result = solver.try_unit_cube_test().unwrap();
        assert!(result.is_none(), "unit cube test should fail");

        // Solver state should be restored
        assert!(solver.is_valid());
    }

    /// Unit cube test succeeds on a system with unbounded non-basic variables where
    /// pivoting occurs during the initial solve:
    ///
    ///   (-3/2)x + y <= -1/4
    ///   (2/3)x - y <= -1/6
    ///
    ///   Tableau: s1 = (-3/2)x + y, s2 = (2/3)x - y
    ///   x, y are integer non-basic, fully unbounded
    ///   s1 is real basic with upper bound -1/4 (no lower bound)
    ///   s2 is real basic with upper bound -1/6 (no lower bound)
    ///
    ///   The rational relaxation has solution x=1/2, y=1/2 (not integer). Since the feasible
    ///   region grows unboundedly, a unit cube exists inside it and the test succeeds.
    #[test]
    fn try_unit_cube_test_succeeds_unbounded() {
        let non_basic = vec![
            VarInfo::new(Var::int(0), Owner::NonBasic(0)).with_bounds(Bounds::unbounded()),
            VarInfo::new(Var::int(1), Owner::NonBasic(1)).with_bounds(Bounds::unbounded()),
        ];
        let basic = vec![
            // s1 <= -1/4
            VarInfo::new(Var::real(2), Owner::Basic(0))
                .with_bounds(Bounds::new(None, Some(QDelta::from(rbig!(-1 / 4))))),
            // s2 <= -1/6
            VarInfo::new(Var::real(3), Owner::Basic(1))
                .with_bounds(Bounds::new(None, Some(QDelta::from(rbig!(-1 / 6))))),
        ];
        // s1 = (-3/2)x + y, s2 = (2/3)x - y
        let equations = vec![vec![rbig!(-3 / 2), rbig!(1)], vec![rbig!(2 / 3), rbig!(-1)]];
        let ctx = ConvContext::default();
        let mut solver =
            LRASolver::from_eqs(basic, non_basic, equations, ctx, TableauKind::Dense).unwrap();

        let result = solver.try_unit_cube_test().unwrap();
        assert!(
            result.is_some(),
            "unit cube test should succeed for unbounded system"
        );

        let assg = result.unwrap();
        let x = assg.get(&Var::int(0)).unwrap();
        let y = assg.get(&Var::int(1)).unwrap();
        assert!(x.is_int(), "x should be integer, got {}", x);
        assert!(y.is_int(), "y should be integer, got {}", y);

        // Verify original constraints hold:
        // (-3/2)x + y <= -1/4
        let lhs1 = rbig!(-3 / 2) * x + y;
        assert!(
            lhs1 <= rbig!(-1 / 4),
            "constraint 1 violated: {} > -1/4",
            lhs1
        );
        // (2/3)x - y <= -1/6
        let lhs2 = rbig!(2 / 3) * x - y;
        assert!(
            lhs2 <= rbig!(-1 / 6),
            "constraint 2 violated: {} > -1/6",
            lhs2
        );

        assert!(solver.is_valid());
    }

    // ─── incremental add_relation tests (sparse tableau) ─────────────────────────
    //
    // These exercise extending a live, solved tableau with a new slack row, then
    // relaxing the slack's bounds to unbounded on backtrack rather than physically
    // removing the row.

    /// Build a small feasible sparse system with two unbounded non-basic variables and
    /// one bounded slack:
    ///
    ///    |  x  y
    /// ---+-------
    /// s1 |  1  1     2 <= s1        (i.e. x + y >= 2)
    ///
    /// x = Var::real(10), y = Var::real(11), s1 = Var::real(1).
    fn ex_sum_sparse() -> LRASolver {
        let basic =
            vec![VarInfo::new(Var::real(1), Owner::Basic(0)).with_bounds(Bounds::above_of(2))];
        let non_basic = vec![
            VarInfo::new(Var::real(10), Owner::NonBasic(0)), // x, unbounded
            VarInfo::new(Var::real(11), Owner::NonBasic(1)), // y, unbounded
        ];
        let equations = vec![vec![rbig!(1), rbig!(1)]];
        let ctx = ConvContext::default();
        LRASolver::from_eqs(basic, non_basic, equations, ctx, TableauKind::Sparse).unwrap()
    }

    #[test]
    fn add_relation_grows_sparse_tableau() {
        let mut solver = ex_sum_sparse();
        assert!(matches!(
            solver.solve().unwrap().decision,
            SolverDecision::FEASIBLE(_)
        ));

        let nrows_before = solver.tableau.nrows();
        let ncols_before = solver.tableau.ncols();

        // Add s_new = x + y (a second slack over the same, existing, non-basic variables).
        let slack = Var::real(2);
        let rel = Rel::mk_ge(
            vec![Mon::new(1, Var::real(10)), Mon::new(1, Var::real(11))],
            0,
        );
        solver.add_relation(rel, slack).unwrap();

        // One new row, no new columns (x, y already present).
        assert_eq!(solver.tableau.nrows(), nrows_before + 1);
        assert_eq!(solver.tableau.ncols(), ncols_before);

        // Slack is basic and owns the new row.
        let idx = *solver.var_to_idx.get(&slack).unwrap();
        let new_row = solver.variables[idx].is_basic().expect("slack should be basic");
        assert_eq!(new_row, nrows_before);

        // β(slack) == β(x) + β(y).
        let x_val = solver.variables[solver.non_basic[0]].val.clone();
        let y_val = solver.variables[solver.non_basic[1]].val.clone();
        assert_eq!(solver.variables[idx].val, &x_val + &y_val);

        // Slack is unbounded and the check-invariant holds immediately after add.
        assert!(solver.variables[idx].is_totally_unbounded());
        assert!(solver.is_valid());
    }

    #[test]
    fn add_relation_substitutes_basic_var() {
        // Use the ex_5_6 system with an extensible tableau, then pivot so an original
        // variable (x) becomes basic.
        let basic = vec![
            VarInfo::new(Var::real(1), Owner::Basic(0)).with_bounds(Bounds::above_of(2)),
            VarInfo::new(Var::real(2), Owner::Basic(1)).with_bounds(Bounds::above_of(0)),
            VarInfo::new(Var::real(3), Owner::Basic(2)).with_bounds(Bounds::above_of(1)),
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
        let mut solver =
            LRASolver::from_eqs(basic, non_basic, equations, ctx, TableauKind::Sparse).unwrap();
        assert!(matches!(
            solver.solve().unwrap().decision,
            SolverDecision::FEASIBLE(_)
        ));

        // Ensure x (Var::real(4)) is basic: if not already, pivot s1(row 0) with x(col of x).
        let x_idx = *solver.var_to_idx.get(&Var::real(4)).unwrap();
        if let Some(col) = solver.variables[x_idx].is_non_basic() {
            // pivot the first basic row against x's column (coeff is nonzero in row 0)
            let val = solver.variables[solver.non_basic[col]].val.clone();
            solver.pivot_and_update(0, col, &val).unwrap();
        }
        assert!(
            solver.variables[x_idx].is_basic().is_some(),
            "x should be basic for this test"
        );

        // Add a relation referencing the now-basic x: s_new = x. This exercises the
        // Owner::Basic(r) substitution branch (x is replaced by its row over non-basics).
        let slack = Var::real(6);
        let rel = Rel::mk_ge(vec![Mon::new(1, Var::real(4))], 0);
        solver.add_relation(rel, slack).unwrap();

        // The written row must equal x's row (since s_new = x = <x's row over non-basics>).
        let x_row = solver.variables[x_idx].is_basic().unwrap();
        let slack_idx = *solver.var_to_idx.get(&slack).unwrap();
        let slack_row = solver.variables[slack_idx].is_basic().unwrap();
        for c in 0..solver.non_basic.len() {
            assert_eq!(
                solver.tableau.get(slack_row, c).unwrap(),
                solver.tableau.get(x_row, c).unwrap(),
                "substituted row must match x's row at column {c}"
            );
        }
        // β(slack) == β(x).
        assert_eq!(solver.variables[slack_idx].val, solver.variables[x_idx].val);
        assert!(solver.is_valid());
    }

    #[test]
    fn add_relation_new_variable() {
        let mut solver = ex_sum_sparse();
        assert!(matches!(
            solver.solve().unwrap().decision,
            SolverDecision::FEASIBLE(_)
        ));
        let ncols_before = solver.tableau.ncols();

        // Add s_new = x + z, where z (Var::real(20)) is brand new.
        let z = Var::real(20);
        let slack = Var::real(2);
        let rel = Rel::mk_ge(vec![Mon::new(1, Var::real(10)), Mon::new(1, z)], 0);
        solver.add_relation(rel, slack).unwrap();

        // One new column for z.
        assert_eq!(solver.tableau.ncols(), ncols_before + 1);
        let z_idx = *solver.var_to_idx.get(&z).unwrap();
        assert!(
            solver.variables[z_idx].is_non_basic().is_some(),
            "z should be a new non-basic variable"
        );
        assert!(solver.variables[z_idx].is_totally_unbounded());
        assert!(solver.is_valid());
    }

    #[test]
    fn add_relation_all_zero_row() {
        let mut solver = ex_sum_sparse();
        assert!(matches!(
            solver.solve().unwrap().decision,
            SolverDecision::FEASIBLE(_)
        ));

        // s_new = x - x, which cancels to the all-zero row.
        let slack = Var::real(2);
        let rel = Rel::mk_ge(
            vec![Mon::new(1, Var::real(10)), Mon::new(-1, Var::real(10))],
            0,
        );
        solver.add_relation(rel, slack).unwrap();

        // The new row is all zero and β(slack) == 0.
        let slack_idx = *solver.var_to_idx.get(&slack).unwrap();
        let slack_row = solver.variables[slack_idx].is_basic().unwrap();
        for c in 0..solver.non_basic.len() {
            assert!(solver.tableau.get(slack_row, c).unwrap().is_zero());
        }
        assert_eq!(solver.variables[slack_idx].val, QDelta::ZERO);
        assert!(solver.is_valid());

        // Asserting slack >= 1 makes the (stuck-at-0) slack infeasible with no valid pivot.
        assert_eq!(solver.assert_lower(&slack, &1i32.into()).unwrap(), None);
        assert!(matches!(
            solver.solve().unwrap().decision,
            SolverDecision::INFEASIBLE(_)
        ));
    }

    #[test]
    fn add_relation_all_zero_row_feasible_bounds() {
        let mut solver = ex_sum_sparse();
        solver.solve().unwrap();
        let slack = Var::real(2);
        let rel = Rel::mk_ge(
            vec![Mon::new(1, Var::real(10)), Mon::new(-1, Var::real(10))],
            0,
        );
        solver.add_relation(rel, slack).unwrap();

        // Bounds [-1, 5] contain 0, so the stuck slack is trivially feasible.
        assert_eq!(solver.assert_lower(&slack, &(-1i32).into()).unwrap(), Some(true));
        assert_eq!(solver.assert_upper(&slack, &5i32.into()).unwrap(), Some(true));
        assert!(matches!(
            solver.solve().unwrap().decision,
            SolverDecision::FEASIBLE(_)
        ));
    }

    /// Assert a bound on a freshly added slack, let simplex pivot the slack out of the
    /// basis, then backtrack — the slack's bounds must relax to (−∞, +∞) with no
    /// linear-algebra work, and the solver must land in a valid state even though the
    /// slack is now non-basic.
    #[test]
    fn add_relation_pivot_then_backtrack_relaxes_slack() {
        let mut solver = ex_sum_sparse();
        assert!(matches!(
            solver.solve().unwrap().decision,
            SolverDecision::FEASIBLE(_)
        ));

        // Add s_new = x + y and register it, then take the backtrack snapshot AFTER the add
        // (the intended DPLL(T) order: the snapshot includes the slack).
        let slack = Var::real(2);
        let rel = Rel::mk_ge(
            vec![Mon::new(1, Var::real(10)), Mon::new(1, Var::real(11))],
            0,
        );
        solver.add_relation(rel, slack).unwrap();
        assert!(solver.is_valid());
        let slack_idx = *solver.var_to_idx.get(&slack).unwrap();
        assert!(solver.variables[slack_idx].is_basic().is_some());

        let level = solver.set_backtrack();

        // Assert slack >= 5. The slack starts basic at β = β(x)+β(y) = 0 < 5, so simplex must
        // pivot it against an unbounded non-basic (x or y) to satisfy the bound.
        assert_eq!(solver.assert_lower(&slack, &5i32.into()).unwrap(), None);
        assert!(matches!(
            solver.solve().unwrap().decision,
            SolverDecision::FEASIBLE(_)
        ));
        assert!(
            solver.variables[slack_idx].is_non_basic().is_some(),
            "slack should have drifted to non-basic via the feasibility pivot"
        );

        // Backtrack: the slack's lower bound (previously None) is restored, i.e. relaxed to -inf.
        solver.backtrack(level);
        assert!(
            solver.variables[slack_idx].is_totally_unbounded(),
            "backtrack must relax the popped slack to (-inf, +inf)"
        );
        // Pivots are NOT undone — the slack is still non-basic.
        assert!(solver.variables[slack_idx].is_non_basic().is_some());
        // ...yet the check-invariant holds, with zero linear algebra on the backtrack path.
        assert!(solver.is_valid());
    }

    /// Regression guard for the `restore_assignment` robustness fix: set the backtrack point
    /// BEFORE `add_relation`, then assert / solve (pivot) / backtrack past the add. The snapshot
    /// does not contain the slack, but recomputing basics from restored non-basics keeps the
    /// solver valid.
    #[test]
    fn add_relation_before_backtrack_gap() {
        let mut solver = ex_sum_sparse();
        assert!(matches!(
            solver.solve().unwrap().decision,
            SolverDecision::FEASIBLE(_)
        ));

        // Snapshot BEFORE adding the relation.
        let level = solver.set_backtrack();

        let slack = Var::real(2);
        let rel = Rel::mk_ge(
            vec![Mon::new(1, Var::real(10)), Mon::new(1, Var::real(11))],
            0,
        );
        solver.add_relation(rel, slack).unwrap();
        assert_eq!(solver.assert_lower(&slack, &5i32.into()).unwrap(), None);
        assert!(matches!(
            solver.solve().unwrap().decision,
            SolverDecision::FEASIBLE(_)
        ));

        // Backtrack past the add. The slack post-dates the snapshot; restore_assignment must
        // still leave the solver in a consistent state.
        solver.backtrack(level);
        assert!(solver.is_valid());
    }

    /// A feasible system is checked, then a new relation is added whose asserted bound makes
    /// the system infeasible; backtracking over the assertion must return the solver to a
    /// feasible state.
    #[test]
    fn add_relation_infeasible_then_backtrack_feasible() {
        // ex_sum_sparse: s1 = x + y with s1 >= 2, x/y unbounded.
        let mut solver = ex_sum_sparse();
        assert!(matches!(
            solver.solve().unwrap().decision,
            SolverDecision::FEASIBLE(_)
        ));

        // Add s_new = x + y (the same combination as s1), then snapshot.
        let slack = Var::real(2);
        let rel = Rel::mk_le(
            vec![Mon::new(1, Var::real(10)), Mon::new(1, Var::real(11))],
            0,
        );
        solver.add_relation(rel, slack).unwrap();
        assert!(solver.is_valid());

        let level = solver.set_backtrack();

        // Assert s_new <= 1. Since s_new = x + y = s1 and s1 >= 2, this is infeasible.
        assert_eq!(solver.assert_upper(&slack, &1i32.into()).unwrap(), None);
        assert!(matches!(
            solver.solve().unwrap().decision,
            SolverDecision::INFEASIBLE(_)
        ));

        // Backtracking relaxes the s_new bound; the system is feasible again.
        solver.backtrack(level);
        assert!(solver.variables[*solver.var_to_idx.get(&slack).unwrap()].is_totally_unbounded());
        assert!(matches!(
            solver.solve().unwrap().decision,
            SolverDecision::FEASIBLE(_)
        ));
        assert!(solver.is_valid());
    }
}
