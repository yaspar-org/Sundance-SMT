// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Linear integer and real arithmetic solver
//!
//! The [LIRASolver] is a wrapper around [LRASolver] which manages solver state for mixed
//! integer and real arithmetic problems.

use dashu::{Integer, Rational};
use slotmap;

use crate::arithmetic::lia::bounds::Bounds;
use crate::arithmetic::lia::config::SolverConfig;
use crate::arithmetic::lia::lra_solver::LRASolver;
use crate::arithmetic::lia::qdelta::QDelta;
use crate::arithmetic::lia::solver_result::{
    Assignment, Conflict, SolverDecision, SolverResult, SolverReturn,
};
use crate::arithmetic::lia::stats::Stats;
use crate::arithmetic::lia::variables::{Var, VarType};
use crate::debug_println;

// ---- New Implementation

// pointer to a BrtNode in the slotmap
type K = slotmap::DefaultKey;

/// Represents branching an integer variable
#[derive(Debug)]
struct Branch {
    var: Var,                // variable branched on
    bounds: Bounds<Integer>, // new bounds for `var`
}

/// Represents action to take on at an active node before invoking the LRASolver
#[derive(Debug)]
enum BrtAction {
    // no bound assertions needed before LRA solve
    NoOp,
    // variable choice and bound assertions to make before LRA solve
    BranchTo(Branch),
}

/// A node is
/// - active: Q-feasibility is unknown and we have not branched yet
/// - branched: the node is Q-feasible, but some int variable was assigned a non-int value
///   the node is branched on that variable
/// - pruned: the node is proved to be mixed-infeasible with given set of conflict variables
#[derive(Debug)]
enum BrtNodeState {
    // BrtNode that has not yet been LRA solved; setup data included
    Active(BrtAction),
    // branched node: left and right point to child nodes which may be in any state
    Branched(Var, /* left node */ K, /* right node */ K),
    // pruned node: BnB has proven the problem at this node is UNSAT and the [Conflict]
    // contains a subset of the asserted slack variable bounds that explain it
    Pruned(Conflict<Var>),
}

#[derive(Debug)]
struct BrtNode {
    // node's bracktrack level
    level: Option<usize>,
    // node's state
    state: BrtNodeState,
    // pointer to node's parent; root has None
    parent: Option<K>,
}

/// Structure for exploring a branching tree starting from an active root node
#[derive(Debug)]
struct BrtExplorer {
    root_k: K,
    arena: slotmap::SlotMap<K, BrtNode>,
    active: Vec<K>,
}

impl BrtExplorer {
    pub fn new(root: BrtNode) -> Self {
        let mut arena = slotmap::SlotMap::new();
        let root_k = arena.insert(root);
        Self {
            root_k,
            arena,
            active: vec![root_k],
        }
    }

    /// Starting at a node, resolve conflicts upward in the branching tree until
    /// no further resolutions are possible.
    ///
    /// To resolve conflicts upwards means to look at the parent of `start` and its
    /// children. If the other child's state is Pruned(C_1) and `start`'s state is
    /// Pruned(C_2) then we change the parent's state to Pruned(res(C_1, C2))
    ///
    /// Returns the backtrack level corresponding to the node where resolution stops. This
    /// level needs to be backtracked to at the call site after resolution.
    ///
    /// TODO: lira_solver::resolve: clean up debug statements
    fn resolve(&mut self, start_k: K) -> usize {
        let mut current_k = start_k;
        while let Some(parent_k) = self.arena[current_k].parent {
            // Current state
            let mut current_conflict = match &self.arena[current_k].state {
                BrtNodeState::Active(_) | BrtNodeState::Branched(_, _, _) => break,
                BrtNodeState::Pruned(c) => c.clone(), // TODO: resolve: cloning conflicts at every node is expensive
            };
            debug_println!(
                15,
                0,
                "lia::lira_solver::resolve: current node is pruned and has conflicts {:?}",
                current_conflict
            );
            debug_println!(
                15,
                0,
                "lia::lira_solver::resolve: parent node {:?}",
                self.arena[parent_k]
            );

            // Parent state
            match self.arena[parent_k].state {
                BrtNodeState::Branched(var, left_k, right_k) => {
                    debug_println!(
                        15,
                        0,
                        "lia::lira_solver::resolve: parent node is branched on {var}"
                    );
                    let other_k = if current_k == left_k { right_k } else { left_k };
                    let other_conflict = match &self.arena[other_k].state {
                        // the other branch hasn't been fully explored yet
                        BrtNodeState::Active(_) => {
                            debug_println!(
                                15,
                                0,
                                "lia::lira_solver::resolve: other branch is still active; ending conflict resolution"
                            );
                            return self.arena[parent_k].level.unwrap(); // safe b/c parent is branched, not active
                        }
                        BrtNodeState::Branched(other_var, _, _) => {
                            debug_assert!(var == *other_var);
                            debug_println!(
                                15,
                                0,
                                "lia::lira_solver::resolve: other branch is still branched; ending conflict resolution"
                            );
                            return self.arena[parent_k].level.unwrap(); // safe b/c parent is branched, not active
                        }
                        // the other branch is fully explored and pruned
                        BrtNodeState::Pruned(c) => c,
                    };
                    debug_println!(
                        15,
                        0,
                        "lia::lira_solver::resolve: other branch is pruned and has conflicts {:?}",
                        other_conflict
                    );
                    current_conflict = current_conflict.resolve(var, other_conflict);
                    debug_println!(
                        15,
                        0,
                        "lia::lira_solver::resolve: after resolution conflicts are {:?}",
                        current_conflict
                    );
                    self.arena[parent_k].state = BrtNodeState::Pruned(current_conflict);
                }
                // If the parent is Active or Pruned, it's a bug
                // there's nothing to resolve
                BrtNodeState::Pruned(_) | BrtNodeState::Active(_) => {
                    unreachable!("lia::lira_solver::resolve: unexpected active/pruned parent")
                }
            }
            current_k = parent_k;
        }
        self.arena[current_k].level.unwrap() // safe b/c final node is guaranteed not to be active
    }
}

/// Linear integer and real arithmetic solver
#[derive(Debug)]
pub struct LIRASolver {
    /// The underlying LRA solver
    lra_solver: LRASolver,
    /// Stack of variable bounds for tracking during solving
    explorer: BrtExplorer,
    /// Solver configuration
    config: SolverConfig,
    /// Runtime statistics
    stats: Stats,
}

impl LIRASolver {
    /// Create a new LIRASolver with the given LRASolver
    pub fn new(lra_solver: LRASolver, config: SolverConfig) -> Self {
        let root = BrtNode {
            level: Some(0usize),
            state: BrtNodeState::Active(BrtAction::NoOp),
            parent: None,
        };
        Self {
            lra_solver,
            explorer: BrtExplorer::new(root),
            config,
            stats: Stats::new(),
        }
    }

    // Setup LRA solver state for the active branch pointed to by `current_k`.
    //
    // Returns the backtracking level of the active node's parent.
    fn setup_active(&mut self, current_k: K) -> SolverResult<()> {
        let current = self
            .explorer
            .arena
            .get_mut(current_k)
            .expect("invalid node key {current_k:?}");
        // `new_current_state` is optionally updated below to avoid needing to modify
        // current.state in the match where &mut current.state is borrowed
        let mut new_current_state: Option<BrtNodeState> = None;
        let mut new_bt_level: Option<usize> = None;
        match &current.state {
            BrtNodeState::Active(setup) => {
                match setup {
                    BrtAction::BranchTo(Branch { var, bounds }) => {
                        debug_println!(15, 0, "lia::lira_solver: pushing branch {var} in {bounds}");
                        match (&bounds.lower, &bounds.upper) {
                            (Some(l), None) => {
                                new_bt_level = Some(self.lra_solver.set_backtrack());
                                let ass_res = self
                                    .lra_solver
                                    .assert_lower(var, &QDelta::from(Rational::from(l.clone())))?;
                                if let Some(false) = ass_res {
                                    debug_println!(
                                        15,
                                        0,
                                        "lia::lira_solver: (assert_lower) branch is trivially INFEASIBLE"
                                    );
                                    // conflict is the single variable asserted upon
                                    new_current_state = Some(BrtNodeState::Pruned(
                                        vec![*var].into_iter().collect(),
                                    ));
                                }
                            }
                            (None, Some(u)) => {
                                new_bt_level = Some(self.lra_solver.set_backtrack());
                                let ass_res = self
                                    .lra_solver
                                    .assert_upper(var, &QDelta::from(Rational::from(u.clone())))?;
                                if let Some(false) = ass_res {
                                    // branch is trivially UNSAT
                                    debug_println!(
                                        15,
                                        0,
                                        "lia::lira_solver: (assert_upper) branch is trivially INFEASIBLE"
                                    );
                                    // conflict is the single variable asserted upon
                                    new_current_state = Some(BrtNodeState::Pruned(
                                        vec![*var].into_iter().collect(),
                                    ));
                                }
                            }
                            _ => {
                                unreachable!(
                                    "branch_and_bound: only one bound direction should be set"
                                )
                            }
                        }
                    }
                    _ => {
                        // no-op
                    }
                }
            }
            _ => unreachable!("unexpected node state"),
        };

        // Now that we can release &mut current, update it and other fields in &mut self
        if let Some(c) = new_current_state {
            current.state = c;
            if matches!(current.state, BrtNodeState::Pruned(_)) {
                // in case new state is `Pruned`, resolve conflicts before continuing Resolution
                // includes backtracking to the LRASolver state at the final node visited
                let res_level = self.explorer.resolve(current_k);
                self.lra_solver.backtrack(res_level);
            }
        }
        let current = self // get current again to avoid 2x mut borrow
            .explorer
            .arena
            .get_mut(current_k)
            .expect("invalid node key {current_k:?}");
        if current.level.is_none() {
            current.level = new_bt_level; // replaces the initial None in the solve SAT case
        }
        Ok(())
    }

    /// Solve a mixed-integer system.
    ///
    /// First solves the relaxed rational system. If feasible with all integer variables
    /// assigned integer values, returns immediately. Otherwise attempts heuristics
    /// (rounding, unit cube test) before falling back to branch-and-bound.
    pub fn solve(&mut self) -> SolverResult<SolverReturn> {
        debug_println!(21, 0, "lia::lira_solver: starting LIRASolver");

        // Try unit cube test
        debug_println!(21, 0, "lia::lira_solver::solve: trying the unit cube test");
        if let Some(cube_assg) = self.try_unit_cube_test()? {
            debug_println!(21, 0, "lia::lira_solver::solve: unit cube test succeeded");
            return Ok(SolverReturn::new(
                SolverDecision::FEASIBLE(cube_assg),
                self.stats.clone(),
            ));
        }

        // Solve the rational relaxation
        debug_println!(
            21,
            0,
            "lia::lira_solver::solve: solving the rational relaxation"
        );
        let ret = self.lra_solver.solve()?;
        self.stats.combine(&ret.stats);

        match ret.decision {
            SolverDecision::INFEASIBLE(cs) => Ok(SolverReturn::new(
                SolverDecision::INFEASIBLE(cs),
                self.stats.clone(),
            )),
            SolverDecision::UNKNOWN => Ok(SolverReturn::new(
                SolverDecision::UNKNOWN,
                self.stats.clone(),
            )),
            SolverDecision::FEASIBLE(assg) => {
                debug_println!(
                    21,
                    0,
                    "lia::lira_solver::solve: rational relaxation is feasible with assignment:"
                );
                debug_println!(21, 0, "{assg}");
                // Check if all integer variables already have integer assignments
                if self.find_next_int_var().is_none() {
                    return Ok(SolverReturn::new(
                        SolverDecision::FEASIBLE(assg),
                        self.stats.clone(),
                    ));
                }

                // Try rounding heuristic
                debug_println!(21, 0, "lia::lira_solver::solve: trying rounding heuristic");
                if let Some(rounded_assg) = self.try_rounding_heuristic() {
                    debug_println!(
                        21,
                        0,
                        "lia::lira_solver::solve: rounding heuristic succeeded"
                    );
                    return Ok(SolverReturn::new(
                        SolverDecision::FEASIBLE(rounded_assg),
                        self.stats.clone(),
                    ));
                }

                // Fall back to branch-and-bound
                self.branch_and_bound()
            }
        }
    }

    /// Solve a mixed-integer system using branch-and-bound
    fn branch_and_bound(&mut self) -> SolverResult<SolverReturn> {
        debug_println!(21, 0, "lia::lira_solver: starting branch-and-bound");

        while let Some(current_k) = self.explorer.active.pop() {
            debug_println!(
                21,
                0,
                "lia::lira_solver::solve: pop & setup node {:?}",
                self.explorer.arena[current_k]
            );
            self.setup_active(current_k)?;
            // Handle pruning that can happen during setup phase
            if matches!(
                self.explorer.arena[current_k].state,
                BrtNodeState::Pruned(_)
            ) {
                // backtracking has already happened in (resolution in) the setup phase
                continue;
            }

            // Solve the rational system
            debug_println!(21, 0, "lia::lira_solver: solving over Q");
            let ret = self.lra_solver.solve()?;

            // Update stats: LRASolver::solve bumps num_lra_solve by 1
            self.stats.combine(&ret.stats);

            // Depending on current solver config, stop early and return UNKNOWN if we have
            // made too many LRA solver calls.
            if let Some(max) = self.config.max_lra_solve_calls
                && self.stats.num_lra_solve > max
            {
                debug_println!(
                    21,
                    0,
                    "lia::lira_solver: max LRASolver calls reached, returning UNKNOWN"
                );
                return Ok(SolverReturn::new(
                    SolverDecision::UNKNOWN,
                    self.stats.clone(),
                ));
            }

            match ret.decision {
                SolverDecision::INFEASIBLE(cs) => {
                    debug_println!(
                        15,
                        0,
                        "lia::lira_solver: INFEASIBLE, pruning node and backtracking"
                    );
                    self.explorer.arena[current_k].state = BrtNodeState::Pruned(cs);
                    let level = self.explorer.resolve(current_k);
                    // Resolve optionally returns a final level to backtrack to; this
                    // may jump several levels back, not just to the parent.
                    debug_println!(
                        15,
                        0,
                        "lia::lira_solver: after resolution, backtracking to level {level}"
                    );
                    self.lra_solver.backtrack(level)
                }
                SolverDecision::FEASIBLE(assg) => {
                    debug_println!(
                        15,
                        0,
                        "lia::lira_solver: FEASIBLE, checking for non-integral assignments"
                    );
                    // identify the first integer type variable whose assigned value is not integral
                    let (x, val) = match self.find_next_int_var() {
                        None => {
                            return Ok(SolverReturn::new(
                                SolverDecision::FEASIBLE(assg),
                                self.stats.clone(),
                            ));
                        } // rational solution meets all type constraints
                        Some((x, val)) => {
                            debug_println!(
                                15,
                                0,
                                "lia::lira_solver: FEASIBLE, {x} is not assigned an integer: {val}"
                            );
                            (x, val)
                        }
                    };

                    // (x : Int) is assigned a non-integer solution, so we branch
                    debug_println!(
                        15,
                        0,
                        "lia::lira_solver: branching on var {x} with current assignment {val}"
                    );
                    let lower_branch = Bounds::below_of(val.floor()); // new upper bound for `x` in branch 1
                    let upper_branch = Bounds::above_of(val.ceil()); // new lower bound for `x` in branch 2
                    debug_println!(
                        15,
                        0,
                        "lia::lira_solver: lower branch: {x} in {lower_branch}, upper branch: {x} in {upper_branch}"
                    );

                    // construct new lower and upper nodes to explore, add them to the tree
                    // and the active stack
                    //
                    // Lower:
                    let lower_node = BrtNode {
                        level: None,
                        state: BrtNodeState::Active(BrtAction::BranchTo(Branch {
                            var: x,
                            bounds: lower_branch,
                        })),
                        parent: Some(current_k),
                    };
                    let lower_node_k = self.explorer.arena.insert(lower_node);
                    self.explorer.active.push(lower_node_k);

                    // Upper:
                    let upper_node = BrtNode {
                        level: None,
                        state: BrtNodeState::Active(BrtAction::BranchTo(Branch {
                            var: x,
                            bounds: upper_branch,
                        })),
                        parent: Some(current_k),
                    };
                    let upper_node_k = self.explorer.arena.insert(upper_node);
                    self.explorer.active.push(upper_node_k);
                    self.explorer.arena[current_k].state =
                        BrtNodeState::Branched(x, lower_node_k, upper_node_k);
                }
                SolverDecision::UNKNOWN => {
                    unreachable!("lra_solver decision cannot be UNKNOWN after solve")
                }
            }
        }
        // active is now empty

        // At this point, every node should be pruned and all conflicts resolved
        // up to the root node. The initial linear mixed integer problem is infeasible.
        let root_k = self.explorer.root_k;
        let root = self
            .explorer
            .arena
            .get(root_k)
            .unwrap_or_else(|| panic!("invalid root key {root_k:?}"));
        match &root.state {
            BrtNodeState::Pruned(conflict) => Ok(SolverReturn::new(
                SolverDecision::INFEASIBLE(conflict.clone()),
                self.stats.clone(),
            )),
            state => unreachable!("invalid final root node state {state:?}"),
        }
    }

    /// Get a reference to the underlying LRASolver
    pub fn lra_solver(&self) -> &LRASolver {
        &self.lra_solver
    }

    /// Get a mutable reference to the underlying LRASolver
    pub fn lra_solver_mut(&mut self) -> &mut LRASolver {
        &mut self.lra_solver
    }

    /// Find the first integer variable whose currently assigned value is
    /// not integral and return it along with its current assignment.
    fn find_next_int_var(&self) -> Option<(Var, Rational)> {
        // Get the current model (assignment of variables)
        let model = self.lra_solver.get_rational_model()?;

        // Iterate through the variables in the model
        //
        // TODO: Maintain a separate list of Integer type variables
        for (var, val) in model.iter() {
            // Check if the variable is of integer type
            if var.typ == VarType::Int {
                // Check if the value is not an integer
                if !val.is_int() {
                    return Some((*var, val.clone()));
                }
            }
        }

        // No integer variables with non-integer values found
        None
    }

    /// Attempt to round non-basic integer variables to the nearest integer value.
    /// Delegates to the underlying LRASolver.
    fn try_rounding_heuristic(&mut self) -> Option<Assignment<Var>> {
        self.lra_solver.try_rounding_heuristic()
    }

    /// Attempt the unit cube test. Delegates to the underlying LRASolver.
    fn try_unit_cube_test(&mut self) -> SolverResult<Option<Assignment<Var>>> {
        self.lra_solver.try_unit_cube_test()
    }
}

/// The tests in this module were ported from integration tests. As such, they use the frontend
/// `solve_smtlib` and solver construction methods rather than the LIRASolver methods
/// directly.
#[cfg(test)]
mod tests {
    use dashu::{Rational, rbig};

    use crate::arithmetic::lia::config::SolverConfig;
    use crate::arithmetic::lia::frontend::{smt_to_lra_solver, solve_smtlib};
    use crate::arithmetic::lia::lira_solver::LIRASolver;
    use crate::arithmetic::lia::solver_result::SolverDecision;
    use crate::arithmetic::lia::solver_result_api::SolverDecisionApi;

    /// Execute branch and bound manually on an UNSAT QF_LIA problem
    #[test]
    fn manual_branch_and_bound_triangle() {
        // If x, y are Real this problem is FEASBILE, ex. model {x := 1/3, y := 1/3}
        let smt_input = r#"
        (set-logic QF_LIRA)
        (declare-fun x () Real)
        (declare-fun y () Int)
        (assert (>= (to_real y) x))                  ; y >= x
        (assert (>= x (/ (to_real 1) (to_real 3))))  ; x >= 1/3
        (assert (<= (to_real y) (/ (to_real 2) (to_real 3))))  ; y <= 2/3
            "#;
        let mut solver = smt_to_lra_solver(smt_input, &SolverConfig::default())
            .expect("Failed to create LRA solver");
        let ass = match solver.solve().unwrap().decision {
            SolverDecision::FEASIBLE(ass) => ass,
            _ => unreachable!(),
        };

        // select an integer variable whose assignment is not an integer
        let y_var = solver.get_var("y").unwrap();
        let y_val = ass.get(&y_var).unwrap();
        assert!(y_val >= &rbig!(1 / 3) && y_val <= &rbig!(2 / 3));
        let y0 = y_val;

        // for y to be integral it must either be below this value
        let lower_branch_0 = Rational::from(y0.floor());
        // or above this value
        let upper_branch_0 = Rational::from(y0.ceil());

        // consider original problem S_0 branched and new problems
        // {S_0, y <= lower_branch_0}, {S_0, y >= upper_branch_0} active

        let level_0 = solver.set_backtrack();

        assert_eq!(
            solver
                // the new lower branch corresponds to a tighter upper bound
                .assert_upper(&y_var, &lower_branch_0.into())
                .expect("assert_upper failed"),
            None // satisfiability unknown
        );
        // lower branch is infeasible
        assert!(matches!(
            solver.solve().unwrap().decision,
            SolverDecision::INFEASIBLE(_)
        ));

        solver.backtrack(level_0);

        assert_eq!(
            solver
                // the new lower branch corresponds to a tighter upper bound
                .assert_lower(&y_var, &upper_branch_0.into())
                .expect("assert_lower failed"),
            None // satisfiability unknown
        );
        // upper branch is infeasible
        assert!(matches!(
            solver.solve().unwrap().decision,
            SolverDecision::INFEASIBLE(_)
        ));

        // all branches are pruned, therefor the problem is mixed integer infeasible
        // -> in the LIRA solver we would now backtrack to `level_0` and set solver state
        //    to UNSAT
    }

    // Repeat the manual test above but using the actual LIRA solver branch-and-bound implementation
    #[test]
    fn branch_and_bound_triangle() {
        // If x, y are Real this problem is FEASBILE, ex. model {x := 1/3, y := 1/3}
        let smt_input = r#"
        (set-logic QF_LIRA)
        (declare-fun x () Real)
        (declare-fun y () Int)
        (assert (>= (to_real y) x))                  ; y >= x
        (assert (>= x (/ (to_real 1) (to_real 3))))  ; x >= 1/3
        (assert (<= (to_real y) (/ (to_real 2) (to_real 3))))  ; y <= 2/3
            "#;
        let lra_solver = smt_to_lra_solver(smt_input, &SolverConfig::default())
            .expect("Failed to create LRA solver");
        let mut lira_solver = LIRASolver::new(lra_solver, SolverConfig::default());
        assert!(matches!(
            lira_solver.solve().unwrap().decision,
            SolverDecision::INFEASIBLE(_)
        ));
    }

    // Repeat the `branch_and_bound_triangle` test as purely LIA
    #[test]
    fn branch_and_bound_triangle_lia() {
        // If x, y are Real this problem is FEASBILE, ex. model {x := 1/3, y := 1/3}
        let smt_input = r#"
        (set-logic QF_LIA)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (>= y x))        ; y >= x
        (assert (>= (* 3 x) 1))  ; 3x >= 1
        (assert (<= (* 3 y) 2))  ; 3y <= 2
            "#;
        let lra_solver = smt_to_lra_solver(smt_input, &SolverConfig::default())
            .expect("Failed to create LRA solver");
        let mut lira_solver = LIRASolver::new(lra_solver, SolverConfig::default());
        assert!(matches!(
            lira_solver.solve().unwrap().decision,
            SolverDecision::INFEASIBLE(_)
        ));
    }

    #[test]
    fn unsat_2_sat_branch_and_bound() {
        // Encode the 2-variable 2-SAT problem:
        // (x y) ∧ (-x y) ∧ (x -y) ∧ (-x -y)
        let smt_input = r#"
        (set-logic QF_LIA)
        (declare-fun x () Int)
        (declare-fun y () Int)

        (assert (>= x 0))
        (assert (<= x 1))
        (assert (>= y 0))
        (assert (<= y 1))

        (assert (>= (+      x       y)  1))
        (assert (>= (+ (- 1 x)      y)  1))
        (assert (>= (+      x  (- 1 y)) 1))
        (assert (>= (+ (- 1 x) (- 1 y)) 1))
        (check-sat)
        "#;

        let lra_solver = smt_to_lra_solver(smt_input, &SolverConfig::default())
            .expect("Failed to create LRA solver");
        let mut lira_solver = LIRASolver::new(lra_solver, SolverConfig::default());

        // Assert that the system is INFEASIBLE
        assert!(matches!(
            lira_solver.solve().unwrap().decision,
            SolverDecision::INFEASIBLE(_)
        ));
    }

    /// Solve an UNSAT 3-SAT problem enoded using QF_LIA.
    ///
    /// (𝑥∨𝑦∨𝑧)∧(𝑥∨𝑦∨¬𝑧)∧(𝑥∨¬𝑦∨𝑧)∧(𝑥∨¬𝑦∨¬𝑧)∧(¬𝑥∨𝑦∨𝑧)∧(¬𝑥∨𝑦∨¬𝑧)∧(¬𝑥∨¬𝑦∨𝑧)∧(¬𝑥∨¬𝑦∨¬𝑧)
    ///
    /// A positive literal `x`` is encoded as an integer variable with coefficient 1 and bounds [0, 1].
    /// ¬x is encoded as the term (1-x). A disjunction of literals is encoded as the sum of the
    /// literals. Each encoded clause term is also required to be >= 1, meaning at least one literal
    /// is assigned true.
    ///
    /// For example, (𝑥∨𝑦∨𝑧) should be encoded as x + y + z, whereas the clause (𝑥∨¬𝑦∨𝑧) should be
    /// encoded as x + (1 - y) + z.
    ///
    /// The encoding in this unit test cost $2.61
    #[test]
    fn unsat_3_sat_branch_and_bound() {
        // This encodes the 3-SAT problem:
        // (𝑥∨𝑦∨𝑧)∧(𝑥∨𝑦∨¬𝑧)∧(𝑥∨¬𝑦∨𝑧)∧(𝑥∨¬𝑦∨¬𝑧)∧(¬𝑥∨𝑦∨𝑧)∧(¬𝑥∨𝑦∨¬𝑧)∧(¬𝑥∨¬𝑦∨𝑧)∧(¬𝑥∨¬𝑦∨¬𝑧)
        let smt_input = r#"
        (set-logic QF_LIA)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun z () Int)

        ; Bound all variables to [0, 1]
        (assert (>= x 0))
        (assert (<= x 1))
        (assert (>= y 0))
        (assert (<= y 1))
        (assert (>= z 0))
        (assert (<= z 1))

        ; Clause 1: (x ∨ y ∨ z) encoded as x + y + z >= 1
        (assert (>= (+ x y z) 1))

        ; Clause 2: (x ∨ y ∨ ¬z) encoded as x + y + (1-z) >= 1
        (assert (>= (+ x y (+ 1 (* (- 1) z))) 1))

        ; Clause 3: (x ∨ ¬y ∨ z) encoded as x + (1-y) + z >= 1
        (assert (>= (+ x (+ 1 (* (- 1) y)) z) 1))

        ; Clause 4: (x ∨ ¬y ∨ ¬z) encoded as x + (1-y) + (1-z) >= 1
        (assert (>= (+ x (+ 1 (* (- 1) y)) (+ 1 (* (- 1) z))) 1))

        ; Clause 5: (¬x ∨ y ∨ z) encoded as (1-x) + y + z >= 1
        (assert (>= (+ (+ 1 (* (- 1) x)) y z) 1))

        ; Clause 6: (¬x ∨ y ∨ ¬z) encoded as (1-x) + y + (1-z) >= 1
        (assert (>= (+ (+ 1 (* (- 1) x)) y (+ 1 (* (- 1) z))) 1))

        ; Clause 7: (¬x ∨ ¬y ∨ z) encoded as (1-x) + (1-y) + z >= 1
        (assert (>= (+ (+ 1 (* (- 1) x)) (+ 1 (* (- 1) y)) z) 1))

        ; Clause 8: (¬x ∨ ¬y ∨ ¬z) encoded as (1-x) + (1-y) + (1-z) >= 1
        (assert (>= (+ (+ 1 (* (- 1) x)) (+ 1 (* (- 1) y)) (+ 1 (* (- 1) z))) 1))
        "#;

        let lra_solver = smt_to_lra_solver(smt_input, &SolverConfig::default())
            .expect("Failed to create LRA solver");
        let mut lira_solver = LIRASolver::new(lra_solver, SolverConfig::default());

        // Assert that the system is INFEASIBLE
        assert!(matches!(
            lira_solver.solve().unwrap().decision,
            SolverDecision::INFEASIBLE(_)
        ));
    }

    /// Test from front page of https://lean-lang.org/ showcasing proof automation
    /// In the grind example, the first three hypotheses imply the fourth.
    ///
    /// https://www.desmos.com/calculator/y1wwdqoqle
    #[test]
    fn grind_test_playground() {
        let smt1 = r#"
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= (+ (* 11 x) (* 13 y)) 27))
        (assert (<= (+ (* 11 x) (* 13 y)) 45))
        (assert (>= (- (* 7 x) (* 9 y)) (- 10)))
        (check-sat)
        "#;
        // first 3 constraints are sat
        let result = solve_smtlib(smt1, &SolverConfig::default()).expect("solver failed");
        assert!(matches!(result, SolverDecisionApi::FEASIBLE(_)));

        // all 4 constraints are sat
        let smt2 = smt1.to_string() + "(assert (> (- (* 7 x) (* 9 y)) 4))";
        let result2 = solve_smtlib(&smt2, &SolverConfig::default()).expect("solver failed");
        assert!(matches!(result2, SolverDecisionApi::FEASIBLE(_)));

        // now prove validity
        // let r1 := 11x + 13 y
        //     r2 := 7x - 9y
        //     constraints C1...C4
        //
        // forall (x y: Int) C1 and C2 and C3 ==> C4
        // forall (x y: Int) -(C1 and C2 and C3) or C4
        // negate: exists (x y: Int) (C1 and ... and C3) and (-C4)
        let smt3 = smt1.to_string() + "(assert (not (> (- (* 7 x) (* 9 y)) 4)))";
        let result3 = solve_smtlib(&smt3, &SolverConfig::default()).expect("solver failed");
        assert!(matches!(result3, SolverDecisionApi::INFEASIBLE(_)));
    }

    /// Test from the Lean manual:
    /// https://lean-lang.org/doc/reference/latest/The--grind--tactic/Linear-Arithmetic-Solver/#grind-linarith
    /// Example 1
    #[test]
    fn grind_test_ref_manual_1() {
        let smt = r#"
        (declare-const a Int)
        (declare-const b Int)
        (assert (not (>= (+ (* 2 a) b) (+ b a a))))
        (check-sat)
        "#;
        let result = solve_smtlib(smt, &SolverConfig::default()).expect("solver failed");
        assert!(matches!(result, SolverDecisionApi::INFEASIBLE(_)),);
        if let SolverDecisionApi::INFEASIBLE(conflict) = result {
            assert_eq!(conflict.len(), 1);
        }
    }

    /// Test from the Lean manual:
    /// https://lean-lang.org/doc/reference/latest/The--grind--tactic/Linear-Arithmetic-Solver/#grind-linarith
    /// Example 2
    #[test]
    fn grind_test_ref_manual_2() {
        let smt = r#"
        (declare-const a Int)
        (declare-const b Int)
        (declare-const c Int)
        (assert (= a (+ b c)))
        (assert (<= (* 2 b) c))
        (assert (not (<= (* 2 a) (* 3 c))))
        (check-sat)
        "#;
        let result = solve_smtlib(smt, &SolverConfig::default()).expect("solver failed");
        assert!(matches!(result, SolverDecisionApi::INFEASIBLE(_)),);
        if let SolverDecisionApi::INFEASIBLE(conflict) = result {
            assert_eq!(conflict.len(), 3); // every subset of 2 assertions is feasible
        }
    }

    /// Test from the Lean manual:
    /// https://lean-lang.org/doc/reference/latest/The--grind--tactic/Linear-Arithmetic-Solver/#grind-linarith
    /// Example 3
    ///
    /// This example is infeasible over both ints and reals.
    #[test]
    fn grind_test_ref_manual_3() {
        let smt = r#"
        (declare-const a Real)
        (declare-const b Real)
        (declare-const c Real)
        (declare-const d Real)
        (declare-const e Real)

        ; assertions marked with 'x' are in conflict
        (assert (>= (+ (* 2.0 a) b) 0.0)) ; x
        (assert (>= b 0.0)) ; x
        (assert (>= c 0.0)) ; x
        (assert (>= d 0.0)) ; x
        (assert (>= e 0.0)) ; x
        (assert (>= a (* 3.0 c)))
        (assert (>= c (* 6.0 e)))
        (assert (>= (- d (* 5.0 e)) 0.0))
        (assert (< (+ a b (* 3.0 c) d (* 2.0 e)) 0.0))  ; x
        (check-sat)
        "#;
        let result = solve_smtlib(smt, &SolverConfig::default()).expect("solver failed");
        assert!(matches!(result, SolverDecisionApi::INFEASIBLE(_)),);
        if let SolverDecisionApi::INFEASIBLE(conflict) = result {
            assert_eq!(conflict.len(), 6);
        }

        // Check that the conflict set is actually conflicting.
        // This test may be brittle if conflict computation is not stable.
        let smt_conflict = r#"
        (declare-const a Real)
        (declare-const b Real)
        (declare-const c Real)
        (declare-const d Real)
        (declare-const e Real)

        ; assertions marked with 'x' are in conflict
        (assert (>= (+ (* 2.0 a) b) 0.0)) ; x
        (assert (>= b 0.0)) ; x
        (assert (>= c 0.0)) ; x
        (assert (>= d 0.0)) ; x
        (assert (>= e 0.0)) ; x
        (assert (< (+ a b (* 3.0 c) d (* 2.0 e)) 0.0))  ; x
        (check-sat)
        "#;
        let result = solve_smtlib(smt_conflict, &SolverConfig::default()).expect("solver failed");
        assert!(matches!(result, SolverDecisionApi::INFEASIBLE(_)),);

        // Sanity check that the conflict is minimal; not a proof of such, just
        // removing one constraint b >= 0 and showing feasibility.
        let smt_conflict = r#"
        (declare-const a Real)
        (declare-const b Real)
        (declare-const c Real)
        (declare-const d Real)
        (declare-const e Real)

        ; assertions marked with 'x' are in conflict
        (assert (>= (+ (* 2.0 a) b) 0.0)) ; x
        (assert (>= c 0.0)) ; x
        (assert (>= d 0.0)) ; x
        (assert (>= e 0.0)) ; x
        (assert (< (+ a b (* 3.0 c) d (* 2.0 e)) 0.0))  ; x
        (check-sat)
        "#;
        let result = solve_smtlib(smt_conflict, &SolverConfig::default()).expect("solver failed");
        assert!(matches!(result, SolverDecisionApi::FEASIBLE(_)),);
    }

    // Regression test from https://github.com/yaspar-org/Sundance-SMT/issues/33
    //
    //  b <  0       {       b < 0
    // -b <= 1  -->  { -1 <= b
    // -b <  1       { -1 <  b
    //
    // The first and 3rd constraints are mutually UNSAT.
    #[test]
    fn regresssion_issue_33() {
        let smt = r#"
        (declare-const b Int)
        (assert (< b 0))
        (assert (<= (- b) 1))
        (assert (< (- b) 1))
        (check-sat)
        "#;
        let result = solve_smtlib(smt, &SolverConfig::default()).expect("solver failed");
        assert!(matches!(result, SolverDecisionApi::INFEASIBLE(_)),);
        if let SolverDecisionApi::INFEASIBLE(conflict) = result {
            assert_eq!(conflict.len(), 2);
            // The terms printed here are correct by inspection
            // println!("{conflict:#?}");
        }
    }

    #[test]
    fn regression_issue_30() {
        let smt = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (= (* 2 x) 3))
        (check-sat)
        "#;
        let result = solve_smtlib(smt, &SolverConfig::default()).expect("solver failed");
        assert!(matches!(result, SolverDecisionApi::FEASIBLE(_)),);
        if let SolverDecisionApi::FEASIBLE(assg) = result {
            let (_, val) = assg.iter().next().unwrap();
            assert_eq!(Rational::from(2) * val, Rational::from(3));
        }
    }
}
