// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Linear integer and real arithmetic solver
//!
//! The [LIRASolver] is a wrapper around [LRASolver] which manages solver state for mixed
//! integer and real arithmetic problems.

use dashu::{Integer, Rational};

use crate::arithmetic::lia::config::SolverConfig;
use crate::arithmetic::lia::lra_solver::LRASolver;
use crate::arithmetic::lia::qdelta::QDelta;
use crate::arithmetic::lia::solver_result::{
    Assignment, Conflict, SolverDecision, SolverResult, SolverReturn,
};
use crate::arithmetic::lia::stats::Stats;
use crate::arithmetic::lia::variables::{Var, VarType};
use crate::debug_println;

/// Outcome of exploring one node of the branch-and-bound tree.
///
/// Branch-and-bound is a depth-first search over the tree of integer bound
/// refinements. Each node solves the rational relaxation under the bounds asserted
/// along the path from the root; [`explore`](LIRASolver::explore) returns one of these
/// for every node, and a parent combines its two children's outcomes into its own.
enum NodeOutcome {
    /// A rational assignment satisfying every integrality constraint in scope. The search
    /// short-circuits on the first one found.
    Feasible(Assignment<Var>),
    /// The subtree rooted at this node is infeasible; the [`Conflict`] is a subset of the
    /// asserted bounds (identified by their slack variables) that explains why.
    Pruned(Conflict<Var>),
    /// The search hit a resource limit (LRA-solve budget or maximum depth) before proving
    /// feasibility or infeasibility.
    Unknown,
}

/// Which side of a branch to assert for an integer variable `x` currently sitting at a
/// fractional value `v`. The two sides partition the integers: `x <= floor(v)` or
/// `x >= ceil(v)`, so together they lose no integer solutions.
#[derive(Clone, Copy)]
enum BranchSide {
    /// Assert `x <= floor(v)` as an upper bound.
    Floor,
    /// Assert `x >= ceil(v)` as a lower bound.
    Ceil,
}

/// One node of the branch-and-bound search, held on an explicit heap stack rather than the
/// call stack (see [`LIRASolver::branch_iterative`]). Each frame records where it is in
/// exploring its two children so the search can be suspended and resumed as the stack grows
/// and shrinks.
struct BranchFrame {
    /// The fractional integer variable this node branches on.
    x: Var,
    /// Upper bound for the floor branch (`x <= floor_bound`).
    floor_bound: Integer,
    /// Lower bound for the ceil branch (`x >= ceil_bound`).
    ceil_bound: Integer,
    /// Distance from the root; drives the depth guard in [`LIRASolver::over_budget`].
    depth: usize,
    /// Which child this frame is about to explore or is currently waiting on.
    stage: Stage,
    /// The floor branch's conflict, kept while the ceil branch runs so the two can be
    /// resolved on `x` once both branches are pruned.
    floor_conflict: Option<Conflict<Var>>,
    /// LRA backtrack level to restore once the currently-awaited child completes. `None`
    /// when no bound is outstanding (the child finished without recursing, or none started).
    pending_level: Option<usize>,
}

/// Where a [`BranchFrame`] is in exploring its two children.
#[derive(Clone, Copy)]
enum Stage {
    /// Yet to explore the floor branch.
    ExploreFloor,
    /// Floor branch is running; its outcome is pending.
    AwaitFloor,
    /// Floor branch was pruned by a conflict on `x`; yet to explore the ceil branch.
    ExploreCeil,
    /// Ceil branch is running; its outcome is pending.
    AwaitCeil,
}

/// Result of entering a branch node: either it was solved immediately (the relaxation is
/// already integral) or it needs a [`BranchFrame`] pushed to explore its children.
enum Descent {
    Solved(NodeOutcome),
    Branch(BranchFrame),
}

/// Result of asserting one branch bound and solving the relaxation under it.
enum ExploreStep {
    /// Exploration finished without recursing; the LRA solver has already been backtracked
    /// to its pre-assertion state.
    Done(NodeOutcome),
    /// The relaxation is feasible but not yet integral, so a child branch should run at
    /// `depth + 1`. The asserted bound is still live; `level` must be backtracked once the
    /// child subtree completes.
    Recurse { level: usize },
}

/// Linear integer and real arithmetic solver.
///
/// Wraps an [`LRASolver`] and adds integrality reasoning via branch-and-bound. The LRA
/// solver is used incrementally: the search asserts a bound, recurses, then backtracks to
/// the saved level, so a single [`LRASolver`] instance serves the whole tree.
#[derive(Debug)]
pub struct LIRASolver {
    /// The underlying LRA solver, driven incrementally across the whole search.
    lra_solver: LRASolver,
    /// Solver configuration.
    config: SolverConfig,
    /// Runtime statistics accumulated across all LRA solves.
    stats: Stats,
}

impl LIRASolver {
    /// Create a new LIRASolver wrapping the given LRASolver.
    pub fn new(lra_solver: LRASolver, config: SolverConfig) -> Self {
        Self {
            lra_solver,
            config,
            stats: Stats::new(),
        }
    }

    /// Solve a mixed integer/real system.
    ///
    /// First tries cheap heuristics (unit cube test, rounding) against the rational
    /// relaxation, then falls back to branch-and-bound. Returns `FEASIBLE` with a model,
    /// `INFEASIBLE` with a conflict core, or `UNKNOWN` if a resource limit was hit.
    pub fn solve(&mut self) -> SolverResult<SolverReturn> {
        debug_println!(21, 0, "lia::lira_solver: starting LIRASolver");

        // The unit cube test can find an integer point without any LRA solving, so try it
        // before touching the relaxation.
        debug_println!(21, 0, "lia::lira_solver::solve: trying the unit cube test");
        if let Some(cube_assg) = self.lra_solver.try_unit_cube_test()? {
            debug_println!(21, 0, "lia::lira_solver::solve: unit cube test succeeded");
            return Ok(self.finish(SolverDecision::FEASIBLE(cube_assg)));
        }

        // Solve the rational relaxation once up front. If it is infeasible or already
        // integral we are done; otherwise try the rounding heuristic before branching.
        debug_println!(21, 0, "lia::lira_solver::solve: solving the relaxation");
        let ret = self.lra_solver.solve()?;
        self.stats.combine(&ret.stats);

        match ret.decision {
            SolverDecision::INFEASIBLE(cs) => Ok(self.finish(SolverDecision::INFEASIBLE(cs))),
            SolverDecision::UNKNOWN => Ok(self.finish(SolverDecision::UNKNOWN)),
            SolverDecision::FEASIBLE(assg) => {
                debug_println!(21, 0, "lia::lira_solver::solve: relaxation feasible:\n{assg}");

                // The relaxation already satisfies every integrality constraint.
                if self.find_fractional_int_var().is_none() {
                    return Ok(self.finish(SolverDecision::FEASIBLE(assg)));
                }

                debug_println!(21, 0, "lia::lira_solver::solve: trying rounding heuristic");
                if let Some(rounded) = self.lra_solver.try_rounding_heuristic() {
                    debug_println!(21, 0, "lia::lira_solver::solve: rounding succeeded");
                    return Ok(self.finish(SolverDecision::FEASIBLE(rounded)));
                }

                // Fall back to branch-and-bound. The relaxation is already solved and its
                // state is live in the LRA solver, so start exploring from the root at
                // depth 0 rather than re-solving.
                debug_println!(21, 0, "lia::lira_solver: starting branch-and-bound");
                let outcome = self.branch_iterative(0)?;
                Ok(self.finish(match outcome {
                    NodeOutcome::Feasible(assg) => SolverDecision::FEASIBLE(assg),
                    NodeOutcome::Pruned(conflict) => SolverDecision::INFEASIBLE(conflict),
                    NodeOutcome::Unknown => SolverDecision::UNKNOWN,
                }))
            }
        }
    }

    /// Branch-and-bound driven by an explicit heap stack instead of the call stack.
    ///
    /// This is a direct iterative rendering of the recursive descent: each `BranchFrame` on
    /// `stack` is one node whose relaxation was feasible-but-fractional, and `stage` records
    /// which child it is exploring. Because depth is now bounded by heap memory rather than
    /// the OS thread stack, [`SolverConfig::max_branch_depth`] can be set far higher than a
    /// recursive version could safely tolerate.
    ///
    /// The per-node combine rules are unchanged from the recursive form:
    /// - either child feasible  → propagate it up (the search is done),
    /// - either child pruned by a conflict not mentioning `x` → that conflict alone proves
    ///   this node infeasible, so the other branch is irrelevant and skipped,
    /// - both children pruned    → resolve the two conflicts on `x` (drops `x`, unions the
    ///   rest), yielding this node's conflict.
    ///
    /// The LRA solver is still driven incrementally with the same
    /// `set_backtrack`/assert/solve/`backtrack` discipline the recursion used: every bound
    /// asserted on the way down is undone on the way back up, in strict LIFO order.
    fn branch_iterative(&mut self, root_depth: usize) -> SolverResult<NodeOutcome> {
        let mut stack: Vec<BranchFrame> = Vec::new();
        match self.descend(root_depth)? {
            // The root relaxation is already integral (or otherwise decided) — no branching.
            Descent::Solved(outcome) => Ok(outcome),
            Descent::Branch(frame) => {
                stack.push(frame);
                self.run(&mut stack)
            }
        }
    }

    /// Drive the explicit stack to completion, returning the root node's outcome.
    ///
    /// `stack` must contain exactly the root frame on entry. On return the stack is empty and
    /// the LRA solver has been backtracked to its state before branching began.
    ///
    /// `child` carries the outcome bubbling up from the most-recently-finished node to the
    /// frame that explored it; it is consumed by the `Await*` stages and, once the stack is
    /// empty, holds the root's outcome.
    fn run(&mut self, stack: &mut Vec<BranchFrame>) -> SolverResult<NodeOutcome> {
        let mut child: Option<NodeOutcome> = None;

        while let Some(top) = stack.len().checked_sub(1) {
            match stack[top].stage {
                // Explore the floor branch: x <= floor(val).
                Stage::ExploreFloor => {
                    let (x, bound, depth) =
                        (stack[top].x, stack[top].floor_bound.clone(), stack[top].depth);
                    match self.step(x, BranchSide::Floor, bound, depth)? {
                        // Floor branch finished without recursing. Combine at this node.
                        ExploreStep::Done(outcome) => Self::combine_floor(stack, &mut child, outcome),
                        // Floor branch is feasible-but-fractional; descend into its child.
                        ExploreStep::Recurse { level } => {
                            stack[top].stage = Stage::AwaitFloor;
                            stack[top].pending_level = Some(level);
                            self.push_child(stack, depth + 1, &mut child)?;
                        }
                    }
                }

                // The floor child we descended into has returned in `child`.
                Stage::AwaitFloor => {
                    let outcome = child.take().expect("await floor without child outcome");
                    let level = stack[top].pending_level.take().expect("await floor without level");
                    self.lra_solver.backtrack(level);
                    Self::combine_floor(stack, &mut child, outcome);
                }

                // Explore the ceil branch: x >= ceil(val).
                Stage::ExploreCeil => {
                    let (x, bound, depth) =
                        (stack[top].x, stack[top].ceil_bound.clone(), stack[top].depth);
                    match self.step(x, BranchSide::Ceil, bound, depth)? {
                        ExploreStep::Done(outcome) => Self::combine_ceil(stack, &mut child, outcome),
                        ExploreStep::Recurse { level } => {
                            stack[top].stage = Stage::AwaitCeil;
                            stack[top].pending_level = Some(level);
                            self.push_child(stack, depth + 1, &mut child)?;
                        }
                    }
                }

                // The ceil child we descended into has returned in `child`.
                Stage::AwaitCeil => {
                    let outcome = child.take().expect("await ceil without child outcome");
                    let level = stack[top].pending_level.take().expect("await ceil without level");
                    self.lra_solver.backtrack(level);
                    Self::combine_ceil(stack, &mut child, outcome);
                }
            }
        }

        Ok(child.expect("stack drained without producing a root outcome"))
    }

    /// Fold the floor branch's `outcome` into the top frame: pop-and-propagate if the node is
    /// decided, or advance it to the ceil branch otherwise.
    fn combine_floor(
        stack: &mut Vec<BranchFrame>,
        child: &mut Option<NodeOutcome>,
        outcome: NodeOutcome,
    ) {
        let top = stack.len() - 1;
        let x = stack[top].x;
        match outcome {
            NodeOutcome::Feasible(assg) => Self::finish_frame(stack, child, NodeOutcome::Feasible(assg)),
            NodeOutcome::Unknown => Self::finish_frame(stack, child, NodeOutcome::Unknown),
            NodeOutcome::Pruned(floor_conflict) => {
                // A floor conflict independent of `x` proves this node infeasible on its own;
                // the ceil branch cannot change that, so skip it.
                if !floor_conflict.contains(&x) {
                    debug_println!(15, 0, "lia::lira_solver: floor conflict independent of {x}");
                    Self::finish_frame(stack, child, NodeOutcome::Pruned(floor_conflict));
                } else {
                    // Keep the floor conflict and explore the ceil branch next.
                    stack[top].floor_conflict = Some(floor_conflict);
                    stack[top].stage = Stage::ExploreCeil;
                }
            }
        }
    }

    /// Fold the ceil branch's `outcome` into the top frame, then pop-and-propagate the node's
    /// final outcome.
    fn combine_ceil(
        stack: &mut Vec<BranchFrame>,
        child: &mut Option<NodeOutcome>,
        outcome: NodeOutcome,
    ) {
        let top = stack.len() - 1;
        let x = stack[top].x;
        let final_outcome = match outcome {
            NodeOutcome::Feasible(assg) => NodeOutcome::Feasible(assg),
            NodeOutcome::Unknown => NodeOutcome::Unknown,
            NodeOutcome::Pruned(ceil_conflict) => {
                if !ceil_conflict.contains(&x) {
                    debug_println!(15, 0, "lia::lira_solver: ceil conflict independent of {x}");
                    NodeOutcome::Pruned(ceil_conflict)
                } else {
                    // Both branches are infeasible and both depend on `x`. Resolve on `x` to
                    // obtain a conflict that no longer mentions it, proving this node
                    // infeasible.
                    let floor_conflict = stack[top]
                        .floor_conflict
                        .take()
                        .expect("ceil branch completed without a saved floor conflict");
                    NodeOutcome::Pruned(floor_conflict.resolve(x, &ceil_conflict))
                }
            }
        };
        Self::finish_frame(stack, child, final_outcome);
    }

    /// Pop the top frame and hand its `outcome` to whatever explored it (its parent frame, or
    /// the caller if it was the root) by stashing it in `child`.
    fn finish_frame(
        stack: &mut Vec<BranchFrame>,
        child: &mut Option<NodeOutcome>,
        outcome: NodeOutcome,
    ) {
        stack.pop();
        *child = Some(outcome);
    }

    /// Enter a branch node given the LRA solver already holds a feasible rational model.
    ///
    /// Returns [`Descent::Solved`] when the model is already integral (a real solution), and
    /// [`Descent::Branch`] with a fresh [`BranchFrame`] otherwise. `depth` is the node's
    /// distance from the root.
    fn descend(&mut self, depth: usize) -> SolverResult<Descent> {
        let (x, val) = match self.find_fractional_int_var() {
            // Every integer variable is integral: this rational model is a real solution.
            None => {
                let model = self
                    .lra_solver
                    .get_rational_model()
                    .expect("feasible node must have a rational model");
                return Ok(Descent::Solved(NodeOutcome::Feasible(Assignment::new(model))));
            }
            Some(pair) => pair,
        };
        debug_println!(15, 0, "lia::lira_solver: branching on {x} = {val}");
        Ok(Descent::Branch(BranchFrame {
            x,
            floor_bound: val.floor(),
            ceil_bound: val.ceil(),
            depth,
            stage: Stage::ExploreFloor,
            floor_conflict: None,
            pending_level: None,
        }))
    }

    /// Descend into a child node at `depth`, pushing a frame for it when it needs further
    /// branching or writing its immediate outcome to `child` when it is solved outright.
    fn push_child(
        &mut self,
        stack: &mut Vec<BranchFrame>,
        depth: usize,
        child: &mut Option<NodeOutcome>,
    ) -> SolverResult<()> {
        match self.descend(depth)? {
            Descent::Solved(outcome) => *child = Some(outcome),
            Descent::Branch(frame) => stack.push(frame),
        }
        Ok(())
    }

    /// Assert one side of a branch on `x` and solve the relaxation under it.
    ///
    /// `bound` is `floor(val)` (asserted as an upper bound) or `ceil(val)` (asserted as a
    /// lower bound) depending on `side`.
    ///
    /// Returns [`ExploreStep::Done`] — with the LRA solver already backtracked — when the
    /// branch resolves without needing a child (budget hit, trivial contradiction, or an
    /// infeasible relaxation). Returns [`ExploreStep::Recurse`] with the outstanding
    /// backtrack `level` when the relaxation is feasible-but-fractional and a child should be
    /// explored; the caller must `backtrack(level)` once that child completes.
    fn step(
        &mut self,
        x: Var,
        side: BranchSide,
        bound: Integer,
        depth: usize,
    ) -> SolverResult<ExploreStep> {
        // Guard the LRA-solve budget and the (now heap-bounded) branch depth.
        if self.over_budget(depth) {
            return Ok(ExploreStep::Done(NodeOutcome::Unknown));
        }

        let level = self.lra_solver.set_backtrack();
        let qbound = QDelta::from(Rational::from(bound));
        let assert_res = match side {
            BranchSide::Floor => self.lra_solver.assert_upper(&x, &qbound)?,
            BranchSide::Ceil => self.lra_solver.assert_lower(&x, &qbound)?,
        };

        if let Some(false) = assert_res {
            // The bound directly contradicts an existing one on `x`, so the branch is
            // infeasible without any solving. The conflict is `x`'s bound alone.
            debug_println!(15, 0, "lia::lira_solver: branch on {x} trivially infeasible");
            self.lra_solver.backtrack(level);
            return Ok(ExploreStep::Done(NodeOutcome::Pruned([x].into_iter().collect())));
        }

        // Solve the relaxation under the new bound.
        let ret = self.lra_solver.solve()?;
        self.stats.combine(&ret.stats);
        match ret.decision {
            SolverDecision::INFEASIBLE(conflict) => {
                self.lra_solver.backtrack(level);
                Ok(ExploreStep::Done(NodeOutcome::Pruned(conflict)))
            }
            // Feasible but not necessarily integral: keep the bound live and branch deeper.
            // The caller backtracks `level` once the child subtree completes.
            SolverDecision::FEASIBLE(_) => Ok(ExploreStep::Recurse { level }),
            SolverDecision::UNKNOWN => {
                unreachable!("lra_solver decision cannot be UNKNOWN after solve")
            }
        }
    }

    /// Whether the search should stop and report `UNKNOWN`, because either the configured
    /// LRA-solve budget or the maximum branch depth (also the recursion-depth guard) has
    /// been reached.
    fn over_budget(&self, depth: usize) -> bool {
        if let Some(max) = self.config.max_lra_solve_calls
            && self.stats.num_lra_solve > max
        {
            debug_println!(21, 0, "lia::lira_solver: max LRA-solve calls reached");
            return true;
        }
        if let Some(max) = self.config.max_branch_depth
            && depth >= max
        {
            debug_println!(21, 0, "lia::lira_solver: max branch depth reached");
            return true;
        }
        false
    }

    /// Wrap a decision together with the accumulated stats into a [`SolverReturn`].
    fn finish(&self, decision: SolverDecision) -> SolverReturn {
        SolverReturn::new(decision, self.stats.clone())
    }

    /// Get a reference to the underlying LRASolver.
    pub fn lra_solver(&self) -> &LRASolver {
        &self.lra_solver
    }

    /// Get a mutable reference to the underlying LRASolver.
    pub fn lra_solver_mut(&mut self) -> &mut LRASolver {
        &mut self.lra_solver
    }

    /// Find the first integer-typed variable whose current rational assignment is not
    /// integral, returning it with that value. `None` means the model is fully integral.
    ///
    /// TODO: track integer variables separately to avoid scanning the whole model.
    fn find_fractional_int_var(&self) -> Option<(Var, Rational)> {
        let model = self.lra_solver.get_rational_model()?;
        model
            .iter()
            .find(|(var, val)| var.typ == VarType::Int && !val.is_int())
            .map(|(var, val)| (*var, val.clone()))
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
