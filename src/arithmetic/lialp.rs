// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Entry point for the LIA mixed integer arithmetic solver

use crate::arithmetic::incremental::IncrementalArithSolver;
use crate::arithmetic::lia::config::SolverConfig;
use crate::arithmetic::lia::context::ConvContext;
use crate::arithmetic::lia::frontend;
use crate::arithmetic::lia::linear_system::{Constraint, LinearSystem, Mon, Rel};
use crate::arithmetic::lia::solver_result::SolverDecision;
use crate::arithmetic::lia::variables::{Var, VarType};
use crate::arithmetic::lp::{
    ArithResult, Coefficient, FunctionType, FunctionType::*, LinearConstraint,
    extract_constraint_from_term, extract_linear_constraints, extract_linear_expression,
};
use crate::debug_println;
use crate::egraphs::EgraphTrait;
use crate::solver_state::SolverState;
use crate::utils::{DeterministicHashMap, DeterministicHashSet};
use dashu::{Integer, Rational};
use std::collections::HashMap;

pub fn check_integer_constraints_satisfiable_lia(
    terms: &[i32],
    // TODO: lialp: check that taking egraph mutable is okay
    solver_state: &mut SolverState,
) -> ArithResult {
    let (constraints, arithmetic_literals) = extract_linear_constraints(terms, solver_state);

    if constraints.is_empty() && arithmetic_literals.is_empty() {
        return ArithResult::None; // No constraints mean trivially satisfiable
    }

    debug_println!(21, 4, "trying to solve with constraints: {:?}", constraints);
    debug_println!(21, 4, "and arithmetic literals {:?}", arithmetic_literals);

    let mut var_map = DeterministicHashMap::new();

    // Create a context for the internal arithmetic solver then build it up
    let mut ctx = ConvContext::new();
    let mut roots = vec![];
    // For each var we create in the arithmetic solver, track the literals that were used to justify
    // it. This is used later for translating an "infeasible" outcome into an unsat core.
    let mut slack_to_lits: HashMap<Var, Vec<i32>> = HashMap::new();

    for idx in 0..solver_state.arithmetic_terms.len() {
        let term_id = solver_state.arithmetic_terms[idx];
        let egraph_id = solver_state.to_egraph_id(term_id);
        if solver_state.egraph.find(egraph_id) == egraph_id {
            let (expr, additional_constraints) = extract_linear_expression(term_id, solver_state);
            let root_var = *var_map.entry(egraph_id).or_insert_with(|| {
                ctx.allocate_var(&format!("!ext_var_{}", egraph_id), VarType::Int)
            });
            roots.push((term_id, root_var));

            // We have "root_var = expr," make it into "root_var - expr = 0"
            let (mut monomials, constant) =
                expr_to_monomials(&expr, -Rational::ONE, &mut var_map, &mut ctx);
            monomials.insert(0, Mon::new(Rational::ONE, root_var));

            let slack =
                ctx.allocate_var(&format!("!ext_slack_var_root_{}", term_id), VarType::Real);
            ctx.push_relation(Rel::mk_eq(monomials, constant), slack);
            slack_to_lits.insert(slack, additional_constraints);
        }
    }

    for (constraint_idx, constraint) in constraints.iter().enumerate() {
        debug_println!(4, 0, "WE ARE IN ARITH CHECK: Constraint: {:?}", constraint);
        // We have  "left_expr REL right_expr," make it into "(left_expr - right_expr) REL 0"
        let (mut constr_monomials, mut constant) =
            expr_to_monomials(&constraint.left_expr, Rational::ONE, &mut var_map, &mut ctx);
        let (rhs_monomials, rhs_constant) = expr_to_monomials(
            &constraint.right_expr,
            -Rational::ONE,
            &mut var_map,
            &mut ctx,
        );
        constr_monomials.extend(rhs_monomials);
        constant += rhs_constant;

        let rel = match &constraint.function {
            Leq => Rel::mk_le(constr_monomials, constant),
            Lt => Rel::mk_lt(constr_monomials, constant),
            Eq => Rel::mk_eq(constr_monomials, constant),
        };

        let slack = ctx.allocate_var(
            &format!("!ext_slack_constraint_{}", constraint_idx),
            VarType::Real,
        );
        ctx.push_relation(rel, slack);

        let mut lits = constraint.additional_constraint.clone().unwrap_or_default();
        lits.push(arithmetic_literals[constraint_idx]);
        slack_to_lits.insert(slack, lits);
    }

    match frontend::solve_ctx_raw(&mut ctx, &SolverConfig::default()) {
        Ok(ret) => {
            debug_println!(25, 4, "lia::frontend: stats: {:?}", ret.stats);
            let stats = ret.stats;
            match ret.decision {
                SolverDecision::FEASIBLE(assignment) => {
                    let mut model_hashmap: DeterministicHashMap<i64, DeterministicHashSet<u64>> =
                        DeterministicHashMap::new();
                    for (term_id, root_var) in &roots {
                        if let Some(value) = assignment.get(root_var) {
                            let val_i64: i64 =
                                value.to_int().value().try_into().unwrap_or(i64::MAX);
                            model_hashmap.entry(val_i64).or_default().insert(*term_id);
                        }
                    }
                    ArithResult::Sat(model_hashmap, stats)
                }
                SolverDecision::INFEASIBLE(conflict) => {
                    let unsat_core_literals: Vec<i32> = conflict
                        .iter()
                        .flat_map(|var| slack_to_lits.get(var).into_iter().flatten().copied())
                        .collect();
                    debug_println!(21, 4, "LIA: Unsat core literals: {:?}", unsat_core_literals);
                    ArithResult::Unsat(unsat_core_literals, stats)
                }
                SolverDecision::UNKNOWN => ArithResult::None,
            }
        }
        Err(e) => panic!("lialp: unexpected error: {e:?}"),
    }
}

/// Map the extraction-layer [`FunctionType`] to the linear-system [`Constraint`] used for a
/// *positive* literal. The extraction always normalizes to `left REL right` with `REL` one of
/// `<=`, `<`, `=` (`>=`/`>` are folded into `<=`/`<` by swapping sides), so only these three
/// cases arise.
fn function_to_constraint(f: &FunctionType) -> Constraint {
    match f {
        Leq => Constraint::Le,
        Lt => Constraint::Lt,
        Eq => Constraint::Eq,
    }
}

/// Build a persistent [`IncrementalArithSolver`] with a **static tableau** covering every
/// arithmetic atom in the formula (Stage 2 of the incremental-arithmetic plan).
///
/// Unlike [`check_integer_constraints_satisfiable_lia`], which rebuilds a context + tableau
/// from the *current* SAT model on every call, this walks the full, up-front atom set once:
///
/// - definitional rows `root_var - expr = 0` for each egraph-root arithmetic term (mirrors
///   `check_integer_constraints_satisfiable_lia`, but done once);
/// - one slack per comparison atom, its relation pushed with the atom's threshold as the
///   relation constant. Slacks are built **unbounded** (`to_lra_solver(false, …)`): the bound
///   direction is chosen at assert time, so a single slack serves both polarities of the atom.
///
/// Both `+lit` (the relation) and `-lit` (the negated relation, via [`Constraint::negate`];
/// equality negation is deferred to Nelson-Oppen, matching the one-shot path) are registered
/// against that slack.
///
/// This does **not** touch the live solve path; it is exercised in isolation and against the
/// one-shot path as a differential check (Stage 8).
pub fn build_incremental_solver(solver_state: &mut SolverState) -> IncrementalArithSolver {
    let mut ctx = ConvContext::new();
    // egraph-var-id -> the Var allocated for that (root) term
    let mut var_map: DeterministicHashMap<u32, Var> = DeterministicHashMap::new();

    // 1. Definitional rows for arithmetic terms that are their own egraph root: root - expr = 0.
    //    Keyed on egraph id, which is stable before search begins (moving-root handling is
    //    Stage 6). Iterate a copy of the term list to avoid borrow conflicts with extraction.
    //    Also collect (term_id, root_var) pairs to register as roots for NO model translation.
    let arithmetic_terms = solver_state.arithmetic_terms.clone();
    let mut root_pairs: Vec<(u64, Var)> = Vec::new();
    for term_id in arithmetic_terms {
        let egraph_id = solver_state.to_egraph_id(term_id);
        if solver_state.egraph.find(egraph_id) != egraph_id {
            continue;
        }
        let (expr, _additional) = extract_linear_expression(term_id, solver_state);
        let root_var = *var_map
            .entry(egraph_id)
            .or_insert_with(|| ctx.allocate_var(&format!("!ext_var_{}", egraph_id), VarType::Int));
        root_pairs.push((term_id, root_var));

        let (mut monomials, constant) =
            expr_to_monomials(&expr, -Rational::ONE, &mut var_map, &mut ctx);
        monomials.insert(0, Mon::new(Rational::ONE, root_var));
        let slack = ctx.allocate_var(&format!("!ext_slack_var_root_{}", term_id), VarType::Real);
        ctx.push_relation(Rel::mk_eq(monomials, constant), slack);
    }

    // 2. Enumerate all arithmetic comparison atoms once. `var_map` in the CNF cache holds every
    //    atom's uid -> literal. Sort the uids so atom/slack allocation order is deterministic.
    let mut atom_uids: Vec<u64> = solver_state.cnf_cache.var_map.keys().copied().collect();
    atom_uids.sort_unstable();

    // Collect (uid, lit, LinearConstraint) first so all &mut solver_state extraction is done
    // before we start borrowing ctx/var_map mutably alongside the registry.
    let mut atoms: Vec<(i32, LinearConstraint)> = Vec::new();
    for uid in atom_uids {
        let lit = solver_state.get_lit_from_u64(uid);
        // Interpret the atom positively; `extract_constraint_from_term` returns Some exactly for
        // the arithmetic comparisons `<=`, `<`, `>=`, `>`, `=`.
        if let Some(constraint) = extract_constraint_from_term(uid, true, solver_state) {
            atoms.push((lit, constraint));
        }
    }

    let mut incremental_pending: Vec<(i32, Var, Constraint, Rational)> = Vec::new();
    for (idx, (lit, constraint)) in atoms.into_iter().enumerate() {
        // (left_expr - right_expr) REL 0, exactly as the one-shot path builds it.
        let (mut monomials, mut constant) =
            expr_to_monomials(&constraint.left_expr, Rational::ONE, &mut var_map, &mut ctx);
        let (rhs_monomials, rhs_constant) =
            expr_to_monomials(&constraint.right_expr, -Rational::ONE, &mut var_map, &mut ctx);
        monomials.extend(rhs_monomials);
        constant += rhs_constant;

        let pos_constraint = function_to_constraint(&constraint.function);
        let rel = match pos_constraint {
            Constraint::Le => Rel::mk_le(monomials, constant.clone()),
            Constraint::Lt => Rel::mk_lt(monomials, constant.clone()),
            Constraint::Eq => Rel::mk_eq(monomials, constant.clone()),
            // function_to_constraint only yields Le/Lt/Eq
            _ => unreachable!("unexpected positive constraint from function_to_constraint"),
        };
        let slack = ctx.allocate_var(&format!("!ext_slack_atom_{}", idx), VarType::Real);
        ctx.push_relation(rel, slack);

        // The threshold for the slack bound is the relation constant.
        incremental_pending.push((lit, slack, pos_constraint, constant));
    }

    // 3. Build the LRA solver with unbounded slacks (bounds are asserted incrementally).
    let lra = LinearSystem::new(ctx)
        .to_lra_solver(false, &SolverConfig::default())
        .expect("build_incremental_solver: failed to build LRA solver");
    let mut solver = IncrementalArithSolver::new(lra, SolverConfig::default());

    // 4. Register both polarities of each atom against its slack.
    for (lit, slack, pos_constraint, threshold) in incremental_pending {
        solver.register_literal_atom(lit, slack, pos_constraint, threshold.clone());
        if let Some(neg_constraint) = pos_constraint.negate() {
            solver.register_literal_atom(-lit, slack, neg_constraint, threshold);
        }
    }

    // 5. Register root (term_id, root_var) pairs for NO model translation.
    for (term_id, root_var) in root_pairs {
        solver.register_root(term_id, root_var);
    }

    solver
}

pub(crate) fn expr_to_monomials(
    expr: &DeterministicHashMap<Coefficient, Integer>,
    sign: Rational, // just one or negative one
    var_map: &mut DeterministicHashMap<u32, Var>,
    ctx: &mut ConvContext,
) -> (Vec<Mon<Rational>>, Rational) {
    // Each entry in expr is a (Coefficient, Integer) pair, but really the Integer part is what
    // should be the coefficient in the monomial we create. The "Coefficient" here either has a
    // term (by its id) or no term at all; i.e. 1.
    let mut monomials: Vec<Mon<Rational>> = Vec::new();
    let mut constant = Rational::ZERO;
    for (term_part, int_coeff) in expr {
        let rational_coeff = Rational::from(int_coeff.clone());
        match term_part {
            Coefficient::Term(id) => {
                let v = *var_map
                    .entry(*id)
                    .or_insert_with(|| ctx.allocate_var(&format!("!ext_var_{}", id), VarType::Int));
                monomials.push(Mon::new(&sign * &rational_coeff, v));
            }
            Coefficient::Constant => constant = -&sign * rational_coeff,
        }
    }
    (monomials, constant)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arithmetic::incremental::{AssertOutcome, CheckResult};
    use crate::cnf::CNFConversion;
    use yaspar_ir::ast::{
        Context, GlobalSubst, LetElim, ObjectAllocatorExt, Repr, Term, TermAllocator, Typecheck,
        alg,
    };
    use yaspar_ir::untyped::UntypedAst;

    /// Build a `SolverState` from an `.smt2` string, mirroring the essential preprocessing
    /// pipeline in `main.rs` (parse → typecheck → collect asserts → nnf → insert_predecessor →
    /// cnf_tseitin). Enough to populate `arithmetic_terms` and the CNF `var_map`, which is all
    /// the static builder needs.
    fn setup_solver_state(smt: &str) -> SolverState {
        let commands = UntypedAst
            .parse_script_str(smt)
            .expect("parse failed");
        let mut context = Context::new();
        let typed = commands.type_check(&mut context).expect("typecheck failed");

        let mut assertions: Vec<Term> = typed
            .iter()
            .filter_map(|c| match c.repr() {
                alg::Command::Assert(t) => Some(t.clone()),
                _ => None,
            })
            .collect();

        let false_term = context.get_false();
        let not_false_term = context.not(false_term.clone());
        let true_term = context.get_true();
        assertions.push(true_term.clone());
        assertions.push(not_false_term);

        let mut solver_state = SolverState::new(context, false, false, false);
        solver_state.register_bool_constants(&true_term, &false_term);

        let global_names = solver_state.context.all_defined_symbols();
        for assert in assertions {
            let expanded = assert
                .let_elim(&mut solver_state.context)
                .gsubst(global_names.clone(), &mut solver_state.context);
            let nnf_term = expanded.nnf(&mut solver_state);
            solver_state.insert_predecessor(&nnf_term, None, None, false);
            let _ = nnf_term.cnf_tseitin(&mut solver_state);
        }
        solver_state
    }

    /// Collect every arithmetic atom literal (positive form) known to the CNF cache.
    fn arithmetic_atom_lits(solver_state: &mut SolverState) -> Vec<i32> {
        let mut uids: Vec<u64> = solver_state.cnf_cache.var_map.keys().copied().collect();
        uids.sort_unstable();
        let mut lits = vec![];
        for uid in uids {
            let lit = solver_state.get_lit_from_u64(uid);
            if extract_constraint_from_term(uid, true, solver_state).is_some() {
                lits.push(lit);
            }
        }
        lits
    }

    #[test]
    fn build_registers_both_polarities() {
        // Two atoms over one variable: (x <= 5) and (x >= 0), plus true/false.
        let smt = r#"
(declare-const x Int)
(assert (<= x 5))
(assert (>= x 0))
"#;
        let mut ss = setup_solver_state(smt);
        let atom_lits = arithmetic_atom_lits(&mut ss);
        assert!(!atom_lits.is_empty(), "expected arithmetic atoms");

        let solver = build_incremental_solver(&mut ss);
        // Each non-equality atom registers 2 polarities.
        for lit in &atom_lits {
            assert!(
                solver.atom_for_literal(*lit).is_some(),
                "positive literal {lit} should be registered"
            );
            assert!(
                solver.atom_for_literal(-*lit).is_some(),
                "negative literal {} should be registered",
                -*lit
            );
        }
    }

    /// Differential check: asserting a set of atom literals into the static solver and calling
    /// `check` must agree (sat vs unsat) with the one-shot `check_integer_constraints_satisfiable_lia`
    /// on the same literals.
    fn assert_agrees(smt: &str, lits_to_assert: &[i32]) {
        let mut ss = setup_solver_state(smt);

        // Incremental path.
        let mut solver = build_incremental_solver(&mut ss);
        let mut incremental_conflict = false;
        for &lit in lits_to_assert {
            if let Some(AssertOutcome::Conflict) = solver.assert_literal(lit) {
                incremental_conflict = true;
            }
        }
        let incremental_unsat =
            incremental_conflict || matches!(solver.check(), CheckResult::Unsat { .. });

        // One-shot path on the same literals. It negates literals internally, so pass them as-is.
        let one_shot = check_integer_constraints_satisfiable_lia(lits_to_assert, &mut ss);
        let one_shot_unsat = matches!(one_shot, ArithResult::Unsat(..));

        assert_eq!(
            incremental_unsat, one_shot_unsat,
            "incremental vs one-shot disagree on {smt:?} with lits {lits_to_assert:?}"
        );
    }

    #[test]
    fn differential_feasible() {
        let smt = r#"
(declare-const x Int)
(assert (<= x 5))
(assert (>= x 0))
"#;
        let mut ss = setup_solver_state(smt);
        let lits = arithmetic_atom_lits(&mut ss);
        // asserting both (x <= 5) and (x >= 0): feasible
        assert_agrees(smt, &lits);
    }

    #[test]
    fn differential_infeasible() {
        // x >= 5 and x <= 3 asserted together: infeasible.
        let smt = r#"
(declare-const x Int)
(assert (>= x 5))
(assert (<= x 3))
"#;
        let mut ss = setup_solver_state(smt);
        let lits = arithmetic_atom_lits(&mut ss);
        assert_agrees(smt, &lits);
    }

    #[test]
    fn differential_negated_polarity() {
        // Assert the *negation* of (x <= 3), i.e. x > 3, together with x <= 3's companion
        // bound x >= 5's negation etc. Here we drive the `-lit` (negated-constraint) path:
        // asserting ¬(x <= 3) [x > 3] and (x <= 2) is infeasible.
        let smt = r#"
(declare-const x Int)
(assert (<= x 3))
(assert (<= x 2))
"#;
        let mut ss = setup_solver_state(smt);
        let lits = arithmetic_atom_lits(&mut ss);
        // Negate the first atom literal (x <= 3 -> x > 3); keep x <= 2. x > 3 & x <= 2 is unsat.
        let mixed: Vec<i32> = vec![-lits[0], lits[1]];
        assert_agrees(smt, &mixed);
    }
}
