// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Entry point for the LIA mixed integer arithmetic solver

use crate::arithmetic::lia::config::SolverConfig;
use crate::arithmetic::lia::context::ConvContext;
use crate::arithmetic::lia::frontend;
use crate::arithmetic::lia::linear_system::{Mon, Rel};
use crate::arithmetic::lia::solver_result::SolverDecision;
use crate::arithmetic::lia::variables::{Var, VarType};
use crate::arithmetic::lp::{
    ArithResult, Coefficient, FunctionType::*, extract_linear_constraints,
    extract_linear_expression,
};
use crate::debug_println;
use crate::egraphs::EgraphTrait;
use crate::solver_state::SolverState;
use crate::utils::{DeterministicHashMap, DeterministicHashSet};
use dashu::{Integer, Rational, integer::IBig};
use std::collections::HashMap;

pub fn check_integer_constraints_satisfiable_lia(
    terms: &[i32],
    // TODO: lialp: check that taking egraph mutable is okay
    solver_state: &mut SolverState,
) -> ArithResult {
    let (constraints, arithmetic_literals) = extract_linear_constraints(terms, solver_state);
    let arithmetic_terms = solver_state.active_arithmetic_terms();

    // Even with no explicit inequality/equality constraints, arithmetic terms
    // carry definitional equalities (e.g. `(* 1 y) == y`) that, combined with
    // egraph disequalities, are refuted via Nelson-Oppen. Only short-circuit
    // when there is genuinely no arithmetic content to define.
    if constraints.is_empty() && arithmetic_literals.is_empty() && arithmetic_terms.is_empty() {
        return ArithResult::None; // No arithmetic content means trivially satisfiable
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

    for term_id in arithmetic_terms {
        let egraph_id = solver_state.to_egraph_id(term_id);
        if solver_state.egraph.find(egraph_id) == egraph_id {
            let (expr, additional_constraints) = extract_linear_expression(term_id, solver_state);
            let root_var = *var_map.entry(egraph_id).or_insert_with(|| {
                ctx.allocate_var(&format!("!ext_var_{}", egraph_id), VarType::Int)
            });
            roots.push((term_id, root_var));

            // We have "root_var = expr," make it into "root_var - expr = 0"
            let (mut monomials, constant, euclidean_slacks) =
                expr_to_monomials(&expr, -Rational::ONE, &mut var_map, &mut ctx, solver_state);
            monomials.insert(0, Mon::new(Rational::ONE, root_var));

            let slack =
                ctx.allocate_var(&format!("!ext_slack_var_root_{}", term_id), VarType::Real);
            ctx.push_relation(Rel::mk_eq(monomials, constant), slack);
            // Euclidean rows exist only because this root expression was extracted; if they
            // appear in a conflict, the same justification literals apply.
            for eucl_slack in euclidean_slacks {
                slack_to_lits.insert(eucl_slack, additional_constraints.clone());
            }
            slack_to_lits.insert(slack, additional_constraints);
        }
    }

    for (constraint_idx, constraint) in constraints.iter().enumerate() {
        debug_println!(4, 0, "WE ARE IN ARITH CHECK: Constraint: {:?}", constraint);
        // We have  "left_expr REL right_expr," make it into "(left_expr - right_expr) REL 0"
        let (mut constr_monomials, mut constant, mut euclidean_slacks) = expr_to_monomials(
            &constraint.left_expr,
            Rational::ONE,
            &mut var_map,
            &mut ctx,
            solver_state,
        );
        let (rhs_monomials, rhs_constant, rhs_euclidean_slacks) = expr_to_monomials(
            &constraint.right_expr,
            -Rational::ONE,
            &mut var_map,
            &mut ctx,
            solver_state,
        );
        constr_monomials.extend(rhs_monomials);
        constant += rhs_constant;
        euclidean_slacks.extend(rhs_euclidean_slacks);

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
        // Euclidean rows exist only because this constraint's expressions were extracted;
        // if they appear in a conflict, the same justification literals apply.
        for eucl_slack in euclidean_slacks {
            slack_to_lits.insert(eucl_slack, lits.clone());
        }
        slack_to_lits.insert(slack, lits);
    }

    match frontend::solve_ctx_raw(&mut ctx, &SolverConfig::default()) {
        Ok(ret) => {
            debug_println!(25, 4, "lia::frontend: stats: {:?}", ret.stats);
            let stats = ret.stats;
            match ret.decision {
                SolverDecision::FEASIBLE(assignment) => {
                    let mut model_hashmap: DeterministicHashMap<IBig, DeterministicHashSet<u64>> =
                        DeterministicHashMap::new();
                    for (term_id, root_var) in &roots {
                        if let Some(value) = assignment.get(root_var) {
                            let val: IBig = value.to_int().value().clone();
                            model_hashmap.entry(val).or_default().insert(*term_id);
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

fn expr_to_monomials(
    expr: &DeterministicHashMap<Coefficient, Integer>,
    sign: Rational, // just one or negative one
    var_map: &mut DeterministicHashMap<u32, Var>,
    ctx: &mut ConvContext,
    solver_state: &mut SolverState,
) -> (Vec<Mon<Rational>>, Rational, Vec<Var>) {
    let mut monomials: Vec<Mon<Rational>> = Vec::new();
    let mut constant = Rational::ZERO;
    let mut euclidean_slacks: Vec<Var> = Vec::new();
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
            Coefficient::Div(a_id, b_id) => {
                let n = resolve_constant_from_egraph_id(*b_id, solver_state);
                let a_var = *var_map.entry(*a_id).or_insert_with(|| {
                    ctx.allocate_var(&format!("!ext_var_{}", a_id), VarType::Int)
                });
                let q = ctx.allocate_var(&format!("!div_q_{}_{}", a_id, b_id), VarType::Int);
                let (slack_ge, slack_le) = add_euclidean_constraints(a_var, q, &n, ctx);
                euclidean_slacks.push(slack_ge);
                euclidean_slacks.push(slack_le);
                monomials.push(Mon::new(&sign * &rational_coeff, q));
            }
            Coefficient::Mod(a_id, b_id) => {
                let n = resolve_constant_from_egraph_id(*b_id, solver_state);
                let a_var = *var_map.entry(*a_id).or_insert_with(|| {
                    ctx.allocate_var(&format!("!ext_var_{}", a_id), VarType::Int)
                });
                let q = ctx.allocate_var(&format!("!mod_q_{}_{}", a_id, b_id), VarType::Int);
                let (slack_ge, slack_le) = add_euclidean_constraints(a_var, q, &n, ctx);
                euclidean_slacks.push(slack_ge);
                euclidean_slacks.push(slack_le);
                // mod(a, n) = a - n*q
                monomials.push(Mon::new(&sign * &rational_coeff, a_var));
                monomials.push(Mon::new(&sign * &rational_coeff * (-n), q));
            }
        }
    }
    (monomials, constant, euclidean_slacks)
}

/// Resolve an egraph ID to its constant integer value by evaluating its linear expression.
/// Handles cases like `(- 2)` which yaspar stores as `App("-", [2])`, not `Constant(-2)`.
/// Panics if the expression is not a pure constant.
fn resolve_constant_from_egraph_id(egraph_id: u32, solver_state: &mut SolverState) -> Rational {
    let solver_uid = solver_state.to_solver_uid(egraph_id);
    let (expr, _) = extract_linear_expression(solver_uid, solver_state);
    if expr.len() == 1 && expr.contains_key(&Coefficient::Constant) {
        Rational::from(expr[&Coefficient::Constant].clone())
    } else {
        panic!(
            "div/mod with non-constant divisor not supported by the internal solver (egraph id {})",
            egraph_id
        );
    }
}

/// Add Euclidean division constraints for quotient q = div(a, n):
///   a - n*q >= 0  (remainder is non-negative)
///   a - n*q <= |n| - 1  (remainder < |n|)
/// Returns the (>=, <=) slack vars owning the two rows so the caller can register
/// them in slack_to_lits under the same justification as the enclosing expression.
fn add_euclidean_constraints(
    a_var: Var,
    q: Var,
    n: &Rational,
    ctx: &mut ConvContext,
) -> (Var, Var) {
    let abs_n = if *n < Rational::ZERO {
        -n.clone()
    } else {
        n.clone()
    };

    // a - n*q >= 0
    let slack_ge = ctx.allocate_var(
        &format!("!div_slack_ge_{}", ctx.num_variables()),
        VarType::Real,
    );
    ctx.push_relation(
        Rel::mk_ge(
            vec![Mon::new(Rational::ONE, a_var), Mon::new(-n.clone(), q)],
            Rational::ZERO,
        ),
        slack_ge,
    );

    // a - n*q <= |n| - 1
    let slack_le = ctx.allocate_var(
        &format!("!div_slack_le_{}", ctx.num_variables()),
        VarType::Real,
    );
    ctx.push_relation(
        Rel::mk_le(
            vec![Mon::new(Rational::ONE, a_var), Mon::new(-n.clone(), q)],
            &abs_n - Rational::ONE,
        ),
        slack_le,
    );

    (slack_ge, slack_le)
}
