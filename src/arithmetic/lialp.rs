// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Entry point for the LIA mixed integer arithmetic solver

use crate::arithmetic::lia::context::ConvContext;
use crate::arithmetic::lia::frontend;
use crate::arithmetic::lia::linear_system::{Mon, Rel};
use crate::arithmetic::lia::solver_result::SolverDecision;
use crate::arithmetic::lia::variables::{Var, VarType};
use crate::arithmetic::lp::{
    ArithResult, Coefficient, FunctionType::*, extract_linear_constraints,
    extract_linear_expression,
};
use crate::egraphs::egraph::Egraph;
use crate::egraphs::proofforest::ProofForestEdge;
use crate::utils::{DeterministicHashMap, DeterministicHashSet};
use dashu::{Integer, Rational};

pub fn check_integer_constraints_satisfiable_lia(
    terms: &[i32],
    // TODO: lialp: check that taking egraph mutable is okay
    egraph: &mut Egraph,
) -> ArithResult {
    let (constraints, arithmetic_literals) = extract_linear_constraints(terms, egraph);

    if constraints.is_empty() && arithmetic_literals.is_empty() {
        return ArithResult::None; // No constraints mean trivially satisfiable
    }

    debug_println!(21, 4, "trying to solve with constraints: {:?}", constraints);
    debug_println!(21, 4, "and arithmetic literals {:?}", arithmetic_literals);

    let mut var_map = DeterministicHashMap::new();

    // Create a context for the internal lia solver then build it up
    let mut ctx = ConvContext::new();
    let mut roots = vec![];
    for term_id in egraph.arithmetic_terms.clone() {
        if let ProofForestEdge::Root { .. } = &egraph.proof_forest[term_id as usize] {
            let (expr, _) = extract_linear_expression(term_id, egraph);
            let root_var = *var_map
                .entry(term_id)
                .or_insert_with(|| ctx.allocate_var(&format!("var_{}", term_id), VarType::Int));
            roots.push((term_id, root_var));

            // We have "root_var = expr," make it into "root_var - expr = 0"
            let (mut monomials, constant) =
                expr_to_monomials(&expr, -Rational::ONE, &mut var_map, &mut ctx);
            monomials.insert(0, Mon::new(Rational::ONE, root_var));

            let slack = ctx.allocate_var(&format!("slack_var_root_{}", term_id), VarType::Real);
            ctx.push_relation(Rel::mk_eq(monomials, constant), slack);
        }
    }

    let mut constraint_literals: Vec<Vec<i32>> = Vec::new();
    let mut constraint_slack_vars: DeterministicHashMap<Var, usize> = DeterministicHashMap::new();

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
            &format!("slack_constraint_{}", constraint_idx),
            VarType::Real,
        );
        ctx.push_relation(rel, slack);
        constraint_slack_vars.insert(slack, constraint_idx);

        let mut lits = constraint.additional_constraint.clone().unwrap_or_default();
        lits.push(arithmetic_literals[constraint_idx]);
        constraint_literals.push(lits);
    }

    match frontend::solve_ctx_raw(&mut ctx) {
        Ok(SolverDecision::FEASIBLE(assignment)) => {
            let mut model_hashmap: DeterministicHashMap<i64, DeterministicHashSet<u64>> =
                DeterministicHashMap::new();
            for (term_id, root_var) in &roots {
                if let Some(value) = assignment.get(root_var) {
                    let val_i64: i64 = value.to_int().value().try_into().unwrap_or(i64::MAX);
                    model_hashmap.entry(val_i64).or_default().insert(*term_id);
                }
            }
            ArithResult::Sat(model_hashmap)
        }
        Ok(SolverDecision::INFEASIBLE(conflict)) => {
            let unsat_core_literals: Vec<i32> = conflict
                .iter()
                .filter_map(|var| constraint_slack_vars.get(var))
                .flat_map(|&idx| constraint_literals[idx].iter().copied())
                .collect();
            debug_println!(21, 4, "LIA: Unsat core literals: {:?}", unsat_core_literals);
            ArithResult::Unsat(unsat_core_literals)
        }
        Ok(SolverDecision::UNKNOWN) => ArithResult::None,
        Err(e) => panic!("lialp: unexpected error: {e:?}"),
    }
}

fn expr_to_monomials(
    expr: &DeterministicHashMap<Coefficient, Integer>,
    sign: Rational, // just one or negative one
    var_map: &mut DeterministicHashMap<u64, Var>,
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
                    .or_insert_with(|| ctx.allocate_var(&format!("var_{}", id), VarType::Int));
                monomials.push(Mon::new(&sign * &rational_coeff, v));
            }
            Coefficient::Constant => constant = -&sign * rational_coeff,
        }
    }
    (monomials, constant)
}
