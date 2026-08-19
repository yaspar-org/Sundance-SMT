// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::arithmetic::lia::stats::Stats as LiaStats;
use crate::egraphs::traits::EgraphTrait;
use crate::solver_state::SolverState;
use crate::{
    arithmetic::lp::{
        ArithResult, Coefficient, FunctionType::*, extract_linear_constraints,
        extract_linear_expression,
    },
    debug_println,
    utils::{DeterministicHashMap, DeterministicHashSet},
};
use dashu::integer::IBig;
use std::collections::HashMap;
use z3::{
    Solver,
    ast::{Bool, Int},
};

/// Checks if a conjunction of integer constraints is satisfiable using Z3
pub fn check_integer_constraints_satisfiable_z3(
    terms: &[i32],
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

    // Create Z3 solver
    let solver = Solver::new();

    // Collect all unique variable IDs (egraph IDs) and create Z3 variables
    let mut variable_ids = std::collections::BTreeSet::new();
    for constraint in &constraints {
        for var_name in constraint
            .left_expr
            .keys()
            .chain(constraint.right_expr.keys())
        {
            match var_name {
                Coefficient::Term(id) => {
                    variable_ids.insert(*id);
                }
                Coefficient::Div(a, b) | Coefficient::Mod(a, b) => {
                    variable_ids.insert(*a);
                    variable_ids.insert(*b);
                }
                Coefficient::Constant => {}
            }
        }
    }

    let mut var_map: DeterministicHashMap<u32, Int> = DeterministicHashMap::new();
    for id in variable_ids {
        var_map
            .entry(id)
            .or_insert_with(|| Int::new_const(format!("var_{}", id)));
    }

    // Create assumption-based constraints for proper unsat core extraction
    let mut assumptions: Vec<Bool> = Vec::new();
    let mut constraint_to_literals = HashMap::new();

    // keep track of these -> will be relevant for Nelson-Oppen
    let mut non_strict_inequalities = vec![];

    // todo: loop through the terms list and add equalities term = var_{root(term)}
    // also save the roots
    // todo: might be able to move this later
    let mut roots = vec![];
    for term_id in arithmetic_terms {
        let egraph_id = solver_state.to_egraph_id(term_id);
        if solver_state.egraph.find(egraph_id) == egraph_id {
            let left_expr = var_map
                .entry(egraph_id)
                .or_insert_with(|| Int::new_const(format!("var_{}", egraph_id)))
                .clone();

            roots.push((term_id, left_expr.clone()));
            let (right, literals) = extract_linear_expression(term_id, solver_state);

            // Ensure any new variables from the expression are in var_map
            for var_name in right.keys() {
                match var_name {
                    Coefficient::Term(id) => {
                        var_map
                            .entry(*id)
                            .or_insert_with(|| Int::new_const(format!("var_{}", id)));
                    }
                    Coefficient::Div(a, b) | Coefficient::Mod(a, b) => {
                        var_map
                            .entry(*a)
                            .or_insert_with(|| Int::new_const(format!("var_{}", a)));
                        var_map
                            .entry(*b)
                            .or_insert_with(|| Int::new_const(format!("var_{}", b)));
                    }
                    Coefficient::Constant => {}
                }
            }

            // Build the right-hand side expression
            let mut right_expr = Int::from_i64(0);
            for (var_name, coeff) in right.iter() {
                if let Some(z3_term) = coeff_to_z3_expr(var_name, coeff, &var_map) {
                    right_expr += z3_term;
                }
            }
            let constraint = Int::eq(&left_expr, right_expr);

            assumptions.push(constraint.clone());
            constraint_to_literals.insert(constraint, literals);
        }
    }

    for (constraint_idx, constraint) in constraints.iter().enumerate() {
        debug_println!(4, 0, "WE ARE IN ARITH CHECK: Constraint: {:?}", constraint);

        let mut left_expr = Int::from_i64(0);
        for (var_name, coeff) in &constraint.left_expr {
            if let Some(z3_term) = coeff_to_z3_expr(var_name, coeff, &var_map) {
                left_expr += z3_term;
            }
        }

        // Build the right-hand side expression
        let mut right_expr = Int::from_i64(0);
        for (var_name, coeff) in &constraint.right_expr {
            if let Some(z3_term) = coeff_to_z3_expr(var_name, coeff, &var_map) {
                right_expr += z3_term;
            }
        }
        let lit = arithmetic_literals[constraint_idx];

        // Create the constraint based on whether it's an equality or inequality
        let constraint_ast = match constraint.function {
            Leq => {
                non_strict_inequalities.push((left_expr.clone(), right_expr.clone(), lit));
                Int::le(&left_expr, &right_expr)
            }
            Eq => Int::eq(&left_expr, &right_expr),
            Lt => Int::lt(&left_expr, &right_expr),
        };

        debug_println!(
            4,
            0,
            "WE ARE IN ARITH CHECK: Adding the constraint {}",
            constraint_ast
        );

        // Convert to boolean assumption - constraint_ast is already a Bool AST
        assumptions.push(constraint_ast.clone());

        let mut constraint = constraint.additional_constraint.clone().unwrap_or(vec![]);
        constraint.push(lit);
        constraint_to_literals.insert(constraint_ast, constraint);
    }

    // Check satisfiability with assumptions
    match solver.check_assumptions(&assumptions) {
        z3::SatResult::Sat => {
            // Satisfiable - return None to indicate no conflict
            let model = solver.get_model().unwrap();

            let mut model_hashmap: DeterministicHashMap<IBig, DeterministicHashSet<u64>> =
                DeterministicHashMap::new();
            for (var, value) in roots {
                let model_val = model.eval(&value, true).unwrap();
                let model_val_str = model_val.to_string();
                let val: IBig = if model_val_str.starts_with("(- ") {
                    let inner = &model_val_str[3..model_val_str.len() - 1];
                    -inner.parse::<IBig>().unwrap_or_else(|e| {
                        panic!(
                            "Failed to parse Z3 model value inner '{}' from '{}': {}",
                            inner, model_val_str, e
                        )
                    })
                } else {
                    model_val_str.parse::<IBig>().unwrap_or_else(|e| {
                        panic!("Failed to parse Z3 model value '{}': {}", model_val_str, e)
                    })
                };
                model_hashmap.entry(val).or_default().insert(var);
            }
            ArithResult::Sat(model_hashmap, LiaStats::new())
        }
        z3::SatResult::Unsat => {
            // Unsatisfiable - return the arithmetic literals that caused the conflict
            let unsat_core = solver.get_unsat_core();
            debug_println!(
                4,
                0,
                "WE ARE IN ARITH CHECK: Arithmetic literals: {:?}",
                arithmetic_literals
            );
            debug_println!(21, 4, "WE ARE IN ARITH CHECK: Unsat core: {:?}", unsat_core);

            let unsat_core_literals: Vec<i32> = unsat_core
                .iter()
                .flat_map(|ast| constraint_to_literals.get(ast).unwrap().clone())
                .collect();
            ArithResult::Unsat(unsat_core_literals, LiaStats::new())
        }
        z3::SatResult::Unknown => {
            // Z3 couldn't determine satisfiability - treat as satisfiable for now
            panic!("Z3 returns unknown")
        }
    }
}

fn convert_dashu_to_bigint(n: &IBig) -> num::BigInt {
    // SmtFunctionalities uses IBig, whereas z3-rs uses num::BigInt
    // Convert IBig to string and then parse as num::BigInt
    let n_str = n.to_string();
    num::BigInt::parse_bytes(n_str.as_bytes(), 10).unwrap()
}

/// Convert a (Coefficient, integer-coeff) pair into a Z3 Int expression.
fn coeff_to_z3_expr(
    coeff_key: &Coefficient,
    coeff_val: &IBig,
    var_map: &DeterministicHashMap<u32, Int>,
) -> Option<Int> {
    match coeff_key {
        Coefficient::Constant => Some(Int::from_big_int(&convert_dashu_to_bigint(coeff_val))),
        Coefficient::Term(id) => var_map
            .get(id)
            .map(|var| Int::from_big_int(&convert_dashu_to_bigint(coeff_val)) * var),
        Coefficient::Div(a, b) => {
            let a_var = var_map.get(a)?;
            let b_var = var_map.get(b)?;
            Some(Int::from_big_int(&convert_dashu_to_bigint(coeff_val)) * a_var.div(b_var))
        }
        Coefficient::Mod(a, b) => {
            let a_var = var_map.get(a)?;
            let b_var = var_map.get(b)?;
            Some(Int::from_big_int(&convert_dashu_to_bigint(coeff_val)) * a_var.modulo(b_var))
        }
    }
}
