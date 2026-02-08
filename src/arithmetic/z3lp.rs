use crate::egraphs::egraph::Egraph;
use crate::{
    arithmetic::lp::{
        extract_linear_constraints, extract_linear_expression, ArithResult, Coefficient,
        FunctionType::*,
    },
    egraphs::proofforest::ProofForestEdge,
    utils::{DeterministicHashMap, DeterministicHashSet},
};
use dashu::integer::IBig;
use std::collections::HashMap;
use z3::{
    ast::{Ast, Bool, Int},
    Solver,
};

/// Checks if a conjunction of integer constraints is satisfiable using Z3
pub fn check_integer_constraints_satisfiable_z3(terms: &[i32], egraph: &mut Egraph) -> ArithResult {
    let (constraints, arithmetic_literals) = extract_linear_constraints(terms, egraph);

    if constraints.is_empty() && arithmetic_literals.is_empty() {
        return ArithResult::None; // No constraints means trivially satisfiable
    }

    debug_println!(21, 4, "trying to solve with constraints: {:?}", constraints);
    debug_println!(21, 4, "and arithmetic literals {:?}", arithmetic_literals);

    // Create Z3 solver;
    let solver = Solver::new();

    // Collect all unique variable names and create Z3 variables
    let mut variables = std::collections::HashSet::new();
    for constraint in &constraints {
        for var_name in constraint.left_expr.keys() {
            if var_name != &Coefficient::Constant {
                variables.insert(*var_name);
            }
        }
        for var_name in constraint.right_expr.keys() {
            if var_name != &Coefficient::Constant {
                variables.insert(*var_name);
            }
        }
    }

    let mut var_map = DeterministicHashMap::new();
    for var in variables {
        let var_name = match var {
            Coefficient::Constant => "__constant__".to_string(),
            Coefficient::Term(id) => format!("var_{}", id),
        };
        let z3_var = Int::new_const(var_name);
        var_map.entry(var).or_insert(z3_var);
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
    for term_id in egraph.arithmetic_terms.clone() {
        // todo: see if I can avoid cloning
        if let ProofForestEdge::Root { .. } = &egraph.proof_forest[term_id as usize] {
            let left_expr = Int::new_const(format!("var_{}", term_id));

            roots.push((term_id, left_expr.clone()));
            let (right, literals) = extract_linear_expression(term_id, egraph);

            // Build the right-hand side expression
            let mut right_expr = Int::from_i64(0);
            for (var_name, coeff) in right.iter() {
                if var_name != &Coefficient::Constant {
                    if let Some(var) = var_map.get(var_name) {
                        let coeff_int = Int::from_big_int(&convert_dashu_to_bigint(coeff));
                        right_expr += coeff_int * var;
                    }
                } else {
                    let const_term = Int::from_big_int(&convert_dashu_to_bigint(coeff));
                    right_expr += const_term;
                }
            }
            let constraint = Int::_eq(&left_expr, right_expr);

            assumptions.push(constraint.clone());
            constraint_to_literals.insert(constraint, literals);
        }
    }

    for (constraint_idx, constraint) in constraints.iter().enumerate() {
        debug_println!(4, 0, "WE ARE IN ARITH CHECK: Constraint: {:?}", constraint);

        let mut left_expr = Int::from_i64(0);
        for (var_name, coeff) in &constraint.left_expr {
            if var_name != &Coefficient::Constant {
                if let Some(var) = var_map.get(var_name) {
                    let coeff_int = Int::from_big_int(&convert_dashu_to_bigint(coeff));
                    left_expr += coeff_int * var;
                }
            } else {
                let const_term = Int::from_big_int(&convert_dashu_to_bigint(coeff));
                left_expr += const_term;
            }
        }

        // Build the right-hand side expression
        let mut right_expr = Int::from_i64(0);
        for (var_name, coeff) in &constraint.right_expr {
            if var_name != &Coefficient::Constant {
                if let Some(var) = var_map.get(var_name) {
                    let coeff_int = Int::from_big_int(&convert_dashu_to_bigint(coeff));
                    right_expr += coeff_int * var;
                }
            } else {
                let const_term = Int::from_big_int(&convert_dashu_to_bigint(coeff));
                right_expr += const_term;
            }
        }
        let lit = arithmetic_literals[constraint_idx];

        // Create the constraint based on whether it's an equality or inequality
        let constraint_ast = match constraint.function {
            Leq => {
                non_strict_inequalities.push((left_expr.clone(), right_expr.clone(), lit));
                Int::le(&left_expr, &right_expr)
            }
            Eq => Int::_eq(&left_expr, &right_expr),
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

            let mut model_hashmap: DeterministicHashMap<i64, DeterministicHashSet<u64>> =
                DeterministicHashMap::new();
            for (var, value) in roots {
                // todo: I think I can do this just for the roots I saved earlier
                let model_val = model.eval(&value, true).unwrap();
                let model_val_i64 = model_val.as_i64().unwrap_or(i64::MAX);
                model_hashmap.entry(model_val_i64).or_default().insert(var);
            }
            ArithResult::Sat(model_hashmap)
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
            let unsat_core_literals = unsat_core
                .iter()
                .flat_map(|ast| constraint_to_literals.get(ast).unwrap().clone())
                .collect();
            ArithResult::Unsat(unsat_core_literals)
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
