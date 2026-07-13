// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use dashu::integer::IBig;
// use z3::{ast::{Ast, Bool, Int}, Context, Solver};
use crate::arithmetic::lia::stats::Stats as LiaStats;
use crate::arithmetic::lialp::check_integer_constraints_satisfiable_lia;
#[cfg(feature = "z3-solver")]
use crate::arithmetic::z3lp::check_integer_constraints_satisfiable_z3;
use crate::debug_println;
use crate::egraphs::EgraphTrait;
use crate::solver_state::SolverState;
use crate::utils::{DeterministicHashMap, DeterministicHashSet};
use clap::ValueEnum;
use dashu::Integer;
use std::fmt;
use std::fmt::Display;
use std::str::FromStr;
use yaspar_ir::ast::alg::Constant;
use yaspar_ir::ast::{
    ATerm::{self, App, Eq, Global, Not},
    Repr,
};

#[derive(Debug, Clone, ValueEnum)]
pub enum ArithSolver {
    Internal,
    #[cfg(feature = "z3-solver")]
    Z3,
    None,
}

impl Display for ArithSolver {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ArithSolver::Internal => "internal".fmt(f),
            #[cfg(feature = "z3-solver")]
            ArithSolver::Z3 => "z3".fmt(f),
            ArithSolver::None => "none".fmt(f),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ArithSolverParseError {
    pub invalid_input: String,
}

impl fmt::Display for ArithSolverParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Invalid ArithSolver: '{}'. Valid options are: 'internal', 'z3', 'none'",
            self.invalid_input
        )
    }
}

pub enum ArithResult {
    Unsat(Vec<i32>, LiaStats), // conflict clause
    Sat(
        DeterministicHashMap<IBig, DeterministicHashSet<u64>>,
        LiaStats,
    ), // literals that correspond to inequalities <= where the two terms are equal
    None,
}

impl std::error::Error for ArithSolverParseError {}

impl FromStr for ArithSolver {
    type Err = ArithSolverParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "internal" => Ok(ArithSolver::Internal),
            #[cfg(feature = "z3-solver")]
            "z3" => Ok(ArithSolver::Z3),
            "none" => Ok(ArithSolver::None),
            _ => Err(ArithSolverParseError {
                invalid_input: s.to_string(),
            }),
        }
    }
}

pub fn check_integer_constraints_satisfiable(
    arith_solver: &ArithSolver,
    terms: &[i32],
    // TODO: lialp: check that taking egraph mutable is okay
    solver_state: &mut SolverState,
) -> ArithResult {
    match arith_solver {
        ArithSolver::Internal => check_integer_constraints_satisfiable_lia(terms, solver_state),
        #[cfg(feature = "z3-solver")]
        ArithSolver::Z3 => check_integer_constraints_satisfiable_z3(terms, solver_state),
        ArithSolver::None => ArithResult::None,
    }
}

#[derive(Debug, Clone)]
pub enum FunctionType {
    Leq,
    Lt,
    Eq,
}

#[derive(Eq, PartialEq, Debug, Clone, Ord, PartialOrd, Hash, Copy)]
pub enum Coefficient {
    Term(u32),
    Constant,
    /// Integer division (div a b) — stores egraph IDs of numerator and denominator
    Div(u32, u32),
    /// Integer modulo (mod a b) — stores egraph IDs of numerator and denominator
    Mod(u32, u32),
}

/// Represents a linear constraint in the form: left_expr ≤ right_expr or left_expr = right_expr
#[derive(Debug, Clone)]
pub struct LinearConstraint {
    pub left_expr: DeterministicHashMap<Coefficient, Integer>, // variable name -> coefficient for left side
    pub right_expr: DeterministicHashMap<Coefficient, Integer>, // variable name -> coefficient for right side
    pub function: FunctionType, // true if it's an equality constraint
    pub additional_constraint: Option<Vec<i32>>, // potentially carries additional constraints created by replacing a literal with its root
}

impl LinearConstraint {
    /// Creates a new linear constraint
    pub fn new(
        left_expr: DeterministicHashMap<Coefficient, Integer>,
        right_expr: DeterministicHashMap<Coefficient, Integer>,
        function: FunctionType,
        additional_constraint: Vec<i32>,
    ) -> Self {
        Self {
            left_expr,
            right_expr,
            function,
            additional_constraint: Some(additional_constraint),
        }
    }
}

// fn linear_constraint_to_term(constraint: LinearConstraint) -> Term {

// }

/// Extracts linear constraints from SMT terms
/// This is a simplified version that handles basic arithmetic constraints
pub fn extract_linear_constraints(
    terms: &[i32],
    solver_state: &mut SolverState,
) -> (Vec<LinearConstraint>, Vec<i32>) {
    let mut constraints = Vec::new();
    let mut arithmetic_literals = vec![];

    for &lit in terms {
        let (term_id, polarity) = solver_state.get_u64_from_lit_with_polarity(lit);
        if let Some(constraint) = extract_constraint_from_term(term_id, polarity, solver_state) {
            debug_println!(21, 4, "We get the constraint {:?}", constraint);
            constraints.push(constraint);
            arithmetic_literals.push(-lit);
        }
    }

    (constraints, arithmetic_literals)
}

/// Extracts a single linear constraint from an SMT term
fn extract_constraint_from_term(
    term_id: u64,
    polarity: bool,
    solver_state: &mut SolverState,
) -> Option<LinearConstraint> {
    let term = solver_state.get_term(term_id);
    debug_println!(
        21,
        6,
        "[ARITH CHECK] Extracting linear constraint for term {}",
        term
    );

    // flip the polarity if the term is a negation
    let (term, polarity) = match term.repr() {
        Not(term) => (term, !polarity),
        _ => (&term, polarity),
    };

    match term.repr() {
        App(identifier, args, _) if !polarity => {
            debug_println!(
                2,
                0,
                "[ARITH CHECK] Extracting linear constraint for NOT APP term {}",
                term
            );
            if args.len() != 2 {
                return None;
            }
            let (left_expr, additional_constraint_l) =
                extract_linear_expression(args[0].uid(), solver_state);
            let (right_expr, additional_constraint_r) =
                extract_linear_expression(args[1].uid(), solver_state);
            let mut additional_constraint = vec![];
            additional_constraint.extend(additional_constraint_l);
            additional_constraint.extend(additional_constraint_r);
            // Handle comparison operators: <=, >=, <, >, =
            match identifier.0.symbol.as_str() {
                "<=" => {
                    // ~ (a <= b) -> a > b
                    Some(LinearConstraint::new(
                        right_expr,
                        left_expr,
                        FunctionType::Lt,
                        additional_constraint,
                    ))
                }
                ">=" => {
                    // ~ (a >= b) -> a < b
                    Some(LinearConstraint::new(
                        left_expr,
                        right_expr,
                        FunctionType::Lt,
                        additional_constraint,
                    ))
                }
                "<" => {
                    // ~ (a < b) -> a >= b
                    Some(LinearConstraint::new(
                        right_expr,
                        left_expr,
                        FunctionType::Leq,
                        additional_constraint,
                    ))
                }
                ">" => {
                    // ~ (a > b) -> a <= b
                    Some(LinearConstraint::new(
                        left_expr,
                        right_expr,
                        FunctionType::Leq,
                        additional_constraint,
                    ))
                }
                _ => None,
            }
        }
        App(identifier, args, _) if polarity => {
            debug_println!(
                2,
                0,
                "[ARITH CHECK] Extracting linear constraint for APP term {}",
                term
            );
            if args.len() != 2 {
                return None;
            }
            let (left_expr, additional_constraint_l) =
                extract_linear_expression(args[0].uid(), solver_state);
            let (right_expr, additional_constraint_r) =
                extract_linear_expression(args[1].uid(), solver_state);
            let mut additional_constraint = vec![];
            additional_constraint.extend(additional_constraint_l);
            additional_constraint.extend(additional_constraint_r);
            // Handle comparison operators: <=, >=, <, >, =
            match identifier.0.symbol.as_str() {
                "<=" => Some(LinearConstraint::new(
                    left_expr,
                    right_expr,
                    FunctionType::Leq,
                    additional_constraint,
                )),
                ">=" => Some(LinearConstraint::new(
                    right_expr,
                    left_expr,
                    FunctionType::Leq,
                    additional_constraint,
                )),
                "<" => Some(LinearConstraint::new(
                    left_expr,
                    right_expr,
                    FunctionType::Lt,
                    additional_constraint,
                )),
                ">" => Some(LinearConstraint::new(
                    right_expr,
                    left_expr,
                    FunctionType::Lt,
                    additional_constraint,
                )),
                _ => None,
            }
        }
        Eq(a, b) if polarity => {
            debug_println!(
                2,
                0,
                "[ARITH CHECK] Extracting linear constraint for EQ term {}",
                term
            );
            let (left_expr, additional_constraint_l) =
                extract_linear_expression(a.uid(), solver_state);
            let (right_expr, additional_constraint_r) =
                extract_linear_expression(b.uid(), solver_state);
            let mut additional_constraint = vec![];
            additional_constraint.extend(additional_constraint_l);
            additional_constraint.extend(additional_constraint_r);
            Some(LinearConstraint::new(
                left_expr,
                right_expr,
                FunctionType::Eq,
                additional_constraint,
            ))
        }
        // note we handle negations of equality via nelson oppen theory combination
        // Eq(a, b) if !polarity => { todo!()}
        _ => None,
    }
}

/// Extracts a linear expression from an SMT term
/// Returns a DeterministicHashMap mapping variable names to coefficients,
/// along with negated equality literals corresponding to term->representative merges.
/// TODO: simplify this, we might not need DeterministicHashMap representation for z3
pub fn extract_linear_expression(
    term_id: u64,
    solver_state: &mut SolverState,
) -> (DeterministicHashMap<Coefficient, Integer>, Vec<i32>) {
    debug_println!(
        21,
        8,
        "[ARITH CHECK] Extracting linear expression for term {:?}",
        solver_state.get_term(term_id)
    );
    let term = solver_state.get_term(term_id);
    let mut expr = DeterministicHashMap::new();
    expr.insert(Coefficient::Constant, IBig::from(0));
    let mut additional_constraints = vec![];
    match term.repr() {
        ATerm::Constant(c, _) => {
            if let Constant::Numeral(num) = c {
                let value = num
                    .to_string()
                    .parse::<Integer>()
                    .unwrap_or_else(|e| panic!("failed to parse numeral {}: {}", num, e));
                *expr.get_mut(&Coefficient::Constant).unwrap() = value;
            } else {
                panic!(
                    "non-numeric constant in arithmetic expression: {}",
                    solver_state.get_term(term_id)
                );
            }
        }
        Global(..) => {
            expr.insert(
                Coefficient::Term(solver_state.to_egraph_id(term_id)),
                IBig::from(1),
            );
        }
        App(identifier, args, _) => match identifier.0.symbol.as_str() {
            "+" => {
                for arg_id in args.iter() {
                    let (arg_expr, additional_const) =
                        extract_linear_expression(arg_id.uid(), solver_state);
                    additional_constraints.extend(additional_const);
                    for (var, coeff) in arg_expr {
                        if var != Coefficient::Constant {
                            *expr.entry(var).or_insert(IBig::from(0)) += coeff;
                        } else {
                            *expr.get_mut(&Coefficient::Constant).unwrap() += coeff;
                        }
                    }
                }
            }
            "*" => {
                assert!(
                    args.len() == 2,
                    "expected multiplication to have exactly 2 arguments, got {}",
                    args.len()
                );
                let (left_expr, additional_const_l) =
                    extract_linear_expression(args[0].uid(), solver_state);
                let (right_expr, additional_const_r) =
                    extract_linear_expression(args[1].uid(), solver_state);

                additional_constraints.extend(additional_const_l);
                additional_constraints.extend(additional_const_r);

                let left_is_const =
                    left_expr.len() == 1 && left_expr.contains_key(&Coefficient::Constant);
                let right_is_const =
                    right_expr.len() == 1 && right_expr.contains_key(&Coefficient::Constant);

                if left_is_const {
                    let constant = &left_expr[&Coefficient::Constant];
                    for (var, coeff) in right_expr {
                        expr.insert(var, constant * coeff);
                    }
                } else if right_is_const {
                    let constant = &right_expr[&Coefficient::Constant];
                    for (var, coeff) in left_expr {
                        expr.insert(var, constant * coeff);
                    }
                } else {
                    panic!(
                        "non-linear multiplication is not supported: (* {} {})",
                        solver_state.get_term(args[0].uid()),
                        solver_state.get_term(args[1].uid()),
                    );
                }
            }
            "-" => {
                assert!(!args.is_empty(), "expected subtraction to have arguments");
                if args.len() == 1 {
                    let (arg_expr, additional_const) =
                        extract_linear_expression(args[0].uid(), solver_state);
                    additional_constraints.extend(additional_const);
                    for (var, coeff) in arg_expr {
                        expr.insert(var, -coeff);
                    }
                } else {
                    let (first_expr, additional_const_first) =
                        extract_linear_expression(args[0].uid(), solver_state);
                    additional_constraints.extend(additional_const_first);
                    for (var, coeff) in first_expr {
                        *expr.entry(var).or_insert(IBig::from(0)) += coeff;
                    }
                    for arg in args.iter().skip(1) {
                        let (arg_expr, additional_const) =
                            extract_linear_expression(arg.uid(), solver_state);
                        additional_constraints.extend(additional_const);
                        for (var, coeff) in arg_expr {
                            *expr.entry(var).or_insert(IBig::from(0)) -= coeff;
                        }
                    }
                }
            }
            "div" => {
                assert!(args.len() == 2, "div requires exactly 2 arguments");
                let raw_numerator_id = solver_state.to_egraph_id(args[0].uid());
                let numerator_id = solver_state.egraph.find(raw_numerator_id);
                if let Some(negated_model) = solver_state
                    .egraph
                    .explain_equality(numerator_id, raw_numerator_id)
                {
                    let model_terms: Vec<i32> = negated_model
                        .into_iter()
                        .map(|x| -solver_state.make_eq(x.0, x.1))
                        .collect();
                    additional_constraints.extend(model_terms);
                }
                let denominator_id = solver_state.to_egraph_id(args[1].uid());
                expr.insert(
                    Coefficient::Div(numerator_id, denominator_id),
                    IBig::from(1),
                );
            }
            "mod" => {
                assert!(args.len() == 2, "mod requires exactly 2 arguments");
                let raw_numerator_id = solver_state.to_egraph_id(args[0].uid());
                let numerator_id = solver_state.egraph.find(raw_numerator_id);
                if let Some(negated_model) = solver_state
                    .egraph
                    .explain_equality(numerator_id, raw_numerator_id)
                {
                    let model_terms: Vec<i32> = negated_model
                        .into_iter()
                        .map(|x| -solver_state.make_eq(x.0, x.1))
                        .collect();
                    additional_constraints.extend(model_terms);
                }
                let denominator_id = solver_state.to_egraph_id(args[1].uid());
                expr.insert(
                    Coefficient::Mod(numerator_id, denominator_id),
                    IBig::from(1),
                );
            }
            _ => {
                let root_id = solver_state.egraph.find(solver_state.to_egraph_id(term_id));
                if let Some(negated_model) = solver_state
                    .egraph
                    .explain_equality(root_id, solver_state.to_egraph_id(term_id))
                {
                    let model_terms: Vec<i32> = negated_model
                        .into_iter()
                        .map(|x| -solver_state.make_eq(x.0, x.1))
                        .collect();
                    additional_constraints.extend(model_terms);
                }
                debug_println!(
                    21,
                    10,
                    "[ARITH CHECK] Uninterpreted expr: var_{} for term {}",
                    root_id,
                    term
                );
                expr.insert(Coefficient::Term(root_id), IBig::from(1));
            }
        },
        _ => {
            let root_id = solver_state.egraph.find(solver_state.to_egraph_id(term_id));
            if let Some(negated_model) = solver_state
                .egraph
                .explain_equality(root_id, solver_state.to_egraph_id(term_id))
            {
                let model_terms: Vec<i32> = negated_model
                    .into_iter()
                    .map(|x| -solver_state.make_eq(x.0, x.1))
                    .collect();
                additional_constraints.extend(model_terms);
            }
            debug_println!(
                21,
                10,
                "[ARITH CHECK] Uninterpreted expr: var_{} for term {}",
                root_id,
                term
            );
            expr.insert(Coefficient::Term(root_id), IBig::from(1));
        }
    }

    (expr, additional_constraints)
}
