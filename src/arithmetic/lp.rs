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
    Unsat(Vec<i32>, Vec<(u32, u32)>, LiaStats),
    Sat(
        DeterministicHashMap<IBig, DeterministicHashSet<u64>>,
        LiaStats,
    ),
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
}

/// Represents a linear constraint in the form: left_expr ≤ right_expr or left_expr = right_expr
#[derive(Debug, Clone)]
pub struct LinearConstraint {
    pub left_expr: DeterministicHashMap<Coefficient, Integer>, // variable name -> coefficient for left side
    pub right_expr: DeterministicHashMap<Coefficient, Integer>, // variable name -> coefficient for right side
    pub function: FunctionType, // true if it's an equality constraint
    pub additional_pairs: Option<Vec<(u32, u32)>>, // egraph ID pairs from explain_equality justifying term->root merges
}

impl LinearConstraint {
    /// Creates a new linear constraint
    pub fn new(
        left_expr: DeterministicHashMap<Coefficient, Integer>,
        right_expr: DeterministicHashMap<Coefficient, Integer>,
        function: FunctionType,
        additional_pairs: Vec<(u32, u32)>,
    ) -> Self {
        Self {
            left_expr,
            right_expr,
            function,
            additional_pairs: Some(additional_pairs),
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
/// along with egraph ID pairs from explain_equality that justify term->representative merges.
/// These pairs are returned raw (not converted to SAT literals) so that trichotomy
/// emission can be deferred to the caller — only needed if the arithmetic solver finds UNSAT.
/// TODO: simplify this, we might not need DeterministicHashMap representation for z3
pub fn extract_linear_expression(
    term_id: u64,
    solver_state: &mut SolverState,
) -> (DeterministicHashMap<Coefficient, Integer>, Vec<(u32, u32)>) {
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
            // Handle numeric constants
            if let Constant::Numeral(num) = c
                && let Ok(value) = num.to_string().parse::<Integer>()
            {
                // println!("We have the constant {} from {}", num, c);
                *expr.get_mut(&Coefficient::Constant).unwrap() = value;
            }
        }
        Global(..) => {
            // TODO: consider whether we need egraph.find() here for correctness when variables are merged
            expr.insert(
                Coefficient::Term(solver_state.to_egraph_id(term_id)),
                IBig::from(1),
            );
        }
        App(identifier, args, _) => {
            // Handle arithmetic operations
            match identifier.0.symbol.as_str() {
                "+" => {
                    // Addition: sum all arguments
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
                    // Multiplication: handle simple cases like c * x or x * c
                    if args.len() == 2 {
                        let (left_expr, additional_const_l) =
                            extract_linear_expression(args[0].uid(), solver_state);
                        let (right_expr, additional_const_r) =
                            extract_linear_expression(args[1].uid(), solver_state);

                        additional_constraints.extend(additional_const_l);
                        additional_constraints.extend(additional_const_r);
                        // Check if one is a constant and the other is a variable
                        if left_expr.len() == 1 && left_expr.contains_key(&Coefficient::Constant) {
                            // c * expr
                            let constant = &left_expr[&Coefficient::Constant];
                            for (var, coeff) in right_expr {
                                expr.insert(var, constant * coeff);
                            }
                        } else if right_expr.len() == 1
                            && right_expr.contains_key(&Coefficient::Constant)
                        {
                            // expr * c
                            let constant = &right_expr[&Coefficient::Constant];
                            for (var, coeff) in left_expr {
                                expr.insert(var, constant * coeff);
                            }
                        }
                    }
                }
                "-" => {
                    // Subtraction: handle unary and binary cases
                    if args.len() == 1 {
                        // Unary minus: -expr
                        let (arg_expr, additional_const) =
                            extract_linear_expression(args[0].uid(), solver_state);
                        additional_constraints.extend(additional_const);
                        for (var, coeff) in arg_expr {
                            expr.insert(var, -coeff);
                        }
                    } else if args.len() == 2 {
                        // Binary minus: left - right
                        let (left_expr, additional_const_l) =
                            extract_linear_expression(args[0].uid(), solver_state);
                        let (right_expr, additional_const_r) =
                            extract_linear_expression(args[1].uid(), solver_state);
                        additional_constraints.extend(additional_const_l);
                        additional_constraints.extend(additional_const_r);
                        // Add left expression
                        for (var, coeff) in left_expr {
                            expr.insert(var, coeff);
                        }

                        // Subtract right expression
                        for (var, coeff) in right_expr {
                            *expr.entry(var).or_insert(IBig::from(0)) -= coeff;
                        }
                    }
                }
                _ => {
                    let root_id = solver_state.egraph.find(solver_state.to_egraph_id(term_id));

                    if let Some(pairs) = solver_state
                        .egraph
                        .explain_equality(root_id, solver_state.to_egraph_id(term_id))
                    {
                        debug_println!(
                            21,
                            10,
                            "[ARITH CHECK] Uninterpreted expr: var_{} for term {}",
                            root_id,
                            term
                        );
                        additional_constraints.extend(pairs);
                        expr.insert(Coefficient::Term(root_id), IBig::from(1));
                    }
                }
            }
        }
        _ => {
            let root_id = solver_state.egraph.find(solver_state.to_egraph_id(term_id));
            if let Some(pairs) = solver_state
                .egraph
                .explain_equality(root_id, solver_state.to_egraph_id(term_id))
            {
                debug_println!(
                    21,
                    10,
                    "[ARITH CHECK] Uninterpreted expr: var_{} for term {}",
                    root_id,
                    term
                );
                additional_constraints.extend(pairs);
                expr.insert(Coefficient::Term(root_id), IBig::from(1));
            }
        }
    }

    (expr, additional_constraints)
}
