// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Conversion of SMT text to parser AST and then to [LinearSystem] relations
//! and solver objects.

use log;
use std::collections;
use std::fmt::{self, Display};
use std::ops;

use yaspar_ir::ast::{self as smt_ast, FetchSort};
use yaspar_ir::ast::{AConstant, ATerm};
use yaspar_ir::ast::{Context, LetElim, Term, Typecheck};
use yaspar_ir::traits::Repr;
use yaspar_ir::untyped::{Command, UntypedAst};

use crate::arithmetic::lia::context::ConvContext;
use crate::arithmetic::lia::linear_system::{
    Addend, Constraint, LinearSystem, LinearSystemError, Rel, combine_terms_helper,
};
use crate::arithmetic::lia::lira_solver::LIRASolver;
use crate::arithmetic::lia::lra_solver::LRASolver;
use crate::arithmetic::lia::preprocess::{PreprocessResult, preprocess};
use crate::arithmetic::lia::solver_result::{Conflict, SolverDecision, SolverError, default_model};
use crate::arithmetic::lia::solver_result_api::SolverDecisionApi;
use crate::arithmetic::lia::tableau_dense::TableauDense;
use crate::arithmetic::lia::types::{FBig, Integer, Rational, UBig};
use crate::arithmetic::lia::variables::VarType;

/// Error type for conversion issues from [Term] to [Rel]
#[derive(Debug)]
pub struct FrontendError(pub String);

impl Display for FrontendError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::error::Error for FrontendError {}

impl From<String> for FrontendError {
    fn from(msg: String) -> Self {
        FrontendError(msg)
    }
}

impl From<SolverError> for FrontendError {
    fn from(err: SolverError) -> Self {
        Self(err.to_string())
    }
}

impl From<LinearSystemError> for FrontendError {
    fn from(le: LinearSystemError) -> Self {
        FrontendError(format!("error building LRA solver: {}", le))
    }
}

type FrontendResult<R> = Result<R, FrontendError>;

/// Linear expression represented by a list of [Addends] implicitly added together
struct LinExpr(pub Vec<Addend<Rational>>);

impl LinExpr {
    /// Determine if the expression, regarded as a polynomial function, is a constant, and if
    /// so, return it.
    fn is_constant(&self) -> Option<Rational> {
        let (terms, const_sum) = Addend::separate_addends(&self.0);
        // Normalize the terms by collecting variable coefficients and filtering out
        // resulting entries with coefficient zero; e.g. x0 - x0 is constant as a
        // polynomial function
        if !combine_terms_helper(&terms).is_empty() {
            None
        } else {
            Some(const_sum)
        }
    }
}

impl ops::Add<LinExpr> for LinExpr {
    type Output = Self;

    fn add(self, rhs: LinExpr) -> Self {
        Self(self.0.into_iter().chain(rhs.0).collect())
    }
}

impl ops::Neg for LinExpr {
    type Output = Self;

    fn neg(self) -> Self {
        Self(self.0.into_iter().map(|a| -a).collect())
    }
}

impl ops::Mul<&Rational> for LinExpr {
    type Output = Self;

    fn mul(self, rhs: &Rational) -> Self {
        Self(self.0.into_iter().map(|a| a * rhs).collect())
    }
}

impl ops::Div<&Rational> for LinExpr {
    type Output = Self;

    fn div(self, rhs: &Rational) -> Self {
        Self(self.0.into_iter().map(|a| a / rhs).collect())
    }
}

// Arithmetic operator symbols for matching
const PLUS_SYMBOL: &str = "+";
const NEG_SYMBOL: &str = "-";
const MULT_SYMBOL: &str = "*";
const REAL_DIV_SYMBOL: &str = "/";
const INT_DIV_SYMBOL: &str = "div";
const TO_REAL_SYMBOL: &str = "to_real";
// Note: to_int and is_int are not supported

// Arithmetic relation symbols for matching
const EQ_SYMBOL: &str = "=";
const LE_SYMBOL: &str = "<=";
const LT_SYMBOL: &str = "<";
const GE_SYMBOL: &str = ">=";
const GT_SYMBOL: &str = ">";

// Sort names
// const BOOL_SORT: &str = "Bool";

/// Convert a term to a linear expression represented as a vector of [Addend]s.
///
/// This function takes an SMT term representing a linear-affine expression and
/// converts it to a vector of [Addend]s, suitable for building [Rel]ations and
/// for use in the linear system solver.
///
/// # Arguments
/// * `term` - The SMT term to convert to a linear expression
///
/// Note: [Term] is an `HConsed<RTerm>`, [RTerm] is a wrapper around `alg::raw::Term<...>`
///
/// # Returns
/// A `Result` containing either:
/// - `Ok(Vec<Mon<Rational>>)` - Vector of monomials representing the linear expression
/// - `Err(String)` - Error message if the conversion fails
///
/// TODO: add source metadata to conversion errors
/// TODO: support left-associating -, +, *, /
fn convert_linear_term(ctx: &mut ConvContext, term: &Term) -> FrontendResult<LinExpr> {
    // println!("converting the term {}", term);
    match term.get().repr() {
        ATerm::Constant(c, _) => Ok(LinExpr(vec![c.convert_constant()?])),
        // handle variables
        ATerm::Global(smt_ast::alg::QualifiedIdentifier(id, _), sort) => {
            let name = id.symbol.get();
            let var_typ = match sort {
                Some(hs) => {
                    let rsort = hs.get();
                    let name = rsort.sort_name().get().as_str();
                    let ind = &rsort.1;
                    debug_assert!(ind.is_empty()); // expect no sort parameters
                    if name == "Real" {
                        VarType::Real
                    } else if name == "Int" {
                        VarType::Int
                    } else {
                        // println!("{}", term);
                        unreachable!() // unreachable assuming type checking and logic is set correctly
                    }
                }
                None => {
                    panic!("no sort information for {name}")
                }
            };
            let var = ctx.allocate_var_term(name, var_typ, term.clone());

            Ok(LinExpr(vec![Addend::term(Rational::ONE, var)]))
        }
        // handle +, *, -, /
        ATerm::App(smt_ast::alg::QualifiedIdentifier(op_id, _op_sort), args, app_sort) => {
            let op_name = op_id.symbol.get();
            match op_name.as_str() {
                PLUS_SYMBOL => {
                    let expr_args = args
                        .iter()
                        .map(|a| convert_linear_term(ctx, a).map(|l| l.0))
                        .collect::<Result<Vec<_>, _>>()?;
                    Ok(LinExpr(expr_args.into_iter().flatten().collect())) // flattening implicitly adds the terms in our rep'n
                }
                NEG_SYMBOL => {
                    debug_assert!(!args.is_empty(), "expected negation to have arguments");
                    let mut expr_args: Vec<LinExpr> = args
                        .iter()
                        .map(|a| convert_linear_term(ctx, a))
                        .collect::<Result<Vec<_>, _>>()?;
                    if expr_args.len() == 1 {
                        // (- a) := -a
                        Ok(-expr_args.remove(0))
                    } else {
                        // (- a b c) := (a - b) - c = a + (-(b + c))
                        let first = expr_args.swap_remove(0);
                        let subtractant =
                            -LinExpr(expr_args.into_iter().flat_map(|l| l.0).collect());
                        Ok(first + subtractant)
                    }
                }
                MULT_SYMBOL => {
                    debug_assert!(
                        args.len() == 2,
                        "chainable multiplication ops are not supported"
                    );
                    let e1 = convert_linear_term(ctx, &args[0])?;
                    let e2 = convert_linear_term(ctx, &args[1])?;
                    if let Some(c) = e1.is_constant() {
                        Ok(e2 * &c)
                    } else if let Some(c) = e2.is_constant() {
                        Ok(e1 * &c)
                    } else {
                        Err(FrontendError(
                            "non-linear multiplication is not supported".to_string(),
                        ))
                    }
                }
                REAL_DIV_SYMBOL | INT_DIV_SYMBOL => {
                    debug_assert!(args.len() == 2, "chainable division is not supported");
                    let e1 = convert_linear_term(ctx, &args[0])?;
                    let e2 = convert_linear_term(ctx, &args[1])?;
                    // e1 / e2 is linear iff. e2 is constant
                    if let Some(c) = e2.is_constant() {
                        Ok(e1 / &c)
                    } else {
                        Err(FrontendError(
                            "non-linear division is not supported".to_string(),
                        ))
                    }
                }
                TO_REAL_SYMBOL => {
                    // the types of non-variable terms are effectively erased, so
                    // to_real is a no-op. As far as the solver is concerned, variables
                    // have type constraints, but all arithmetic is rational.
                    Ok(convert_linear_term(ctx, &args[0])?)
                }
                _op => {
                    // method to create a variable for an uninterpreted function based on its type
                    let var_t = ctx.allocate_term(term.clone(), None, app_sort.clone());
                    Ok(LinExpr(vec![Addend::term(Rational::ONE, var_t)])) // Integer one as rational
                }
            }
        }

        ATerm::Ite(_, t1, _) => {
            // we are treating ite as an uninterpreted function
            // don't know the sort so letting it be 0
            let sort = t1.get_sort(&mut Context::new());
            // println!("we have ite {} with sort {}", term, sort);
            let var_t = ctx.allocate_term(term.clone(), None, Some(sort));
            Ok(LinExpr(vec![Addend::term(Rational::ONE, var_t)])) // Integer one as rational
        }

        // everything else is unreachable for QF_LIA, QF_LRA _terms_
        _ => unreachable!(),
    }
}

/// Generic constant converter allows us to ignore the flexible string type parameter
trait NumConstantConverter {
    fn convert_constant(&self) -> Result<Addend<Rational>, FrontendError>;
}

impl<Str> NumConstantConverter for AConstant<Str> {
    /// Convert a constant term to an [Addend]
    fn convert_constant(&self) -> Result<Addend<Rational>, FrontendError> {
        match self {
            // note: numerals are non-negative
            // TODO: only possible numeral conversion is str -> str :(
            AConstant::Numeral(i) => Ok(Addend::Constant(Rational::from(i.clone()))),
            AConstant::Decimal(d) => Ok(Addend::Constant(convert_dbig(d)?)),
            _ => unreachable!(),
        }
    }
}

/// Convert an high precision floating point number into an arbitrary precision rational; the operation
/// is lossless.
fn convert_dbig(
    d: &FBig<crate::arithmetic::lia::types::float::round::mode::HalfAway, 10>,
) -> FrontendResult<Rational> {
    // express d = significant * 10^exponent
    let drepr = d.repr();
    let exponent = drepr.exponent();
    if exponent >= 0 {
        Ok(Rational::from(drepr.significand().clone())
            * Integer::from(10u32).pow(exponent as usize))
    } else {
        let uexp = usize::try_from(exponent.abs()).map_err(|_| {
            FrontendError(format!(
                "convert_dbig: failed to convert negative exponent: {exponent}"
            ))
        })?;
        Ok(Rational::from_parts(
            drepr.significand().clone(),
            UBig::from(10u32).pow(uexp),
        ))
    }
}

/// Try to convert a relation string into a [Constraint]
fn convert_constraint(symbol: &str) -> FrontendResult<Constraint> {
    match symbol {
        EQ_SYMBOL => Ok(Constraint::Eq),
        LE_SYMBOL => Ok(Constraint::Le),
        LT_SYMBOL => Ok(Constraint::Lt),
        GE_SYMBOL => Ok(Constraint::Ge),
        GT_SYMBOL => Ok(Constraint::Gt),
        _ => Err(FrontendError(format!(
            "expected relation symbol {:?}",
            symbol
        ))),
    }
}
/// Convert a term to a linear relation.
///
/// This function takes an SMT term representing an arithmetic relation (=, >=, ...)
/// and converts it to a linear relation that can be used in the linear system solver.
///
/// Return type has the Option to return None when the term in question can be ignored, e.g.
/// boolean literals from an implicant.
fn convert_relation(ctx: &mut ConvContext, term: &Term) -> FrontendResult<Option<Rel<Rational>>> {
    // println!("in convert relation {}", term);
    match term.repr() {
        // handle =, >=, >, <=, <
        ATerm::App(smt_ast::alg::QualifiedIdentifier(rel_id, _op_sort), args, _app_sort) => {
            // println!("in app {}", term);
            if *rel_id.symbol != ">="
                && *rel_id.symbol != ">"
                && *rel_id.symbol != "<="
                && *rel_id.symbol != "<"
            {
                // println!("returning ok(none)");
                return Ok(None);
            }
            // TODO: support left-assoc (in)equality?
            debug_assert!(
                args.len() == 2,
                "left-associative form of (in)equality is not supported"
            );
            let lhs = convert_linear_term(ctx, &args[0])?;
            let rhs = convert_linear_term(ctx, &args[1])?;
            let rel_name = rel_id.symbol.get().as_str();
            let constraint = convert_constraint(rel_name)?;
            Ok(Some(Rel::from_addends_lhs_rhs(lhs.0, constraint, rhs.0)))
        }
        // handle term identifiers
        ATerm::Global(smt_ast::alg::QualifiedIdentifier(_id, _sort), _) => {
            // The following is some validation, but we return Ok(None) anyway,
            // having nothing to convert.
            //
            // let name = id.symbol.get();
            // let sort_name = sort
            //     .as_ref()
            //     .ok_or(FrontendError(format!("missing sort for symbol {}", name)))?
            //     .get()
            //     .0
            //     .0
            //     .symbol
            //     .get()
            //     .as_str(); // behold the tower of dots
            // if sort_name != BOOL_SORT {
            //     return Err(FrontendError(format!(
            //         "unsupported literal '{}', sort '{}'",
            //         name, sort_name
            //     )));
            // }
            // println!("returning ok(none)");
            Ok(None)
        }
        // Equality is represented above the literal level
        ATerm::Eq(t1, t2) => {
            if (t1.get_sort(&mut Context::new()).sort_name().as_str() != "Real"
                && t1.get_sort(&mut Context::new()).sort_name().as_str() != "Int")
                || (t2.get_sort(&mut Context::new()).sort_name().as_str() != "Real"
                    && t2.get_sort(&mut Context::new()).sort_name().as_str() != "Int")
            {
                // println!("returning ok(none)");
                return Ok(None);
            }
            let lhs = convert_linear_term(ctx, t1)?;
            let rhs = convert_linear_term(ctx, t2)?;
            Ok(Some(Rel::from_addends_lhs_rhs(
                lhs.0,
                Constraint::Eq,
                rhs.0,
            )))
        }
        ATerm::Not(t) => {
            // TODO: Not handling is done identically at two levels
            if let Some(rel) = convert_relation(ctx, t)? {
                Ok(rel.negate())
            } else {
                Ok(None)
            }
        }
        _ => Ok(None), // Err(FrontendError(format!("expected relation term {:?}", term))),
    }
}

fn convert_arith_literal(
    ctx: &mut ConvContext,
    term: &Term,
) -> FrontendResult<Option<Rel<Rational>>> {
    // println!("in convert arith_literal with {}", term);

    // if let Ok(Some(t)) = result {
    //     println!("(assert {})", t);
    // };
    match term.get().repr() {
        // ignore annotations
        ATerm::Annotated(t, _) => convert_relation(ctx, t),
        // handle arithmetic relations
        ATerm::App(..) | ATerm::Eq(..) => convert_relation(ctx, term),
        // handle negated literals
        ATerm::Not(t) => {
            if let Some(rel) = convert_relation(ctx, t)? {
                Ok(rel.negate())
            } else {
                Ok(None)
            }
        }
        _ => Ok(None),
        // Err(FrontendError(format!(
        //     "expected arithmetic literal, but got: {:?}",
        //     term
        // ))),
    }
}

/// Type-check and eliminate let bindings from all assertion commands in a script.
///
/// This function processes a vector of parser commands, converting them to the internal
/// AST representation, type-checking them, and eliminating let bindings. Only assertion
/// commands are processed and returned as terms. The logic is also validated.
///
/// # Arguments
/// * `context` - Mutable reference to the SMT context for type checking and conversion
/// * `cmds` - Vector of untyped AST commands to process
///
/// # Returns
/// A vector of terms representing the assertions with let bindings eliminated
fn tc_let_elim_all(context: &mut Context, cmds: Vec<Command>) -> FrontendResult<Vec<Term>> {
    let mut ret = vec![];
    for cmd in &cmds {
        let cmd = cmd
            .type_check(context)
            .map_err(|e| FrontendError(format!("type error: command '{cmd}', error '{e}'")))?;
        match cmd.repr() {
            // collect assertions to return
            smt_ast::ACommand::Assert(t) => {
                ret.push(t.let_elim(context));
            }
            // ensure logic is correct
            smt_ast::ACommand::SetLogic(hlogic) => {
                let logic = hlogic.get().as_str();
                if !(logic == "QF_LRA" || logic == "QF_LIA" || logic == "QF_LIRA") {
                    return Err(FrontendError(format!("unsupported logic: {}", logic)));
                }
            }
            _ => continue,
        }
    }
    Ok(ret)
}

/// Parse an SMT script into a vector of assertion terms
fn smt_to_terms(smt: &str) -> FrontendResult<Vec<Term>> {
    let cmds = UntypedAst
        .parse_script_str(smt)
        .map_err(|e| e.to_string())?;
    let mut context = Context::new();
    tc_let_elim_all(&mut context, cmds)
}

/// Parse an SMT script and return a list of arithmetic relations
///
/// The SMT script is required to have logic QF_LRA/LIA and be a top-level conjunction of
/// arithmetic literals. Disequality is currently not handled; ideally it should be
/// pre-processed away upstream.
pub fn convert_smt(smt_input: &str) -> FrontendResult<ConvContext> {
    let terms = smt_to_terms(smt_input)?;
    log::debug!("num_parsed_terms={}", terms.len());
    convert_terms(&terms)
}

fn convert_terms(terms: &[Term]) -> FrontendResult<ConvContext> {
    let mut ctx = ConvContext::new();
    for t in terms {
        if let Some(r) = convert_arith_literal(&mut ctx, t)? {
            // Allocate a slack variable associated with the term
            // Note: cloning `t` is cheap; it's a uid + arc ref
            // println!("in convert terms with {}", t);
            let slack_t = ctx.allocate_term(t.clone(), None, None);
            ctx.push_relation(r, slack_t);
        }
    }
    // println!("exiting convert_terms");
    Ok(ctx)
}

/// Parse an SMT script and build a QF_LRA solver without preprocessing
pub fn smt_to_lra_solver(smt_input: &str) -> FrontendResult<LRASolver<TableauDense>> {
    let ctx = convert_smt(smt_input)?;
    Ok(LinearSystem::new(ctx).to_lra_solver(true)?)
}

/// Top-level arithmetic solving function
///
/// This provides solving a system of linear (in)equalities over the rationals as a single function
/// call from SMT-LIB text as input.
pub fn solve_smtlib(smt_input: &str) -> FrontendResult<SolverDecisionApi> {
    let ctx = convert_smt(smt_input)?;
    solve_with_context(ctx)
}

/// Top-level mixed-integer arithmetic solver
///
/// This version accepts a list of arithmetic literals and returns SAT/UNSAT/UNKNOW
/// as usual. SAT comes with a satisfying assignment and UNSAT comes with a conflict
/// set which is guaranteed to be a subset of the input literals.
pub fn solve(arith_literals: &[Term]) -> FrontendResult<SolverDecisionApi> {
    // The context is used to construct a solver below, but also to report conflicts
    // and assignments to the outside in terms of [Term]s rather than internal variables.
    // This value is consumed below, but some of the mappings are cloned for reporting.
    let ctx = convert_terms(arith_literals)?;
    solve_with_context(ctx)
}

fn solve_with_context(mut ctx: ConvContext) -> FrontendResult<SolverDecisionApi> {
    let (_, var_term_map) = ctx.get_term_var_maps(); // this is a clone

    // preprocess the input relations, detect trivial cases, and otherwise return a [LinearSystem]
    // from which to build a solver.
    // println!("before preprocess");
    let result = preprocess(&mut ctx);
    // println!("after preprocess");
    let sys = match result {
        PreprocessResult::TriviallySat => {
            let model = default_model(ctx.get_all_vars());
            return Ok(SolverDecisionApi::from_solver_decision(
                &var_term_map,
                SolverDecision::FEASIBLE(model),
            )?);
        }
        PreprocessResult::TriviallyUnsat(v) => {
            let mut conflict = collections::BTreeSet::new();
            conflict.insert(v);
            return Ok(SolverDecisionApi::from_solver_decision(
                &var_term_map,
                SolverDecision::INFEASIBLE(Conflict::from_set(conflict)),
            )?);
        }
        PreprocessResult::Unknown => LinearSystem::new(ctx),
    };
    // println!("after sys");
    let lra_solver = sys
        .to_lra_solver(true)
        .map_err(|e| FrontendError(format!("error building lra_solver: {}", e)))?;
    // println!("after lar_solver");
    let mut lira_solver = LIRASolver::new(lra_solver);
    // println!("after lira_solver");
    let internal_decision = lira_solver
        .solve()
        .map_err(|e| FrontendError(format!("error solving: {}", e)))?;
    // println!("after internal_decision");
    Ok(SolverDecisionApi::from_solver_decision(
        &var_term_map,
        internal_decision,
    )?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arithmetic::lia::frontend::{convert_smt, smt_to_lra_solver, solve_smtlib};
    use crate::arithmetic::lia::preprocess::{PreprocessResult, preprocess};
    use crate::arithmetic::lia::solver_result::SolverDecision;
    use crate::arithmetic::lia::solver_result_api::SolverDecisionApi;
    use crate::arithmetic::lia::types::{DBig, rbig};
    use crate::arithmetic::lia::variables::Var;
    use std::str::FromStr;

    // A sanity check for `convert_dbig`
    #[test]
    fn fbig_digits() -> Result<(), dashu::base::ParseError> {
        let d = DBig::from_str("1.00234")?; // 100234 * 10^-5
        let expected_r = Rational::ONE + rbig!(234 / 100_000);
        assert_eq!(
            convert_dbig(&d).expect("failed to convert dbig"),
            expected_r
        );
        Ok(())
    }

    #[test]
    fn test_convert_smt_linear_real() {
        // Create a simple SMT-LIB script with linear real arithmetic
        let smt = r#"
            (set-logic QF_LRA)
            (declare-fun x0 () Real)
            (declare-fun x1 () Real)
            (assert (>= (+ x0 (* 2 x1)) 3))
            (assert (<= x1 1))
        "#;

        // Convert SMT script to relations
        let ctx = convert_smt(smt).unwrap();

        // Verify we got 2 relations
        assert_eq!(ctx.num_relations(), 2);

        // First relation: x0 + 2x1 >= 3
        let expected_rel1 = Rel::from_addends_lhs_rhs(
            vec![
                Addend::term(Rational::ONE, Var::real(0)),
                Addend::term(rbig!(2), Var::real(1)),
            ],
            Constraint::Ge,
            vec![Addend::constant(rbig!(3))],
        );

        // Second relation: x1 <= 1
        let expected_rel2 = Rel::from_addends_lhs_rhs(
            vec![Addend::term(Rational::ONE, Var::real(1))],
            Constraint::Le,
            vec![Addend::constant(rbig!(1))],
        );

        // Verify the relations match what we expect
        let rels: Vec<&Rel<Rational>> = ctx.get_relations().map(|(r, _)| r).collect();
        assert!(rels[0].equivalent(&expected_rel1));
        assert!(rels[1].equivalent(&expected_rel2));
    }

    #[test]
    fn test_convert_smt_linear_real_with_negation() {
        // Create a simple SMT-LIB script with linear real arithmetic with a negated literal
        let smt = r#"
            (set-logic QF_LRA)
            (declare-fun x0 () Real)
            (assert (not (<= x0 0)))
        "#;
        let ctx = convert_smt(smt).unwrap();
        assert_eq!(ctx.num_relations(), 1);
        // relation: x0 > 0
        let expected_rel = Rel::from_addends_lhs_rhs(
            vec![Addend::term(Rational::ONE, Var::real(0))],
            Constraint::Gt,
            vec![Addend::constant(rbig!(0))],
        );
        let (rel, _) = ctx.get_relations().next().unwrap();
        assert!(rel.equivalent(&expected_rel));
    }

    #[test]
    fn test_convert_smt_var_types_converted() {
        let smt = r#"
            (set-logic QF_LIA)
            (declare-fun x () Int)
            (declare-fun y () Int)
            (assert (<= x y))
        "#;
        let ctx = convert_smt(smt).unwrap();
        let expected_rel = Rel::from_addends_lhs_rhs(
            vec![
                Addend::term(Rational::ONE, Var::int(0)),
                Addend::term(-Rational::ONE, Var::int(1)),
            ],
            Constraint::Le,
            vec![Addend::constant(rbig!(0))],
        );
        let (rel, _) = ctx.get_relations().next().unwrap();
        assert!(rel.equivalent(&expected_rel));
    }

    #[test]
    fn test_constant_division() {
        let smt = r#"
            (set-logic QF_LIA)
            (declare-fun x () Int)
            (assert (= 1 (div x 2)))  ; 1 = (1/2) x
        "#;
        let ctx = convert_smt(smt).unwrap();
        // normalizes to x = 2
        let expected_rel = Rel::from_addends_lhs_rhs(
            vec![Addend::term(Rational::ONE, Var::int(0))],
            Constraint::Eq,
            vec![Addend::constant(rbig!(2))],
        );
        let (rel, _) = ctx.get_relations().next().unwrap();
        assert!(rel.equivalent(&expected_rel));

        // Test a non-linear division
        let smt = r#"
            (set-logic QF_LIA)
            (declare-fun x () Int)
            (assert (= 1 (div 3 x)))  ; 3/x = 1
        "#;
        assert!(convert_smt(smt).is_err());

        // Test division by a constant polynomial; this goes beyond the extensions
        // to the SMT standard which only allows division by _concrete_ constants
        let smt = r#"
            (set-logic QF_LIA)
            (declare-fun x () Int)
            (declare-fun y () Int)
            (assert (<= 1 (div x (+ 5 (+ y (- y))))))  ; 1 <= x / (5 + y + (-y))
        "#;
        let ctx = convert_smt(smt).unwrap();
        // normalizes to x >= 5
        let expected_rel = Rel::from_addends_lhs_rhs(
            vec![Addend::term(Rational::ONE, Var::int(0))],
            Constraint::Ge,
            vec![Addend::constant(rbig!(5))],
        );
        let (rel, _) = ctx.get_relations().next().unwrap();
        assert!(rel.equivalent(&expected_rel));
    }

    // ---------------------------------------------------------------------
    // ---      Tests ported from LIA frontend integration tests         ---
    // ---------------------------------------------------------------------

    #[test]
    fn test_top_level_solve_smtlib() {
        let _ = env_logger::builder().is_test(true).try_init();
        let smt = r#"
(set-logic QF_LRA)
(declare-fun x0 () Real)
(assert (not (<= x0 0)))
(check-sat)
    "#;
        assert!(matches!(
            solve_smtlib(smt).unwrap(),
            SolverDecisionApi::FEASIBLE(_)
        ));
    }

    /// Test that trivially satisfiable relations are removed during preprocessing
    ///
    /// System:
    ///   x0 + x1 <= 5       (non-trivial relation)
    ///   0 <= 5             (trivially satisfiable relation)
    ///   x0 - x1 >= -2      (non-trivial relation)
    ///   x0 - x0 <= 0       (trivially satisfiable relation)
    ///
    /// The resulting system should only have 2 relations, as the trivially satisfiable
    /// relation "0 <= 5" should be removed during normalization.
    #[test]
    fn test_trivially_sat_relation_removal() {
        let _ = env_logger::builder().is_test(true).try_init();
        let smt_input = r#"
(set-logic QF_LRA)
(declare-fun x0 () Real)
(declare-fun x1 () Real)
(assert (<= (+ x0 x1) 5))
(assert (<= 0 5))
(assert (>= (+ x0 (- x1)) (- 2)))
(assert (<= (+ x0 (- x0)) 0))
(check-sat)
    "#;
        let mut ctx = convert_smt(smt_input).expect("parsing relations failed?");
        if let PreprocessResult::Unknown = preprocess(&mut ctx) {
            assert_eq!(ctx.num_relations(), 2);
        } else {
            unreachable!()
        }

        let result = solve_smtlib(smt_input).expect("solver failed");
        assert!(matches!(result, SolverDecisionApi::FEASIBLE(_)));
    }

    /// Test that trivially satisfiable relations are removed during preprocessing
    ///
    /// System:
    ///   0 <= 5             (trivially satisfiable relation)
    ///   x0 - x0 <= 0       (trivially satisfiable relation)
    ///
    /// The resulting system is trivially satisfiable.
    #[test]
    fn test_trivially_sat() {
        let _ = env_logger::builder().is_test(true).try_init();
        let smt_input = r#"
(set-logic QF_LRA)
(declare-fun x0 () Real)
(declare-fun x1 () Real)
(assert (<= 0 5))
(assert (<= (+ x0 (- x0)) 0))
(check-sat)
    "#;
        let mut ctx = convert_smt(smt_input).expect("parsing relations failed");
        assert!(matches!(
            preprocess(&mut ctx),
            PreprocessResult::TriviallySat
        ));
        let result = solve_smtlib(smt_input).expect("solver failed");
        assert!(matches!(result, SolverDecisionApi::FEASIBLE(_)));
    }

    /// Test that trivially contradictory constraints result in a trivially infeasible
    /// linear system.
    ///
    /// System:
    ///   x0 - x0 > 1        (trivially unsat)
    ///
    /// The resulting system should only have 1 relation: the normalized form of
    /// the second relation.
    #[test]
    fn test_frontend_trivially_unsat_relation_preprocessing() {
        let _ = env_logger::builder().is_test(true).try_init();
        let smt_input = r#"
(set-logic QF_LRA)
(declare-fun x0 () Real)
(assert (> (+ x0 (- x0)) 2))
(check-sat)
    "#;
        let mut ctx = convert_smt(smt_input).expect("parsing relations failed");
        assert!(matches!(
            preprocess(&mut ctx),
            PreprocessResult::TriviallyUnsat(_)
        ));
        let result = solve_smtlib(smt_input).expect("solver failed");
        assert!(matches!(result, SolverDecisionApi::INFEASIBLE(_)));
    }

    #[test]
    fn test_smt_to_lra_solver() {
        // Create an SMT-LIB input string with linear real arithmetic assertions
        //
        // This example is SAT:
        //
        //   x0 + x1      <= 5
        // 2 x0      + x2 >= 2
        //      - x1 + x2 <= 3
        //
        // --> x0 = 1, x1 = 0, x2 = 0
        let smt_input = r#"
(set-logic QF_LRA)
(declare-fun x0 () Real)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(assert (<= (+ x0 x1) 5))
(assert (>= (+ (* 2 x0) x2) 2))
(assert (<= (+ (* (- 1) x1) x2) 3))
(assert (>= x0 0))
(assert (>= x1 0))
(assert (>= x2 0))
(check-sat)
    "#;

        let mut solver = smt_to_lra_solver(smt_input).expect("Failed to create LRA solver");
        let result = solver.solve().expect("Failed to run simplex algorithm");
        assert!(matches!(result, SolverDecision::FEASIBLE(_)));
    }

    #[test]
    fn test_smt_to_lra_solver_infeasible() {
        let smt_input = r#"
(set-logic QF_LRA)
(declare-fun x0 () Real)
(declare-fun x1 () Real)
(assert (<= x0 0))
(assert (<= x1 0))
(assert (>= (+ x0 x1) 1))
(check-sat)
    "#;
        let mut solver = smt_to_lra_solver(smt_input).expect("Failed to create LRA solver");
        let result = solver.solve().expect("Failed to run simplex algorithm");
        assert!(matches!(result, SolverDecision::INFEASIBLE(_)));
    }

    #[test]
    fn test_frontend_boolean_literals() {
        let smt_input = r#"
(set-logic QF_LRA)
(declare-const a Bool)
(declare-const b Bool)
(declare-fun x0 () Real)
(assert (<= x0 0))
(assert (! a :named a-bool-lit))
(assert (not b))
(check-sat)
    "#;
        let mut solver = smt_to_lra_solver(smt_input).expect("Failed to create LRA solver");
        let result = solver.solve().expect("Failed to run simplex algorithm");
        assert!(matches!(result, SolverDecision::FEASIBLE(_)));
    }

    #[test]
    fn test_smt_to_lra_solver_with_div() {
        let smt_input = r#"
(set-logic QF_LRA)
(declare-fun x0 () Real)
(assert (<= (/ x0 2) 0))
(check-sat)
    "#;
        let mut solver = smt_to_lra_solver(smt_input).expect("Failed to create LRA solver");
        let result = solver.solve().expect("Failed to run simplex algorithm");
        assert!(matches!(result, SolverDecision::FEASIBLE(_)));
    }

    #[test]
    fn test_left_assoc_minus() {
        let smt_input = r#"
(set-logic QF_LRA)
(declare-fun x () Real)
(assert (= x (- 1 2 3)))  ; x = (1 - 2) - 3 = -4
(check-sat)
    "#;
        let mut solver = smt_to_lra_solver(smt_input).expect("Failed to create LRA solver");
        let result = solver.solve().expect("Failed to run simplex algorithm");
        match result {
            SolverDecision::FEASIBLE(model) => {
                let x_var = solver.get_var("x").unwrap();
                assert_eq!(model.get(&x_var), Some(&rbig!(-4)));
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn test_uninterpreted_fun() {
        let smt_input = r#"
(declare-fun f (Int) Int)
(declare-fun x () Int)
(assert (= (f x) (+ 1 2)))  ; (f x) = 1 + 2 = 3
(assert (= x (f x)))
(check-sat)
    "#;
        let mut solver = smt_to_lra_solver(smt_input).expect("Failed to create LRA solver");
        let result = solver.solve().expect("Failed to run simplex algorithm");
        match result {
            SolverDecision::FEASIBLE(model) => {
                let x_var = solver.get_var("x").unwrap();
                assert_eq!(model.get(&x_var), Some(&rbig!(3)));
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn test_d0_div_by_zero_bug() {
        let smt_input = r#"
(declare-const i Int)
(declare-const j Int)
; j = 1, i < 0, i < j ==> satisfiable by any i < 0 and j = 1
(assert (= 1 j))
(assert (> 0 i))
(assert (< i j))
(check-sat)
    "#;
        let mut solver = smt_to_lra_solver(smt_input).expect("Failed to create LRA solver");
        let result = solver.solve().expect("Failed to run simplex algorithm");
        assert!(matches!(result, SolverDecision::FEASIBLE(_)));
    }
}
