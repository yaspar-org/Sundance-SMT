// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Entry point for the LIA mixed integer arithmetic solver
use crate::arithmetic::lia::{frontend, solver_result_api};
use crate::egraphs::egraph::Egraph;
use yaspar_ir::ast::Term;

pub fn check_integer_constraints_satisfiable_lia(
    terms: &[i32],
    // TODO: lialp: check that taking egraph mutable is okay
    egraph: &mut Egraph,
) -> Option<Vec<i32>> {
    let terms: Vec<Term> = terms.iter().map(|l| egraph.get_term_from_lit(*l)).collect();
    //
    // pub fn solve(arith_literals: &[Term]) -> FrontendResult<SolverDecisionApi> {
    //
    match frontend::solve(&terms) {
        Ok(solver_result_api::SolverDecisionApi::FEASIBLE(_)) => None,
        Ok(solver_result_api::SolverDecisionApi::INFEASIBLE(conflict)) => {
            let conflict = conflict
                .iter()
                .map(|t| -egraph.get_lit_from_term(t))
                .collect();
            Some(conflict)
        }
        Err(e) => panic!("lialp: unexpected error: {e:?}"),
    }
}
