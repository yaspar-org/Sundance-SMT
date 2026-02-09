// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Solver results at the user API level

use std::collections;

use crate::arithmetic::lia::solver_result::SolverError;
use crate::arithmetic::lia::solver_result::{Assignment, Conflict, SolverDecision, SolverResult};
use crate::arithmetic::lia::variables::Var;

use yaspar_ir::ast::Term;

/// API level decision of the general simplex algorithm
///
/// This reports conflicts in terms of [Term]s, rather than internal [Var]s
#[derive(Debug, PartialEq, Eq)]
pub enum SolverDecisionApi {
    /// The original linear real arithmetic problem is sat
    /// TODO: make model construction lazy
    FEASIBLE(Assignment<Term>),
    /// The original linear real arithmetic problem is UNSAT
    INFEASIBLE(Conflict<Term>),
}

impl SolverDecisionApi {
    /// Construct an API level solver decision from an internal one
    pub fn from_solver_decision(
        var_term_map: &collections::HashMap<Var, Term>,
        decision: SolverDecision,
    ) -> SolverResult<Self> {
        match decision {
            SolverDecision::FEASIBLE(assg) => {
                log::debug!("from_solver_decision: assg {:?}", assg);
                log::debug!("from_solver_decision: term map {:?}", var_term_map);
                // let term_assign = BTreeMap::new();
                let term_assign = assg
                    .into_iter()
                    .map(|(var, value)| (var_term_map.get(&var).unwrap().clone(), value))
                    .collect();
                Ok(SolverDecisionApi::FEASIBLE(Assignment::new(term_assign)))
            }
            SolverDecision::INFEASIBLE(conflict) => {
                let term_conflict: Conflict<Term> = conflict
                    .iter()
                    .map(|v| var_term_map.get(v).unwrap().clone())
                    .collect();
                Ok(SolverDecisionApi::INFEASIBLE(term_conflict))
            }
            // TODO: from_solver_decision: this won't happen until timeout or other cancelation
            //   mechanisms are in place
            SolverDecision::UNKNOWN => Err(SolverError(
                "arithmetic solver returned UNKNOWN".to_string(),
            )),
        }
    }
}
