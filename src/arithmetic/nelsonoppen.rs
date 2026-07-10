// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::solver_state::SolverState;
use yaspar_ir::ast::{
    ObjectAllocatorExt as _, StrAllocator, Term, TermAllocator, alg::QualifiedIdentifier,
};

/// Build the three sub-terms (lt, gt, eq) for the trichotomy on (x, y).
/// Returns None if the trichotomy has already been emitted for this pair.
/// Marks the pair as emitted on the first successful call.
pub fn nelson_oppen_trichotomy_terms(
    x: u64,
    y: u64,
    solver_state: &mut SolverState,
) -> Option<(Term, Term, Term)> {
    if solver_state.nelson_oppen_ineq_literals.contains(&(x, y)) {
        return None;
    }
    solver_state.nelson_oppen_ineq_literals.insert((x, y));

    let bool_sort = solver_state.context.bool_sort();

    let lt = QualifiedIdentifier::simple(solver_state.context.allocate_symbol("<"));
    let lt_term = solver_state.context.app(
        lt,
        vec![solver_state.get_term(x), solver_state.get_term(y)],
        Some(bool_sort.clone()),
    );

    let gt = QualifiedIdentifier::simple(solver_state.context.allocate_symbol(">"));
    let gt_term = solver_state.context.app(
        gt,
        vec![solver_state.get_term(x), solver_state.get_term(y)],
        Some(bool_sort),
    );

    let eq_term = solver_state
        .context
        .eq(solver_state.get_term(x), solver_state.get_term(y));

    Some((lt_term, gt_term, eq_term))
}
