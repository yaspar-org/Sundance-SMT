// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Preprocessing of linear relations; intended as an intermediate step between the
//! SMT parser frontend and the LinearSystem representation.

use crate::arithmetic::lia::context::ConvContext;
use crate::arithmetic::lia::variables::Var;
use std::collections::HashSet;

/// Preprocessing result
///
/// Currently, preprocessing detects trivally Sat relations, trivially Sat/Unsat systems, and
/// otherwise results in a non-trivial suitable for constructing an [crate::arithmetic::lia::lra_solver::LRASolver] instance from.
#[derive(Debug)]
pub enum PreprocessResult {
    /// System has been pre-processed and it's satisfiability is unknown
    Unknown,
    /// Trivially SAT system after preprocessing
    TriviallySat,
    /// Trivially UNSAT system after preprocessing; including the first
    /// conflict variable detected
    TriviallyUnsat(Var),
}

/// Preprocess a context containing a set of linear relations
///
/// 1. normalize input relations
/// 2. filter out trivially sat relations
/// 3. break early if trivial contradictions are found
pub fn preprocess(ctx: &mut ConvContext) -> PreprocessResult {
    let mut to_remove = HashSet::new();
    let mut num_monomials: usize = 0;
    let mut num_trivial: usize = 0;
    for (r, v) in ctx.get_relations_mut() {
        // Preprocess relation
        r.normalize();
        num_monomials += r.terms_ref().len();
        // remove trivially sat relations, e.g. 0 <= 5
        if r.is_trivial_sat() {
            num_trivial += r.terms_ref().len();
            to_remove.insert(*v); // add the associated var to removal set
        } else {
            // immediately return if a trivially unsat relation (e.g. 0 <= -1) is found
            if r.is_trivial_unsat() {
                log::debug!("query is trivially UNSAT");
                return PreprocessResult::TriviallyUnsat(*v);
            }
        }
    }
    log::debug!(
        "num_monomials={}, num_trivial_relations={}",
        num_monomials,
        num_trivial
    );
    // Remove the trivially SAT relations (e.g. 0 <= 1).
    ctx.filter_vars(|v| !to_remove.contains(v));
    if ctx.num_relations() == 0 {
        return PreprocessResult::TriviallySat;
    }
    PreprocessResult::Unknown
}
