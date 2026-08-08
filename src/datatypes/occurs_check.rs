// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashSet;
use yaspar_ir::ast::{FetchSort, HasArena, Monomorphization};

use crate::datatypes::axioms::learn_exactly_one_tester_clause;
use crate::egraphs::traits::EgraphTrait;
use crate::solver_state::SolverState;
use crate::solver_types::ConstructorType;
use crate::solver_types::TermOption;
use crate::utils::DeterministicHashMap;

/// An edge in the constructor graph: (parent_eid, child_eid, parent_tester_lit).
/// parent_eid is the egraph ID of the constructor term,
/// child_eid is the egraph ID of its recursive child (selector application),
/// parent_tester_lit is the SAT literal for `(_ is Ctor) parent` — the reason
/// the parent is treated as this constructor. The cycle only exists while every
/// node on it is committed to its constructor, so the conflict clause must be
/// guarded by the negation of each parent's tester. `None` when no tester
/// literal has been allocated yet (the constructor status is not yet a SAT
/// decision), in which case there is nothing to guard against.
type Edge = (u32, u32, Option<i32>);

/// Performs the occurs check for inductive datatypes.
///
/// Detects cycles in the constructor-child graph over e-classes. A cycle means
/// a term is a subterm of itself, which violates well-foundedness.
/// Returns a conflict clause if a cycle is found, None otherwise.
pub fn datatype_occurs_check(solver_state: &mut SolverState) -> Option<Vec<i32>> {
    // Build directed graph: canonical parent eid -> [(canonical child eid, edge)]
    let mut graph: DeterministicHashMap<u32, Vec<(u32, Edge)>> = Default::default();

    for (&uid, ctor_type) in solver_state.term_constructors.iter() {
        let (children, tester_term) = match ctor_type {
            ConstructorType::Constructor {
                children,
                tester_term,
                hash,
                level,
                ..
            } if !children.is_empty() && solver_state.is_valid_hash(*hash, *level) => {
                (children, tester_term)
            }
            _ => continue,
        };

        // The reason this term is treated as this constructor is its tester
        // literal. The occurs-check cycle only holds while that tester is true,
        // so the conflict clause must be guarded by its negation.
        let tester_lit = solver_state.get_lit_from_term_safe(tester_term);

        let Some(&term_eid) = solver_state.id_map.get_by_left(&uid) else {
            continue;
        };
        let parent_canonical = solver_state.egraph.find(term_eid);

        for &child_uid in children {
            let Some(&child_eid) = solver_state.id_map.get_by_left(&child_uid) else {
                continue;
            };
            let child_canonical = solver_state.egraph.find(child_eid);
            graph
                .entry(parent_canonical)
                .or_default()
                .push((child_canonical, (term_eid, child_eid, tester_lit)));
        }
    }

    // DFS with path tracking — when we find a back-edge, the path IS the cycle.
    let mut visited: HashSet<u32> = Default::default();

    for &start in graph.keys() {
        if visited.contains(&start) {
            continue;
        }

        let mut on_path: HashSet<u32> = HashSet::from([start]);
        // path[i] = (canonical_node, edge that brought us here)
        // The first entry has a dummy edge since nothing "brought us" to start.
        let mut path: Vec<(u32, Edge)> = vec![(start, (0, 0, None))];
        let mut stack: Vec<(u32, usize)> = vec![(start, 0)];

        while let Some((node, idx)) = stack.last_mut() {
            let node = *node;
            let neighbors = graph.get(&node);
            let neighbor_count = neighbors.map_or(0, |n| n.len());

            if *idx >= neighbor_count {
                on_path.remove(&node);
                visited.insert(node);
                path.pop();
                stack.pop();
                continue;
            }

            let &(child_canonical, edge) = &neighbors.unwrap()[*idx];
            *idx += 1;

            if on_path.contains(&child_canonical) {
                // Found a cycle. Extract the cycle edges from the path.
                let cycle_start = path
                    .iter()
                    .position(|(n, _)| *n == child_canonical)
                    .unwrap();
                // Edges forming the cycle: from path[cycle_start+1..] (edges into each node)
                // plus the closing back-edge we just found.
                let mut cycle_edges: Vec<Edge> =
                    path[cycle_start + 1..].iter().map(|(_, e)| *e).collect();
                cycle_edges.push(edge);
                let conflict_clause = build_conflict_clause(solver_state, &cycle_edges);
                let clause_terms: Vec<String> = conflict_clause
                    .iter()
                    .map(|&lit| format!("{}", solver_state.get_term_from_lit(lit)))
                    .collect();
                crate::debug_println!(
                    25,
                    10,
                    "OCCURS CHECK AXIOM (conflict clause): (or {})",
                    clause_terms.join(" ")
                );
                return Some(conflict_clause);
            }

            if !visited.contains(&child_canonical) {
                on_path.insert(child_canonical);
                path.push((child_canonical, edge));
                stack.push((child_canonical, 0));
            }
        }
    }

    None
}

/// Build a conflict clause from the edges forming a cycle.
///
/// Each edge (parent_eid, child_eid, parent_tester_lit) represents a
/// constructor-to-child step. Consecutive edges are linked: edge_i.child_eid
/// and edge_{i+1}.parent_eid are in the same e-class.
///
/// The cycle is a contradiction only under the assignment that produced it:
/// each parent must be committed to its constructor (its tester holds) and the
/// linking equalities must hold. The conflict clause is therefore the negation
/// of that conjunction — the negated tester of every parent on the cycle plus
/// the negated linking equalities. Omitting the testers would wrongly assert
/// the equalities can never hold, even when the parents are other constructors.
fn build_conflict_clause(solver_state: &mut SolverState, cycle_edges: &[Edge]) -> Vec<i32> {
    let mut clause: Vec<i32> = Vec::new();
    let n = cycle_edges.len();

    for i in 0..n {
        // Guard: the parent is only this constructor while its tester is true.
        if let Some(tester_lit) = cycle_edges[i].2 {
            clause.push(-tester_lit);
        }

        let this_child = cycle_edges[i].1;
        let next_parent = cycle_edges[(i + 1) % n].0;

        if let Some(equalities) = solver_state
            .egraph
            .explain_equality(this_child, next_parent)
        {
            for (a, b) in equalities {
                clause.push(-solver_state.make_eq(a, b));
            }
        }
    }

    // The same tester or equality literal can appear on multiple edges; keep the
    // clause a proper set of literals.
    clause.sort_unstable();
    clause.dedup();

    clause
}

/// Generate tester clauses for datatype terms that are still Uninitialized.
/// Called from cb_check_found_model to lazily add case splits (matching Z3's final_check).
pub fn generate_deferred_tester_clauses(solver_state: &mut SolverState) -> Vec<Vec<i32>> {
    let mut all_clauses = vec![];

    let uninitialized_uids: Vec<u64> = solver_state
        .term_constructors
        .iter()
        .filter_map(|(&uid, ctor_type)| match ctor_type {
            ConstructorType::Uninitialized => Some(uid),
            ConstructorType::Constructor { hash, level, .. }
                if !solver_state.is_valid_hash(*hash, *level) =>
            {
                Some(uid)
            }
            _ => None,
        })
        .collect();

    for uid in uninitialized_uids {
        let term = match &solver_state.terms_list[uid as usize] {
            TermOption::Some(t) => t.clone(),
            _ => continue,
        };

        let sort = term.get_sort(solver_state.context.arena());
        let dt_dec = match solver_state
            .datatype_info
            .datatypes
            .get(sort.sort_name())
            .cloned()
        {
            Some(dt) => dt,
            None => continue,
        };
        let dt_dec = match dt_dec.monomorphize(&sort, solver_state.context.arena()) {
            Ok(dt) => dt,
            Err(_) => continue,
        };

        let clauses = learn_exactly_one_tester_clause(solver_state, &term, &dt_dec, false);
        if !clauses.is_empty() {
            solver_state.stat_dt_splits += 1;
        }
        all_clauses.extend(clauses);
    }

    all_clauses
}
