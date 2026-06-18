// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use yaspar_ir::ast::{FetchSort, HasArena, Monomorphization};

use crate::datatypes::axioms::learn_exactly_one_tester_clause;
use crate::egraphs::traits::EgraphTrait;
use crate::solver_state::SolverState;
use crate::solver_types::ConstructorType;
use crate::solver_types::TermOption;
use crate::utils::DeterministicHashMap;

/// Edge in the constructor graph, recording egraph IDs for conflict clause generation.
#[derive(Debug, Clone)]
struct CtorEdge {
    /// Egraph ID of the datatype term (the parent node in the cycle)
    parent_eid: u32,
    /// Egraph ID of the selector application (the child reaching the next node)
    child_eid: u32,
}

/// Performs the occurs check for inductive datatypes.
///
/// Detects cycles in the constructor-child graph over e-classes. A cycle means
/// a term is a subterm of itself, which violates well-foundedness.
/// Returns a conflict clause if a cycle is found, None otherwise.
pub fn datatype_occurs_check(solver_state: &mut SolverState) -> Option<Vec<i32>> {
    // Build directed graph: canonical parent eid -> [(canonical child eid, edge info)]
    let mut graph: DeterministicHashMap<u32, Vec<(u32, CtorEdge)>> = Default::default();

    for (&uid, ctor_type) in solver_state.term_constructors.iter() {
        let children = match ctor_type {
            ConstructorType::Constructor { children, .. } if !children.is_empty() => children,
            _ => continue,
        };

        let Some(&term_eid) = solver_state.id_map.get_by_left(&uid) else {
            continue;
        };
        let parent_canonical = solver_state.egraph.find(term_eid);

        for &child_uid in children {
            let Some(&child_eid) = solver_state.id_map.get_by_left(&child_uid) else {
                continue;
            };
            let child_canonical = solver_state.egraph.find(child_eid);

            graph.entry(parent_canonical).or_default().push((
                child_canonical,
                CtorEdge {
                    parent_eid: term_eid,
                    child_eid,
                },
            ));
        }
    }

    // DFS cycle detection (three-color: 0=white, 1=gray, 2=black)
    let mut color: DeterministicHashMap<u32, u8> = Default::default();
    let mut parent_map: DeterministicHashMap<u32, (u32, CtorEdge)> = Default::default();

    for &start in graph.keys() {
        if *color.get(&start).unwrap_or(&0) != 0 {
            continue;
        }
        let mut stack: Vec<(u32, usize)> = vec![(start, 0)];
        color.insert(start, 1);

        while let Some((node, idx)) = stack.last_mut() {
            let node = *node;
            let neighbors = graph.get(&node);
            let neighbor_count = neighbors.map_or(0, |n| n.len());

            if *idx >= neighbor_count {
                color.insert(node, 2);
                stack.pop();
                continue;
            }

            let (child, edge) = neighbors.unwrap()[*idx].clone();
            *idx += 1;

            match color.get(&child).unwrap_or(&0) {
                0 => {
                    color.insert(child, 1);
                    parent_map.insert(child, (node, edge));
                    stack.push((child, 0));
                }
                1 => {
                    // Found a cycle — reconstruct path from child -> ... -> node -> child
                    let mut cycle_edges: Vec<CtorEdge> = vec![edge];
                    let mut cur = node;
                    while cur != child {
                        let (prev, prev_edge) = parent_map.get(&cur).unwrap().clone();
                        cycle_edges.push(prev_edge);
                        cur = prev;
                    }
                    return Some(build_conflict_clause(solver_state, &cycle_edges));
                }
                _ => {} // black — already fully explored
            }
        }
    }

    None
}

/// Build a conflict clause from the edges forming a cycle.
///
/// The cycle is edge_0, edge_1, ..., edge_k where each edge_i goes from one
/// e-class to the next. The key equality justifying each step is:
///   edge_i.child_eid ≡ edge_{(i+1) % k}.parent_eid
/// i.e., the selector application of term_i ended up equal to term_{i+1}.
/// The conflict clause negates these equalities.
fn build_conflict_clause(solver_state: &mut SolverState, cycle_edges: &[CtorEdge]) -> Vec<i32> {
    let mut clause: Vec<i32> = Vec::new();
    let n = cycle_edges.len();

    for i in 0..n {
        let this_child = cycle_edges[i].child_eid;
        let next_parent = cycle_edges[(i + 1) % n].parent_eid;

        if this_child == next_parent {
            continue;
        }

        if let Some(equalities) = solver_state
            .egraph
            .explain_equality(this_child, next_parent)
        {
            for (a, b) in equalities {
                clause.push(-solver_state.make_eq(a, b));
            }
        }
    }

    clause
}

/// Generate tester clauses for datatype terms that are still Uninitialized.
/// Called from cb_check_found_model to lazily add case splits (matching Z3's final_check).
pub fn generate_deferred_tester_clauses(solver_state: &mut SolverState) -> Vec<Vec<i32>> {
    let mut all_clauses = vec![];

    // Collect UIDs of uninitialized terms (can't mutate term_constructors while iterating)
    let uninitialized_uids: Vec<u64> = solver_state
        .term_constructors
        .iter()
        .filter_map(|(&uid, ctor_type)| match ctor_type {
            ConstructorType::Uninitialized => Some(uid),
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
        all_clauses.extend(clauses);
    }

    all_clauses
}
