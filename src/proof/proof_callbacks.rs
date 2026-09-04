// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::debug_println;
use crate::proof::{Theory, proof_tracer::SMTProofTracer};
use cadical_sys::ProofTracer;

fn note_qi_gc_clause_removed(tracer: &mut SMTProofTracer, id: u64, clause: &[i32]) {
    let Some(ref gc_state) = tracer.qi_gc_state else {
        return;
    };
    let mut gc = gc_state.borrow_mut();
    let matched_id = gc.pending_retired_qi_clause_ids.remove(&id);
    if matched_id {
        gc.total_physically_collected_qi_clause_ids += 1;
    }

    let mut normalized = clause.to_vec();
    normalized.sort_unstable();
    normalized.dedup();
    let matched_content =
        if let Some(count) = gc.pending_retired_qi_clause_contents.get_mut(&normalized) {
            *count -= 1;
            let remove = *count == 0;
            if remove {
                gc.pending_retired_qi_clause_contents.remove(&normalized);
            }
            true
        } else {
            false
        };
    if matched_content {
        gc.total_physically_collected_qi_clause_contents += 1;
    }
    if matched_id || matched_content {
        gc.total_physically_collected_qi_clauses += 1;
    }
    if gc
        .retired_activations
        .iter()
        .any(|act| clause.contains(&-*act))
    {
        gc.total_deleted_retired_activation_clauses += 1;
    }
    if gc.pending_retired_qi_clause_ids.is_empty()
        && gc.pending_retired_qi_clause_contents.is_empty()
        && let Some(started) = gc.in_search_collection_started.take()
    {
        let expected = std::mem::take(&mut gc.in_search_collection_expected_qi_clauses);
        if std::env::var("SUNDANCE_QI_GC_PROFILE").is_ok() {
            eprintln!(
                "[qi-gc-profile] sat-collect-in-search duration={:.6}s \
                 reclaimed_retired_qi={} total_physically_collected_qi={}",
                started.elapsed().as_secs_f64(),
                expected,
                gc.total_physically_collected_qi_clauses,
            );
        }
    }
    let released_epoch_term_owner = gc.tracker.note_deleted_clause(id);
    if gc.pending_requested_theory_clause_ids.remove(&id) {
        gc.total_physically_collected_theory_clauses += 1;
        if std::env::var("SUNDANCE_QI_GC_PROFILE").is_ok() {
            eprintln!(
                "[qi-gc-profile] theory-clause-collected id={} \
                 pending_theory={} total_collected_theory={}",
                id,
                gc.pending_requested_theory_clause_ids.len(),
                gc.total_physically_collected_theory_clauses,
            );
        }
    }
    if released_epoch_term_owner {
        gc.targeted_term_gc_pending = true;
    }
}

/// An implementation of the cadical-sys `ProofTracer` trait,
/// which uses callback functions to notify the owner of a CaDiCaL
/// instance of important events that occur during SAT solving.
impl ProofTracer for SMTProofTracer {
    fn add_original_clause(&mut self, id: u64, _redundant: bool, clause: &[i32], restored: bool) {
        let registered = self.consume_clause_callback_registration(clause);
        if let Some(ref gc_state) = self.qi_gc_state {
            let mut gc = gc_state.borrow_mut();
            let activation = gc.current_act;
            gc.tracker.note_permanent_clause_added(id, clause);
            if gc.tracker.note_gated_qi_clause(id, clause, activation) {
                return;
            }
        }
        if restored || registered {
            return;
        }

        // Known external-clause producers register callbacks at their source.
        // Preserve Background only as a fallback for untracked provenance.
        self.add_theory_clause(clause, Theory::Background);
    }

    fn add_derived_clause(
        &mut self,
        id: u64,
        _redundant: bool,
        clause: &[i32],
        antecedents: &[u64],
    ) {
        debug_println!(6, 0, "*** SAT SOLVER CONFLICT CLAUSE LEARNED ***");
        debug_println!(6, 0, "Clause ID: {}", id);
        debug_println!(6, 0, "Conflict clause: {:?}", clause);
        debug_println!(6, 0, "Antecedent clause IDs: {:?}", antecedents);
        debug_println!(6, 0, "Clause size: {}", clause.len());

        self.add_sat_clause(clause);

        // Track exactly the current epoch's tainted derived clauses. Since no
        // clause contains +act, resolution cannot remove -act, so this test is
        // equivalent to "depends on a guarded QI clause."
        if let Some(ref gc_state) = self.qi_gc_state {
            let mut gc = gc_state.borrow_mut();
            let activation = gc.current_act;
            let tainted = gc
                .tracker
                .note_derived_clause(id, clause, antecedents, activation);
            if std::env::var("SUNDANCE_QI_GC_TRACE").is_ok() {
                let neg_act = -gc.current_act;
                if tainted {
                    let terms: Vec<String> = clause
                        .iter()
                        .map(|&lit| {
                            if lit == neg_act {
                                format!("¬act({})", neg_act)
                            } else if let Some(desc) = self.lit_to_string(lit) {
                                format!("{}={}", lit, desc)
                            } else {
                                format!("{}", lit)
                            }
                        })
                        .collect();
                    eprintln!(
                        "[qi-gc] conflict clause (id={}): {:?} antecedents={:?}",
                        id, terms, antecedents
                    );
                }
            }
        }
    }

    fn delete_clause(&mut self, id: u64, _redundant: bool, clause: &[i32]) {
        self.deleted_clauses += 1;
        note_qi_gc_clause_removed(self, id, clause);
        self.record_deletion(clause);
    }

    fn weaken_minus(&mut self, _id: u64, _clause: &[i32]) {
        // Optional: track weakened clauses
        panic!("Do not currently support weaken minus")
    }

    fn strengthen(&mut self, _id: u64) {
        // Optional: track strengthened clauses
        // panic!("Do not currently support strengthen")
        // we are allowing this for right now: just clause vivification: https://www.cril.univ-artois.fr/~piette/revival/revival.pdf
        // needed for example by tests/regression/smt_files/skolemization/skolem-negatedforall8.smt2
    }

    fn finalize_clause(&mut self, _id: u64, _clause: &[i32]) {
        // Optional: track finalized clauses
        panic!("Do not currently support finalize clause")
    }

    fn add_assumption(&mut self, _lit: i32) {
        // Optional: SMTleveladding assumptions
        panic!("Do not currently support assumptions")
    }

    fn add_constraint(&mut self, _clause: &[i32]) {
        // This callback reports temporary clauses supplied through CaDiCaL's
        // `constrain` API, not clauses derived by CaDiCaL or a Sundance theory.
        // Sundance does not use that API and cannot soundly tag such a clause.
        panic!("CaDiCaL constraints are not supported in eDRAT proofs");
    }

    fn reset_assumptions(&mut self) {
        // We are still not supporting assumptions, but unlike in add_assumption_clause we do not
        // panic here. CaDiCaL rel 2.1.3 hits this in Solver::call_external_solve_and_check_results
        // https://github.com/arminbiere/cadical/blob/rel-2.1.3/src/solver.cpp#L758-L759
        // Specifically this happens when we get unknown, for example when we run with a timeout.
    }

    fn add_assumption_clause(&mut self, _id: u64, _clause: &[i32], _antecedents: &[u64]) {
        panic!("Do not currently support assumptions")
    }

    fn conclude_sat(&mut self, _conclusion_type: i32, _model: &[i32]) {}

    fn conclude_unsat(&mut self, _conclusion_type: i32, _clause_ids: &[u64]) {}

    fn conclude_unknown(&mut self, _trail: &[i32]) {}
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    fn tracer() -> SMTProofTracer {
        SMTProofTracer::new(HashMap::new(), HashMap::new())
    }

    #[test]
    fn classifies_original_clause_callbacks() {
        let mut startup = tracer();
        startup.add_original_clause(&[]);
        startup.register_clause_for_cadical_callback(&[]);
        ProofTracer::add_original_clause(&mut startup, 1, false, &[], false);
        assert_eq!(startup.generate_edrat(), "a 0\n");

        let mut external = tracer();
        ProofTracer::add_original_clause(&mut external, 1, false, &[], false);
        assert_eq!(external.generate_edrat(), "t bg 0\n");
    }

    #[test]
    #[should_panic(expected = "CaDiCaL constraints are not supported in eDRAT proofs")]
    fn rejects_cadical_constraints() {
        ProofTracer::add_constraint(&mut tracer(), &[]);
    }

    #[test]
    fn registered_clause_callbacks_ignore_order_and_count_duplicates() {
        let mut tracer = tracer();
        tracer.register_clause_for_cadical_callback(&[2, -1]);
        assert!(tracer.consume_clause_callback_registration(&[-1, 2]));
        assert!(!tracer.consume_clause_callback_registration(&[2, -1]));

        tracer.register_clause_for_cadical_callback(&[]);
        tracer.register_clause_for_cadical_callback(&[]);
        ProofTracer::add_original_clause(&mut tracer, 1, false, &[], false);
        ProofTracer::add_original_clause(&mut tracer, 2, false, &[], false);
        assert_eq!(tracer.generate_edrat(), "");

        ProofTracer::add_original_clause(&mut tracer, 3, false, &[], false);
        assert_eq!(tracer.generate_edrat(), "t bg 0\n");
    }

    #[test]
    fn restored_callbacks_consume_matching_registrations() {
        let mut tracer = tracer();
        tracer.register_clause_for_cadical_callback(&[1]);
        ProofTracer::add_original_clause(&mut tracer, 1, false, &[1], true);

        assert!(!tracer.consume_clause_callback_registration(&[1]));
        assert_eq!(tracer.generate_edrat(), "");
    }
}
