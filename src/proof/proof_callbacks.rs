// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::debug_println;
use crate::proof::{Theory, proof_tracer::SMTProofTracer};
use cadical_sys::ProofTracer;

/// An implementation of the cadical-sys `ProofTracer` trait,
/// which uses callback functions to notify the owner of a CaDiCaL
/// instance of important events that occur during SAT solving.
impl ProofTracer for SMTProofTracer {
    fn add_original_clause(&mut self, id: u64, _redundant: bool, clause: &[i32], restored: bool) {
        if let Some(registration) = self.consume_clause_registration(clause) {
            self.associate_original_clause(id, registration);
            return;
        }
        if restored {
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

        self.record_derived_clause(id, clause, antecedents);
    }

    fn delete_clause(&mut self, id: u64, _redundant: bool, clause: &[i32]) {
        self.deleted_clauses += 1;
        self.forget_clause_id(id);
        if !clause
            .iter()
            .any(|literal| self.is_activation_literal(*literal))
        {
            self.record_deletion(clause);
        }
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

    #[test]
    fn tracks_transitive_quantifier_dependencies() {
        let mut tracer = tracer();
        let instance = crate::quantifiers::quantifier::QiInstanceId {
            quantifier_id: 11,
            instance_term_id: 22,
        };
        tracer.register_activation_literal(9);
        tracer.register_quantifier_clause(&[1, 2], instance);
        ProofTracer::add_original_clause(&mut tracer, 10, true, &[2, 1], false);
        ProofTracer::add_derived_clause(&mut tracer, 20, true, &[3, 9], &[10]);
        ProofTracer::add_derived_clause(&mut tracer, 30, true, &[], &[20]);

        let record = tracer.qi_derived_after(0).pop().unwrap();
        assert!(record.dependencies.contains(&instance));
        assert!(record.clause.is_empty());
        assert_eq!(tracer.qi_derived_after(0).len(), 2);
        assert!(!tracer.generate_edrat().contains(" 9 "));
    }

    #[test]
    fn delays_qi_proof_until_the_learned_clause_is_selected() {
        let mut tracer = tracer();
        let instance = crate::quantifiers::quantifier::QiInstanceId {
            quantifier_id: 11,
            instance_term_id: 22,
        };
        tracer.register_qi_proof_bundle(instance, Vec::new());
        tracer.register_activation_literal(9);
        tracer.register_quantifier_clause(&[1, 9], instance);
        ProofTracer::add_original_clause(&mut tracer, 10, true, &[1, 9], false);
        ProofTracer::add_derived_clause(&mut tracer, 20, true, &[3, 9], &[10]);

        assert_eq!(tracer.generate_edrat(), "");

        let learned = tracer.qi_derived_after(0).pop().unwrap();
        tracer.emit_qi_derived_clause(&learned);
        assert_eq!(tracer.generate_edrat(), "3 0\n");
    }

    #[test]
    fn omits_activation_only_sat_derivations() {
        let mut tracer = tracer();
        tracer.register_activation_literal(9);
        ProofTracer::add_derived_clause(&mut tracer, 10, true, &[9], &[]);
        assert_eq!(tracer.generate_edrat(), "");
    }

    #[test]
    fn does_not_project_negative_activation_literals() {
        let mut tracer = tracer();
        let instance = crate::quantifiers::quantifier::QiInstanceId {
            quantifier_id: 11,
            instance_term_id: 22,
        };
        tracer.register_activation_literal(9);
        tracer.register_quantifier_clause(&[1, 9], instance);
        ProofTracer::add_original_clause(&mut tracer, 10, true, &[1, 9], false);
        ProofTracer::add_derived_clause(&mut tracer, 20, true, &[-9, 3], &[10]);

        assert!(tracer.qi_derived_after(0).is_empty());

        ProofTracer::add_derived_clause(&mut tracer, 30, true, &[4], &[20]);
        let record = tracer.qi_derived_after(0).pop().unwrap();
        assert_eq!(record.clause, vec![4]);
        assert!(record.dependencies.contains(&instance));
        assert!(!tracer.generate_edrat().contains("-9"));
    }
}
