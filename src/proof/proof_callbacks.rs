// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::debug_println;
use crate::proof::proof_tracer::SMTProofTracer;
use cadical_sys::ProofTracer;

/// An implementation of the cadical-sys `ProofTracer` trait,
/// which uses callback functions to notify the owner of a CaDiCaL
/// instance of important events that occur during SAT solving.
impl ProofTracer for SMTProofTracer {
    fn add_original_clause(
        &mut self,
        _id: u64,
        _redundant: bool,
        _clause: &[i32],
        _restored: bool,
    ) {
        // Previously, this function added original formula clauses and theory clauses to the proof here.
        // However, because this function could only see the clause itself and whether Sundance was
        // still processing original formula clauses, it couldn't determine
        // which theory was responsible for the clause (which eDRAT now requires).
        // Thus, Sundance directly adds original and theory clauses elsewhere.
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

        self.add_sat_clause(&clause.to_vec());
    }

    fn delete_clause(&mut self, _id: u64, _redundant: bool, clause: &[i32]) {
        self.deleted_clauses += 1;
        self.record_deletion(&clause.to_vec());
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
        // Optional: Adding constraints
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
