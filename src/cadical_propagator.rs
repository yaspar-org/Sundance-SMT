// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::arithmetic::lp::{ArithResult, ArithSolver, check_integer_constraints_satisfiable};
use crate::debug_println;
use crate::egraphs::EgraphTrait;
use crate::log::is_important;
use crate::proof::{SMTProofTracer, Theory};
use crate::quantifiers::quantifier::QuantifierInstance::{Instantiation, Skolemization};
use crate::quantifiers::quantifier::instantiate_quantifiers;
use crate::solver_state::{SolverState, process_assignment};
use crate::stats::SolverStats;
use crate::utils::DeterministicHashSet;
use cadical_sys::{CaDiCal, ExternalPropagator};
use std::cell::RefCell;
use std::rc::Rc;

/// Our implementation of a Cadical Propagator
pub struct CustomExternalPropagator<'a> {
    pub decision_level: usize,
    pub solver_state: &'a mut SolverState,
    pub disequalities: RefCell<Vec<Vec<i32>>>, // might be paying a bit of overhead for RefCell
    pub fixed_literals: DeterministicHashSet<i32>,
    pub proof_tracer: Rc<RefCell<SMTProofTracer>>,
    pub assignments: Vec<i32>, // maps abs(literal) -> (decision level assigned + 1) * sgn(literal)
    pub solver: *mut CaDiCal,
    pub arithmetic: ArithSolver, // whether we are doing arithmetic solving or not
    pub stats: SolverStats,
}

impl<'a> CustomExternalPropagator<'a> {
    pub fn add_lit_to_proof_tracer(&mut self, lit: i32) {
        let lit = lit.abs(); // only add the positive version
        if self.proof_tracer.borrow().is_lit_registered(lit) {
            debug_println!(
                19,
                0,
                "We have already added literal {lit} to the proof tracker"
            );
            return;
        }
        debug_println!(
            19,
            0,
            "Adding literal {lit} i.e. {} to proof tracker with uid {}",
            self.solver_state.get_term_from_lit(lit),
            self.solver_state.get_term_from_lit(lit).uid()
        );

        if let Some(id) = self.solver_state.cnf_cache.var_map_reverse.get(&lit) {
            let term = self.solver_state.get_term(*id);
            self.proof_tracer
                .borrow_mut()
                .register_term(lit, &term, true);
        } else if let Some(id) = self.solver_state.cnf_cache.var_map_reverse.get(&-lit) {
            let term = self.solver_state.get_term(*id);
            self.proof_tracer
                .borrow_mut()
                .register_term(-lit, &term, false);
        } else {
            panic!("Literal {lit} does not occur positively or negatively in the terms list");
        }
    }

    /// Add a literal as an observed variable to the solver
    fn add_observed_variable(&mut self, lit: i32) {
        let abs_lit = lit.abs();
        debug_println!(
            7,
            0,
            "Adding literal {} as observed variable to solver",
            abs_lit
        );
        unsafe {
            (*self.solver).add_observed_var(abs_lit);
        }
    }

}

impl<'a> ExternalPropagator for CustomExternalPropagator<'a> {
    fn notify_assignment(&mut self, lits: &[i32]) {
        debug_println!(
            22,
            0,
            "PROPAGATOR: Processing assignments (level {}): {:?}",
            self.decision_level,
            lits
        );
        debug_println!(16, 0, "{}", self.solver_state.egraph);
        for lit in lits {
            debug_println!(
                7,
                0,
                "Assigning the literal {:?} (level {}) which is {}",
                lit,
                self.decision_level,
                self.solver_state.get_term_from_lit(*lit)
            );

            // adding the literal to the assignment
            // add with level (negatively if we learn its negation)
            while self.assignments.len() <= lit.unsigned_abs() as usize {
                self.assignments.resize(2 * self.assignments.len(), 0);
            }
            let lit_sign = if *lit > 0 { 1 } else { -1 };
            self.assignments[lit.unsigned_abs() as usize] =
                ((self.decision_level + 1) as i32) * lit_sign;

            if self.fixed_literals.contains(lit) {
                debug_println!(6, 0, "Skipping literal {lit} because it is fixed");
                continue;
            }

            self.add_lit_to_proof_tracer(*lit);

            let negated_model_or_datatype_constraints_opt =
                process_assignment(*lit, self.solver_state, self.decision_level);

            if let Some(conflict_result) = negated_model_or_datatype_constraints_opt {
                for constraint in conflict_result.clauses {

                // todo: deleting this ordering thing -> just for debugging
                let mut constraint_ordered = constraint.clone();
                constraint_ordered.sort();
                debug_println!(
                    16,
                    0,
                    "[in notify_assignment] We have the following constraint: {:?}",
                    constraint_ordered
                );
                if is_important(12) {
                    for lit in constraint.clone() {
                        debug_println!(12, 4, "{}", self.solver_state.get_term_from_lit(lit));
                    }
                }
                let mut shrunk_constraint = vec![];
                let mut already_considered = DeterministicHashSet::default();
                for lit in constraint {
                    if already_considered.contains(&lit) {
                        debug_println!(
                            2,
                            0,
                            "Skipping literal {lit} from negated model because it is repeated"
                        );
                    } else {
                        shrunk_constraint.push(lit);
                        already_considered.insert(lit);
                    }
                }
                // todo: deleting this ordering thing -> just for debugging
                let mut shrunk_constraint_ordered = shrunk_constraint.clone();
                shrunk_constraint_ordered.sort();
                debug_println!(
                    16,
                    1,
                    "After shrinking [ in notify_assignment]: {:?}",
                    shrunk_constraint_ordered
                );
                debug_println!(11, 1, "This corresponds to ");
                for lit in shrunk_constraint.iter() {
                    self.add_lit_to_proof_tracer(*lit);
                    self.add_observed_variable(*lit);
                    debug_println!(11, 1, "  {}", self.solver_state.get_term_from_lit(*lit));
                }

                debug_println!(
                    14 - 3,
                    0,
                    "In case 1 currently disequalities: {:?}",
                    self.disequalities.borrow()
                );

                self.proof_tracer
                    .borrow_mut()
                    .add_theory_clause(&shrunk_constraint, Theory::Background);

                self.disequalities.borrow_mut().push(shrunk_constraint);
                debug_println!(
                    14 - 3,
                    0,
                    "We have the following disequalities: {:?}",
                    self.disequalities.borrow()
                );
                } // end for constraint in conflict_result.clauses
            }
        }
    }

    fn notify_new_decision_level(&mut self) {
        self.stats.decisions += 1;
        debug_println!(
            11,
            0,
            "PROPAGATOR: New decision level {} -> {}",
            self.decision_level,
            self.decision_level + 1
        );
        self.decision_level += 1;
        // Record solver hash at new level
        while self.decision_level >= self.solver_state.hash_at_level.len() {
            self.solver_state
                .hash_at_level
                .resize(self.solver_state.hash_at_level.len() * 2, 0);
        }
        self.solver_state.hash_at_level[self.decision_level] = self.solver_state.current_hash;
    }

    fn notify_backtrack(&mut self, level: usize) {
        self.stats.backtracks += 1;
        debug_println!(
            23,
            0,
            "PROPAGATOR: Backtracking from level {} to level {}",
            self.decision_level,
            level
        );

        // Reset solver-level assignments
        for i in 1..self.assignments.len() {
            if self.assignments[i].abs() > (level + 1) as i32 {
                self.assignments[i] = 0;
            }
        }

        // Bump solver hash on backtrack and invalidate higher levels
        self.solver_state.current_hash += 1;
        for i in level + 1..self.decision_level + 1 {
            if i < self.solver_state.hash_at_level.len() {
                self.solver_state.hash_at_level[i] = self.solver_state.current_hash;
            }
        }

        self.decision_level = level;

        // Delegate to egraph for all egraph-internal backtracking
        self.solver_state.egraph.backtrack_to(level);

        debug_println!(16, 0, "Ending backtracking at level {}", level);
        debug_println!(11, 0, "{}", self.solver_state.egraph);
    }

    fn cb_check_found_model(&mut self, model: &[i32]) -> bool {
        debug_println!(
            24,
            0,
            "PROPAGATOR: Checking model: {:?} [{:?}]",
            model,
            model
                .iter()
                .map(|x| self.solver_state.get_term_from_lit(*x))
                .collect::<Vec<_>>(),
        );

        // for lit in model{
        //      debug_println!(11, 4, "{}", self.solver_state.get_term_from_lit(*lit))
        // }

        if !self.disequalities.borrow_mut().is_empty() {
            debug_println!(
                24,
                0,
                "Trying to check model when the disequalities are not empty"
            );
            return false;
        }

        for term in model {
            let (u64_val, polarity) = self.solver_state.get_u64_from_lit_with_polarity(*term);
            debug_println!(
                24,
                4,
                "{} [lit: {}] [u64: {} with polarity {}]",
                self.solver_state.get_term_from_lit(*term),
                term,
                u64_val,
                polarity
            );
        }
        debug_println!(24, 0, "{}", self.solver_state.egraph);

        // Check arithmetic consistency before instantiating quantifiers
        debug_println!(21, 0, "Starting arithmetic check",);
        self.stats.arith_checks += 1;

        match check_integer_constraints_satisfiable(&self.arithmetic, model, self.solver_state) {
            ArithResult::Unsat(arithmetic_literals, arith_stats) => {
                self.stats.arith.accumulate(&arith_stats);
                {
                    debug_println!(
                        21,
                        0,
                        "PROPAGATOR: Arithmetic inconsistency detected: {:?}",
                        arithmetic_literals
                    );
                    // let negated_arithmetic_literals = arithmetic_literals.iter().map(|x| -x).collect();
                    // todo: add proof logging
                    self.disequalities.borrow_mut().push(arithmetic_literals);
                    return false;
                }
            }
            ArithResult::Sat(literals, arith_stats) => {
                self.stats.arith.accumulate(&arith_stats);
                eprintln!("[NO] ArithResult::Sat at level {}. Groups: {}", self.decision_level, literals.len());
                for (val, set) in &literals {
                    eprintln!("[NO]   model_val={}: {:?}", val, set);
                }
                // Model-based Nelson-Oppen: merge equal-model-value pairs in the
                // egraph via Arithmetic edges instead of eagerly emitting trichotomies.
                let mut conflict_from_arith = None;
                'outer: for set in literals.values() {
                    let mut t = set.iter();
                    let first = t.next().unwrap();

                    for term in t {
                        let (x, y) = if first < term {
                            (*first, *term)
                        } else {
                            (*term, *first)
                        };

                        let x_e = self.solver_state.to_egraph_id(x);
                        let y_e = self.solver_state.to_egraph_id(y);
                        if self.solver_state.egraph.find(x_e)
                            == self.solver_state.egraph.find(y_e)
                        {
                            eprintln!("[NO]   skip ({},{}) already equal", x_e, y_e);
                            continue;
                        }

                        eprintln!("[NO]   merging egraph ({},{}) at level {}", x_e, y_e, self.decision_level);
                        let result = self
                            .solver_state
                            .egraph
                            .assert_equal_arithmetic(x_e, y_e, self.decision_level);
                        if result.conflict.is_some() {
                            eprintln!("[NO]   CONFLICT from merge!");
                            conflict_from_arith = result.conflict;
                            break 'outer;
                        }
                    }
                }

                if let Some(conflict) = conflict_from_arith {
                    eprintln!("[NO]   conflict equalities: {:?}", conflict.equalities);
                    eprintln!("[NO]   conflict arith_eq: {:?}", conflict.arithmetic_equalities);
                    eprintln!("[NO]   conflict diseq: {:?}", conflict.disequality);
                    let cr = crate::solver_state::build_conflict_with_trichotomies(
                        self.solver_state,
                        &conflict.equalities,
                        conflict.arithmetic_equalities,
                        conflict.diseq_lit,
                    );
                    for clause in cr.clauses {
                        for lit in &clause {
                            self.add_observed_variable(*lit);
                            self.add_lit_to_proof_tracer(*lit);
                        }
                        self.disequalities.borrow_mut().push(clause);
                    }
                } else {
                    eprintln!("[NO]   no conflict from merges");
                }
            }
            ArithResult::None => {}
        }

        if !self.disequalities.borrow().is_empty() {
            return false;
        }

        // Occurs check for recursive datatypes (well-foundedness)
        if self.solver_state.datatype_info.has_recursive_datatype() {
            if let Some(conflict_clause) =
                crate::datatypes::occurs_check::datatype_occurs_check(self.solver_state)
            {
                self.disequalities.borrow_mut().push(conflict_clause);
                return false;
            }

            // Lazy case split: add tester clauses for uninitialized datatype terms
            let new_clauses =
                crate::datatypes::occurs_check::generate_deferred_tester_clauses(self.solver_state);
            if !new_clauses.is_empty() {
                for clause in &new_clauses {
                    for lit in clause {
                        self.add_observed_variable(*lit);
                        self.add_lit_to_proof_tracer(*lit);
                    }
                }
                self.disequalities.borrow_mut().extend(new_clauses);
                return false;
            }
        }

        debug_println!(11, 0, "Starting quantifier instantiations");
        let quantifier_instantiations =
            instantiate_quantifiers(self.solver_state, &self.proof_tracer, &self.assignments);
        debug_println!(
            11,
            0,
            "Found quantifier instantiations {:?}",
            quantifier_instantiations
        );

        if quantifier_instantiations.is_empty() {
            debug_println!(10, 0, "{}", self.solver_state.egraph);
            assert!(self.disequalities.borrow().is_empty());

            return true;
        }

        // Add each quantifier instantiation as an instantiation clause to the proof tracker
        // adds clauses of the formal (or (not (forall ....)) (INSTANTIATED PART)) same as (forall ...) => INSTANTIATED PART
        for instantiation in &quantifier_instantiations {
            match instantiation {
                Instantiation { clause, .. } => {
                    // , skolemized
                    for lit in clause {
                        self.add_observed_variable(*lit);
                        self.add_lit_to_proof_tracer(*lit);
                    }

                    // TODO: since I am adding literals, I might have to add them as observed literals
                    self.disequalities.borrow_mut().push(clause.clone());
                    self.stats.instantiations += 1;
                }
                Skolemization { clause } => {
                    for lit in clause {
                        self.add_observed_variable(*lit);
                        self.add_lit_to_proof_tracer(*lit);
                    }

                    self.disequalities.borrow_mut().push(clause.clone());
                }
            }
        }

        debug_println!(4, 0, "Returning false in cb_check_found_model");
        false
    }

    fn cb_decide(&mut self) -> i32 {
        debug_println!(7, 0, "PROPAGATOR: Decision callback invoked");

        // For recursive datatypes, prefer base-case constructors to avoid infinite expansion
        if self.solver_state.datatype_info.has_recursive_datatype() {
            for &lit in &self.solver_state.base_case_tester_lits {
                let idx = lit.unsigned_abs() as usize;
                while idx >= self.assignments.len() {
                    self.assignments.resize(self.assignments.len() * 2, 0);
                }
                if self.assignments[idx] == 0 {
                    return lit;
                }
            }
        }

        0
    }

    fn cb_propagate(&mut self) -> i32 {
        debug_println!(7, 0, "PROPAGATOR: Propagation callback invoked");
        // For now, no propagation
        // This could deduce new assignments
        0
    }

    fn cb_add_reason_clause_lit(&mut self, _propagated_lit: i32) -> i32 {
        debug_println!(
            7,
            0,
            "PROPAGATOR: Adding reason clause for literal {}",
            _propagated_lit
        );
        // For now, no reason clauses
        // This could explain propagations
        0
    }

    fn cb_has_external_clause(&mut self, is_forgettable: &mut bool) -> bool {
        debug_println!(
            7,
            0,
            "PROPAGATOR: Checking for external clauses (forgettable: {})",
            is_forgettable
        );
        // For now, no external clauses
        if (*self.disequalities.borrow_mut()).is_empty() {
            false
        } else {
            // this is basically saying that the clause is not forgettable; cvc5 also does false
            *is_forgettable = false;
            debug_println!(
                4,
                0,
                "In cb_has_external_clause: We have the following disequalities: {:?}",
                self.disequalities.borrow()[0]
            );
            true
        }
    }

    fn cb_add_external_clause_lit(&mut self) -> i32 {
        // For now, no external clauses
        let mut v = self.disequalities.borrow_mut();
        assert!(!v.is_empty());
        debug_println!(4, 0, "We start with the following disequalities: {:?}", v);
        let last_index = v.len() - 1;
        debug_println!(11, 0, "We have the next clause {:?}", v[last_index]);
        let literal = if v[last_index].is_empty() {
            v.pop();
            0
        } else {
            v[last_index].pop().unwrap()
        };
        drop(v);
        if literal != 0 {
            self.add_lit_to_proof_tracer(literal);
        }
        if let Some(term) = self.solver_state.get_term_from_lit_safe(literal) {
            debug_println!(
                11,
                0,
                "PROPAGATOR: Adding external clause literal (might be negated) {} which is term {}",
                literal,
                term
            );
        } else {
            debug_println!(11, 0, "END OF CLAUSE");
            assert!(literal == 0);
        }
        debug_println!(4, 0, "{}", self.solver_state.egraph);
        literal
    }
}
