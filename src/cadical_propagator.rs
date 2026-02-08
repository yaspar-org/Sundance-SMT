use crate::arithmetic::lp::{check_integer_constraints_satisfiable, ArithResult, ArithSolver};
use crate::arithmetic::nelsonoppen::nelson_oppen_clause_pair;
use crate::cnf::CNFConversion as _;
use crate::egraphs::congruence_closure::{
    get_child, get_parent, process_assignment, proof_forest_backtrack,
};
use crate::egraphs::datastructures::Predecessor;
use crate::egraphs::egraph::Egraph;
use crate::egraphs::proofforest::ProofForestEdge;
use crate::proof::proof_tracer::SMTProofTracker;
use crate::quantifiers::quantifier::instantiate_quantifiers;
use crate::quantifiers::quantifier::QuantifierInstance::{Instantiation, Skolemization};
use crate::utils::{DeterministicHashMap, DeterministicHashSet};
use cadical_sys::{CaDiCal, ExternalPropagator};
use std::cell::RefCell;
use std::rc::Rc;

/// Should we keep backtracking on stack at level
///
/// Note: we are currently not adding fixed levels to backtracking
/// We treat fixed literals at level >0 as unfixed and so we trust the SAT solver to just give us new assignments if it backtracks past a certain point
fn keep_backtracking(
    proof_forest_stack: &[(usize, ProofForestEdge, u64, ProofForestEdge)],
    level: usize,
) -> bool {
    if proof_forest_stack.is_empty() {
        return false;
    }
    let last_elem_level = proof_forest_stack[proof_forest_stack.len() - 1].0;

    last_elem_level > level // note that backtracking is >=
}

/// Our implemetation of a Cadical Propagator
pub struct CustomExternalPropagator<'a> {
    pub decision_level: usize,
    pub egraph: &'a mut Egraph,
    pub disequalities: RefCell<Vec<Vec<i32>>>, // might be paying a bit of overhead for RefCell
    pub fixed_literals: DeterministicHashSet<i32>,
    pub proof_tracker: Rc<RefCell<SMTProofTracker>>,
    pub assignments: Vec<i32>, // maps abs(literal) -> (decision level assigned + 1) * sgn(literal)
    pub solver: *mut CaDiCal,
    pub arithmetic: ArithSolver, // whether we are doing arithmetic solving or not
}

impl<'a> CustomExternalPropagator<'a> {
    pub fn add_lit_to_proof_tracker(&mut self, lit: i32) {
        let lit = lit.abs(); // only add the positive version
        if self.proof_tracker.borrow().terms_list.contains_key(&lit)
        // || self.proof_tracker.borrow().terms_list.contains_key(&-lit)
        {
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
            self.egraph.get_term_from_lit(lit),
            self.egraph.get_term_from_lit(lit).uid()
        );

        if let Some(id) = self.egraph.cnf_cache.var_map_reverse.get(&lit) {
            let term = self.egraph.get_term(*id);
            self.proof_tracker
                .borrow_mut()
                .terms_list
                .insert(lit, (*id, term, true));
        } else if let Some(id) = self.egraph.cnf_cache.var_map_reverse.get(&-lit) {
            let term = self.egraph.get_term(*id);
            self.proof_tracker
                .borrow_mut()
                .terms_list
                .insert(-lit, (*id, term, false));
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
            7,
            0,
            "PROPAGATOR: Processing assignments (level {}): {:?}",
            self.decision_level,
            lits
        );
        debug_println!(6, 0, "{}", self.egraph);
        for lit in lits {
            debug_println!(
                7,
                0,
                "Assigning the literal {:?} (level {}) which is {}",
                lit,
                self.decision_level,
                self.egraph.get_term_from_lit(*lit)
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

            self.add_lit_to_proof_tracker(*lit); // adding the literal to the proof_tracker

            let negated_model_or_datatype_constraints_opt =
                process_assignment(*lit, self.egraph, self.decision_level, false, false, None);

            if let Some(negated_model_or_datatype_constraints) =
                negated_model_or_datatype_constraints_opt
            {
                for constraint in negated_model_or_datatype_constraints {
                    // todo: deleting this ordering thing -> just for debuggin
                    let mut constraint_ordered = constraint.clone();
                    constraint_ordered.sort();
                    debug_println!(
                        16,
                        0,
                        "[in notify_assignment] We have the following constraint: {:?}",
                        constraint_ordered
                    );
                    for lit in constraint.clone() {
                        debug_println!(12, 4, "{}", self.egraph.get_term_from_lit(lit));
                    }
                    let mut shrunk_constraint = vec![];
                    let mut already_considered = DeterministicHashSet::default();
                    for lit in constraint {
                        if already_considered.contains(&lit) {
                            // TODO: we are checking for repeats here, but we should fix this at the conflict clause level so that we never get repeats
                            // the repeats are coming from (= x y) and true being merged and x and y being merged
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
                    // todo: deleting this ordering thing -> just for debuggin
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
                        self.add_lit_to_proof_tracker(*lit);
                        self.add_observed_variable(*lit);
                        debug_println!(11, 1, "  {}", self.egraph.get_term_from_lit(*lit));
                    }

                    // Store the theory lemma with its proof steps
                    // TODO: I am not doing proof step stuff right now, but I need to add it back in
                    // let proof_steps = self.egraph.get_proof_steps_for_lemma(&shrunk_constraint);

                    debug_println!(
                        14 - 3,
                        0,
                        "In case 1 currently disequalities: {:?}",
                        self.disequalities.borrow()
                    );

                    // self.theory_lemmas.borrow_mut().push((shrunk_constraint.clone(), proof_steps));

                    // Add theory clause to proof tracker
                    // note that this is not necessary anymore

                    // let theory_reason = format!("congruence_closure_level_{}", self.decision_level);
                    // self.proof_tracker
                    //     .borrow_mut()
                    //     .add_theory_clause(shrunk_constraint.clone(), theory_reason);

                    self.disequalities.borrow_mut().push(shrunk_constraint);
                    debug_println!(
                        14 - 3,
                        0,
                        "We have the following disequalities: {:?}",
                        self.disequalities.borrow()
                    );
                }
            }
        }
    }

    fn notify_new_decision_level(&mut self) {
        debug_println!(
            11,
            0,
            "PROPAGATOR: New decision level {} -> {}",
            self.decision_level,
            self.decision_level + 1
        );
        if self.decision_level + 2 >= self.egraph.predecessor_level.len() {
            debug_println!(
                2,
                2,
                "Resizing predecessor level array to {}",
                2 * self.egraph.predecessor_level.len()
            );
            self.egraph
                .predecessor_level
                .resize(2 * self.egraph.predecessor_level.len(), 0);
        }
        self.decision_level += 1;
        debug_println!(
            4,
            0,
            "Setting predecessor level for level {} to {}",
            self.decision_level,
            self.egraph.predecessor_hash
        );
        self.egraph.predecessor_level[self.decision_level] = self.egraph.predecessor_hash;
    }

    fn notify_backtrack(&mut self, level: usize) {
        debug_println!(
            23,
            0,
            "PROPAGATOR: Backtracking from level {} to level {}",
            self.decision_level,
            level
        );
        debug_println!(
            4,
            1,
            "Current backtrack stack: {:?}",
            self.egraph.proof_forest_backtrack_stack
        );

        self.egraph.predecessor_hash += 1;

        // resetting the assignments to 0 for all levels greater than the current level
        for i in 1..self.assignments.len() {
            if self.assignments[i].abs() > (level + 1) as i32 {
                debug_println!(7, 0, "We are backtracking on assignment {}", i);
                self.assignments[i] = 0;
            }
        }

        // TODO: not deactivating for rn, because important terms are getting deactivated
        // deactivate_bits(level, self.egraph);

        for i in level + 1..self.decision_level + 1 {
            debug_println!(
                4,
                1,
                "We are updating level {} from {} to {}",
                i,
                self.egraph.predecessor_level[i],
                self.egraph.predecessor_hash
            );
            self.egraph.predecessor_level[i] = self.egraph.predecessor_hash;
        }

        self.decision_level = level;

        debug_println!(
            7,
            0,
            "Before backtracking we hav the stack: {:?}",
            self.egraph
                .proof_forest_backtrack_stack
                .iter()
                .map(|(size, edge, _, _)| (
                    size,
                    format!(
                        "{} = {}",
                        self.egraph.get_term(get_child(edge)),
                        self.egraph.get_term(get_parent(edge))
                    )
                ))
                .collect::<Vec<_>>()
        );
        // TODO: right now we are assuming only fixed literals can be assigned at level 0
        while keep_backtracking(&self.egraph.proof_forest_backtrack_stack, level) {
            let (_, backtrack_equality, y, y_root) =
                self.egraph.proof_forest_backtrack_stack.pop().unwrap();
            debug_println!(16, 1, "Backtracking equality: {:?}", backtrack_equality);
            proof_forest_backtrack(backtrack_equality, y, y_root, self.egraph)
        }

        debug_println!(
            7,
            0,
            "After backtracking we have the stack: {:?}",
            self.egraph
                .proof_forest_backtrack_stack
                .iter()
                .map(|(size, edge, _, _)| (
                    size,
                    format!(
                        "{} = {}",
                        self.egraph.get_term(get_child(edge)),
                        self.egraph.get_term(get_parent(edge))
                    )
                ))
                .collect::<Vec<_>>()
        );

        // TODO: have to clone here which is really bad
        for (term_num, (equality, term_parent_original, new_equality, original_y)) in
            self.egraph.from_quantifier_backtrack_set.clone().iter()
        {
            let congruence_pairs = if let ProofForestEdge::Congruence { pairs, .. } = equality {
                pairs
            } else {
                panic!("We should not be considering a term that is not a congruence");
            };
            for (p1, p2) in congruence_pairs.iter() {
                if self.egraph.find(*p1) != self.egraph.find(*p2) {
                    // remove the equality from egraph
                    debug_println!(
                        16,
                        0,
                        "[QUANTIFIER_BACKTRACK] We are backtracking on the equality {:?}",
                        equality
                    );
                    proof_forest_backtrack(
                        new_equality.clone(),
                        *original_y, //*term_num,
                        term_parent_original.clone(),
                        self.egraph,
                    );
                    // remove from backtracking list
                    debug_println!(
                        16,
                        0,
                        "We are removing the equality between {} and {} at level {} [{:?}] from the backtracking list because of failed equality between {} and {}",
                        self.egraph.get_term(equality.get_parent()),
                        self.egraph.get_term(equality.get_child()),
                        self.decision_level,
                        equality,
                        self.egraph.get_term(*p1),
                        self.egraph.get_term(*p2)
                    );
                    debug_println!(11, 0, "{}", self.egraph);
                    self.egraph.from_quantifier_backtrack_set.remove(term_num);
                    break;
                }
            }
        }

        // adding the new predecessors created by quantifiers to the predecessors list
        for (term, parents) in &self.egraph.predecessors_created_by_quantifiers {
            let current_ancestor = self.egraph.find(*term);
            // if *term == current_ancestor {
            //     continue;
            // }

            for parent in parents {
                debug_println!(
                    11,
                    0,
                    "We are updating the predecessor of {} [ancestor of {}] to {} at level: {}; hash: {}",
                    self.egraph.get_term(current_ancestor),
                    self.egraph.get_term(*term),
                    self.egraph.get_term(*parent),
                    level,
                    self.egraph.predecessor_hash
                );
                let predecessor = Predecessor {
                    level,
                    hash: self.egraph.predecessor_hash,
                    predecessor: *parent,
                    inner_term: *term,
                };
                self.egraph.predecessors[current_ancestor as usize].insert(*parent, predecessor);

                debug_println!(
                    11,
                    0,
                    "We have the predecessors of {}",
                    self.egraph.get_term(current_ancestor)
                );
                for pred in self.egraph.predecessors[current_ancestor as usize].clone() {
                    debug_println!(
                        11,
                        4,
                        "{} with level {} and hash {}",
                        self.egraph.get_term(pred.1.predecessor),
                        pred.1.level,
                        pred.1.hash
                    )
                }
            }
        }

        // once we get to level 0, we don't need to keep track of this anymore since we have reached the bottom case
        if level == 0 {
            self.egraph.predecessors_created_by_quantifiers = DeterministicHashMap::new();
        }

        // redoing the union_to_eclass stuff
        let union_to_eclass_info = self.egraph.union_to_eclass.clone();
        for (term, func, subterms) in union_to_eclass_info {
            self.egraph.find_and_union_to_eclass(term, func, subterms);
        }

        // once we get to level 0, we don't need to keep track of this anymore since we have reached the bottom case
        if level == 0 {
            self.egraph.union_to_eclass = DeterministicHashSet::new();
        }

        debug_println!(11, 0, "{}", self.egraph);
    }

    fn cb_check_found_model(&mut self, model: &[i32]) -> bool {
        debug_println!(
            24,
            0,
            "PROPAGATOR: Checking model: {:?} [{:?}]",
            model,
            model
                .iter()
                .map(|x| self.egraph.get_term_from_lit(*x))
                .collect::<Vec<_>>(),
        );

        // for lit in model{
        //      debug_println!(11, 4, "{}", self.egraph.get_term_from_lit(*lit))
        // }

        if !self.disequalities.borrow_mut().is_empty() {
            debug_println!(
                7,
                0,
                "Trying to check model when the disequalities are not empty"
            );
            return false;
        }

        for term in model {
            let (u64_val, polarity) = self.egraph.get_u64_from_lit_with_polarity(*term);
            debug_println!(
                24,
                4,
                "{} [lit: {}] [u64: {} with polarity {}]",
                self.egraph.get_term_from_lit(*term),
                term,
                u64_val,
                polarity
            );
        }
        debug_println!(16, 0, "{}", self.egraph);

        // Check arithmetic consistency before instantiating quantifiers
        debug_println!(21, 0, "Starting arithmetic check",);

        match check_integer_constraints_satisfiable(&self.arithmetic, model, self.egraph) {
            ArithResult::Unsat(arithmetic_literals) => {
                {
                    debug_println!(
                        21,
                        0,
                        "PROPAGATOR: Arithmetic inconsistency detected: {:?}",
                        arithmetic_literals
                    );
                    // let negated_arithmetic_literals = arithmetic_literals.iter().map(|x| -x).collect();
                    self.disequalities.borrow_mut().push(arithmetic_literals);
                    return false;
                }
            }
            ArithResult::Sat(literals) => {
                for set in literals.values() {
                    let mut t = set.iter();
                    let first = t.next().unwrap();

                    for term in t {
                        let pair = if first < term {
                            (first, term)
                        } else {
                            (term, first)
                        };

                        if let Some(term) = nelson_oppen_clause_pair(*pair.0, *pair.1, self.egraph)
                        {
                            debug_println!(25, 0, "adding in the nelson oppen term {}", term);
                            let term_nnf = term.nnf(self.egraph);
                            // println!("we have the term {:?}", term);
                            self.egraph
                                .insert_predecessor(&term_nnf, None, None, true, None);
                            let term_cnf = term.cnf_tseitin(self.egraph);
                            // assert!(term_cnf.0.len() == 1, "We have term_cnf {:?}", term_cnf);
                            for clause in term_cnf {
                                for lit in &clause.0 {
                                    self.add_observed_variable(*lit);
                                    self.add_lit_to_proof_tracker(*lit);
                                }
                                self.disequalities.borrow_mut().push(clause.0.clone());
                            }
                        }
                    }
                }

                // todo: have a helper function for this, because it gets included twice
                // for literal in literals {
                //     // if self.egraph.nelson_oppen_literals.contains(&literal) {
                //     //     continue;
                //     // }
                //     // self.egraph.nelson_oppen_literals.insert(literal);

                //     if let Some(term) = nelson_oppen_clause_ineq(literal, &mut self.egraph) {
                //         let term_nnf = term.sundance_nnf(&mut *self.egraph.cnfenv.context);
                //         // println!("we have the term {:?}", term);
                //         self.egraph.insert_predecessor(&term_nnf, None, None, false, None);
                //         let term_cnf = term.cnf_tseitin(&mut *self.egraph.cnfenv.context);
                //         // assert!(term_cnf.0.len() == 1, "We have term_cnf {:?}", term_cnf);
                //         for clause in term_cnf {
                //             for lit in &clause.0 {
                //                 self.add_observed_variable(*lit);
                //                 self.add_lit_to_proof_tracker(*lit);
                //             }
                //             self.disequalities.borrow_mut().push(clause.0.clone());
                //         }
                //     }
                // }
            }
            ArithResult::None => {}
        }

        // do the Nelson-Oppen disequality check
        // for literal in model {
        //     if self.egraph.nelson_oppen_literals.contains(literal) {
        //         continue;
        //     }
        //     self.egraph.nelson_oppen_literals.insert(*literal);

        //     if let Some(term) = nelson_oppen_clause(*literal, &mut self.egraph) {
        //         let term_nnf = term.sundance_nnf(&mut self.egraph.cnfenv);
        //         // println!("we have the term {:?}", term);
        //         self.egraph.insert_predecessor(&term_nnf, None, None, false, None);
        //         let term_cnf = term.sundance_cnf_tseitin(&mut self.egraph.cnfenv);
        //         // assert!(term_cnf.0.len() == 1, "We have term_cnf {:?}", term_cnf);
        //         for clause in term_cnf {
        //             for lit in &clause.0 {
        //                 self.add_observed_variable(*lit);
        //                 self.add_lit_to_proof_tracker(*lit);
        //             }
        //             self.disequalities.borrow_mut().push(clause.0.clone());
        //         }
        //     }
        // }

        if !self.disequalities.borrow().is_empty() {
            return false;
        }

        debug_println!(11, 0, "Starting quantifier instantiations");
        let quantifier_instantiations = instantiate_quantifiers(
            self.egraph,
            &self.proof_tracker,
            &self.assignments,
            self.decision_level,
        );
        debug_println!(
            11,
            0,
            "Found quantifier instantiations {:?}",
            quantifier_instantiations
        );

        if quantifier_instantiations.is_empty() {
            debug_println!(10, 0, "{}", self.egraph);
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
                        self.add_lit_to_proof_tracker(*lit);
                    }

                    // TODO: since I am adding literals, I might have to add them as observed literals
                    self.disequalities.borrow_mut().push(clause.clone());
                }
                Skolemization { clause } => {
                    for lit in clause {
                        self.add_observed_variable(*lit);
                        self.add_lit_to_proof_tracker(*lit);
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
        // always no decision
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
            self.add_lit_to_proof_tracker(literal);
        }
        if let Some(term) = self.egraph.get_term_from_lit_safe(literal) {
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
        debug_println!(4, 0, "{}", self.egraph);
        literal
    }
}
