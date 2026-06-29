// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Keeps track of the eDRAT proof
//!
use crate::debug_println;
use crate::proof::{ProofStep, ProofStepType, Theory};
use core::panic;
use std::cmp::Eq;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::ops::Neg;
use yaspar_ir::ast::{ATerm::*, FunctionMeta, Repr, Sig, SortDef, Str, Term};

/// Implementation of ProofTracer both SAT solver clauses and theory clauses
/// to generate an eDRAT proof.
pub struct SMTProofTracer {
    proof_steps: Vec<ProofStep>,
    terms_list: HashMap<i32, (u64, Term, bool)>,
    sorts: HashMap<Str, SortDef>,
    symbol_table: HashMap<Str, Vec<(Sig, FunctionMeta)>>,
    instantiations_for_smt2: Vec<(Term, Vec<(Term, bool)>)>,
}

fn polarize_term(term: &Term, polarity: bool) -> Term {
    if polarity {
        return term.clone();
    }
    match term.repr() {
        Not(t) => t.clone(),
        _ => {
            panic!("Should not have this case {}", term);
        }
    }
}

/// Returns true if the clause contains a literal and its negation (i.e., both `x` and `-x`).
/// Written for generic iterators, since clauses in this file are both `Vec`s and `&[i32]` arrays.
fn is_tautology<'a, I, T>(clause: I) -> bool
where
    I: IntoIterator<Item = &'a T>,
    T: 'a + Copy + Eq + Hash + Neg<Output = T>,
{
    let mut seen = HashSet::new();
    for &lit in clause {
        if seen.contains(&-lit) {
            return true;
        }
        seen.insert(lit);
    }
    false
}

/// Format a sort definition as a declare-sort command
fn format_sort_declaration(sort_name: &Str, sort_def: &SortDef) -> String {
    match sort_def {
        SortDef::Opaque(_) => String::new(),
        SortDef::OpaqueDeclared(arity) => {
            format!("(declare-sort {} {})\n", sort_name, arity)
        }
        SortDef::Transparent { params, sort } => {
            let params_str = params
                .iter()
                .map(|p| p.to_string())
                .collect::<Vec<_>>()
                .join(" ");
            format!("(define-sort {} ({}) {})\n", sort_name, params_str, sort)
        }
        SortDef::Datatype(..) => {
            // datatypes handled by `format_datatype_declaration`
            String::new()
        }
    }
}

/// Format a sort definition as a declare-sort command
fn format_datatype_declaration(sorts: &HashMap<Str, SortDef>) -> String {
    let mut sort_str = vec![];
    let mut ctor_strs = vec![];
    let mut datatype_funs = HashSet::new();
    for (sort_name, sort_def) in sorts {
        if let SortDef::Datatype(data) = sort_def {
            sort_str.push(format!("({} {})", sort_name, data.params.len()));

            for ctor in &data.constructors {
                datatype_funs.insert(&ctor.ctor);
                for sel in &ctor.args {
                    datatype_funs.insert(&sel.0);
                }
            }

            ctor_strs.push(data.to_string());
        }
    }

    if sort_str.is_empty() {
        String::new()
    } else {
        format!(
            "(declare-datatypes ({}) ({}))\n",
            sort_str.join(" "),
            ctor_strs.join(" ")
        )
    }
}

/// Format a function signature as a declare-fun command
fn format_function_declaration(symbol_name: &Str, sigs: &[(Sig, FunctionMeta)]) -> String {
    // overloading is only possible for generated functions; we skip them.
    if sigs.len() != 1 {
        return String::new();
    }

    let (sig, meta) = &sigs[0];

    match (sig, meta) {
        (Sig::ParFunc(_, _, input_sorts, output_sort), FunctionMeta::OpaqueDeclared) => {
            // user declared uninterpreted functions; must be non-polymorphic functions
            let input_sorts_str = input_sorts
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
                .join(" ");
            format!(
                "(declare-fun {} ({}) {})\n",
                symbol_name, input_sorts_str, output_sort
            )
        }
        (Sig::ParFunc(..), FunctionMeta::Defined(meta)) => {
            if !meta.rec_deps.is_empty() {
                panic!("We do not handle recursive function definitions!");
            }
            format!("(define-fun {})\n", meta.def)
        }
        _ => String::new(),
    }
}

impl SMTProofTracer {
    /// Create a new proof tracker
    pub fn new(
        sorts: HashMap<Str, SortDef>,
        symbol_table: HashMap<Str, Vec<(Sig, FunctionMeta)>>,
    ) -> Self {
        Self {
            proof_steps: Vec::new(),
            terms_list: HashMap::new(),
            sorts,
            symbol_table,
            instantiations_for_smt2: Vec::new(),
        }
    }

    ////////////////////////////////////////////////////////////////////////////

    pub fn push_step(&mut self, clause: &Vec<i32>, typ: ProofStepType) {
        if !is_tautology(clause) {
            self.proof_steps.push(ProofStep {
                clause: clause.clone(),
                typ,
            })
        }
    }

    pub fn push_steps(&mut self, clauses: &Vec<Vec<i32>>, typ: ProofStepType) {
        for clause in clauses {
            self.push_step(clause, typ.clone());
        }
    }

    pub fn add_original_clause(&mut self, clause: &Vec<i32>) {
        self.push_step(clause, ProofStepType::OriginalClause);
    }

    pub fn add_sat_clause(&mut self, clause: &Vec<i32>) {
        self.push_step(clause, ProofStepType::SATClause);
    }

    pub fn record_deletion(&mut self, clause: &Vec<i32>) {
        self.push_step(clause, ProofStepType::Deletion);
    }

    pub fn add_theory_clause(&mut self, clause: &Vec<i32>, theory: Theory) {
        self.push_step(clause, ProofStepType::TheoryClause(theory));
    }

    ////////////////////////////////////////////////////////////////////////////

    // TODO: If each literal is only needed once, then they can be removed from the hashmap
    fn get_lit_info(&self, lit: i32) -> Option<(i32, u64, Term, bool)> {
        if let Some((id, term, polarity)) = self.terms_list.get(&lit) {
            Some((lit, *id, term.clone(), *polarity))
        } else if let Some((id, term, polarity)) = self.terms_list.get(&-lit) {
            Some((-lit, *id, term.clone(), *polarity))
        } else {
            None
        }
    }

    /// Registers a `term` with the proof tracer.
    /// Basically, each term registered this way gets an `(edrat-literal ...)`
    /// line in the proof, and may be referenced in later DIMACS-style clauses.
    pub fn register_term(&mut self, literal: i32, term: &Term, polarity: bool) {
        if self.get_lit_info(literal).is_none() {
            self.terms_list
                .insert(literal, (term.uid(), term.clone(), polarity));
        }
    }

    /// Returns whether a term with the `literal` (or its negation) has been registered.
    pub fn is_lit_registered(&self, literal: i32) -> bool {
        self.get_lit_info(literal).is_some() || self.get_lit_info(-literal).is_some()
    }

    /// Pushes literal definitions.
    /// Panics if a literal is not in the terms list.
    fn introduce_literals(
        &self,
        literals_defined: &mut HashSet<i32>,
        clause: &Vec<i32>,
        out: &mut String,
    ) {
        let mut temp_output = String::new();
        for &lit in clause {
            debug_println!(12, 2, "Introducing the literal {}", lit);
            if let Some((lit, _id, term, polarity)) = self.get_lit_info(lit) {
                debug_println!(9, 2, "The lit exists with term {}", term);
                let lit = lit.abs();
                let polarized_term = polarize_term(&term, polarity);

                debug_println!(
                    19,
                    2,
                    "we go from term {} to polarized_term {}",
                    term,
                    polarized_term
                );

                if !literals_defined.contains(&lit) {
                    temp_output.push_str(&format!("(edrat-literal {} {})\n", lit, polarized_term));
                    literals_defined.insert(lit);
                }
            } else {
                panic!(
                    "We should have introduced the literal {} in the terms list",
                    lit
                );
            }
        }
        out.push_str(&temp_output);
    }

    /// Like `introduce_literals`, but skips literals not in the terms list
    /// (e.g., SAT-internal auxiliary variables that were never registered).
    fn introduce_literals_lenient(
        &self,
        literals_defined: &mut HashSet<i32>,
        clause: &Vec<i32>,
        out: &mut String,
    ) {
        let mut temp_output = String::new();
        for &lit in clause {
            if let Some((lit, _id, term, polarity)) = self.get_lit_info(lit) {
                let lit = lit.abs();
                let polarized_term = polarize_term(&term, polarity);
                if !literals_defined.contains(&lit) {
                    temp_output.push_str(&format!("(edrat-literal {} {})\n", lit, polarized_term));
                    literals_defined.insert(lit);
                }
            }
        }
        out.push_str(&temp_output);
    }

    ////////////////////////////////////////////////////////////////////////////

    /// Adds one or several proof steps to the proof to witness the derivation
    /// of a Skolemization or an instantiation.
    ///
    /// Supposing that `parent` is a top-level quantified formula (whether with
    /// a leading `Not` or not), then we can Skolemize/instantiate the
    /// parent in the eDRAT proof by: (1) introducing the instantiation as
    /// a new eDRAT literal, and (2) adding an implication (parent => child)
    /// to the proof. In CNF, this is written as (-p or c).
    ///
    /// However, because Sundance assumes that all its terms are in NNF/CNF
    /// form, and because Sundance does not reduce terms under quantifiers
    /// during pre-processing, we end up with a situation where the
    /// instantiated child may not match the reduced formula that Sundance
    /// eventually adds to its e-graph. In summer 2026, we decided that
    /// Skolem/instantiation eDRAT proof lines should focus solely on
    /// the Skolemization/instantiation, and any formula reductions should
    /// be handled on different proof lines.
    ///
    /// As a result, we carefully register the un-reduced child with only
    /// the eDRAT proof (although the caller must reserve a DIMACS literal
    /// for it beforehand), and then if the reduction differs from the
    /// un-reduced child, we derive the "e-graph implication" using modus ponens
    /// via "parent => child", "child => reduced child".
    pub fn push_skolem_or_instantiation_derivation(
        &mut self,
        parent_literal: i32,
        child_literal: i32,
        child: &Term,
        reduced_literal: i32,
        reduced: &Term,
        typ: ProofStepType,
    ) {
        assert!(parent_literal != 0 && reduced_literal != 0);
        if child.uid() != reduced.uid() {
            assert!(child_literal != 0);
        }

        // We ultimately want to derive this implication
        let imp = vec![-parent_literal, reduced_literal];

        // If the child doesn't reduce, we can add the implication directly
        if child.uid() == reduced.uid() {
            self.push_step(&imp, typ);
        } else {
            // Otherwise, we derive it through additional implications
            let child_imp = vec![-parent_literal, child_literal];
            let equiv_imp = vec![-child_literal, reduced_literal];

            // The child term won't be registered anywhere else
            self.register_term(child_literal, child, true);

            // Derive `imp` through modus ponens via Boolean reasoning
            self.push_step(&child_imp, typ);
            self.add_theory_clause(&equiv_imp, Theory::Boolean);
            self.add_sat_clause(&imp);

            // Delete any clauses mentioning the un-reduced child
            self.record_deletion(&child_imp);
            self.record_deletion(&equiv_imp);
        }
    }

    /// Generate eDRAT proof as a string
    pub fn generate_edrat(&mut self) -> String {
        let mut output = String::new();
        self.instantiations_for_smt2.clear(); // Clear previous instantiations
        let mut literals_defined: HashSet<i32> = HashSet::new();

        // emit the sorts, datatypes, and the symbol table
        for (sort, sort_def) in &self.sorts {
            output.push_str(&format_sort_declaration(sort, sort_def));
        }

        let datatype_string = format_datatype_declaration(&self.sorts);
        output.push_str(&datatype_string);

        for (symbol, sigs) in &self.symbol_table {
            output.push_str(&format_function_declaration(symbol, sigs));
        }

        // Depending on the proof step, introduce new eDRAT literals
        for step in &self.proof_steps {
            let clause = &step.clause;
            let typ = &step.typ;
            match typ {
                ProofStepType::OriginalClause
                | ProofStepType::TheoryClause(..)
                | ProofStepType::Instantiation
                | ProofStepType::SATClause
                | ProofStepType::Deletion => {
                    self.introduce_literals_lenient(&mut literals_defined, clause, &mut output)
                }
                ProofStepType::Skolemization {
                    parent_term,
                    skolem_vars,
                } => {
                    debug_println!(
                        29,
                        2,
                        "The skolem vars for clause {:?}: {:?}",
                        clause,
                        skolem_vars
                    );
                    for (i, var) in skolem_vars.iter().enumerate() {
                        // CC TODO think about negated parent term, if (negated forall)
                        output.push_str(&format!(
                            "(declare-skolem {} {} {} {})\n",
                            parent_term, i, var.0, var.1
                        ));
                    }
                    self.introduce_literals(&mut literals_defined, clause, &mut output);
                }
            }

            step.push_line_to(&mut output);

            // Stop adding proof steps to the output once the empty clause is derived
            if matches!(typ, ProofStepType::SATClause) && clause.is_empty() {
                break;
            }
        }
        output
    }
}
