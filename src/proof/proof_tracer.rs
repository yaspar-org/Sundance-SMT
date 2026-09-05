// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Keeps track of the eDRAT proof
//!
use crate::debug_println;
use crate::proof::{ProofStep, ProofStepType, Theory};
use core::panic;
use std::cmp::Eq;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::ops::Neg;
use yaspar_ir::ast::{ATerm::*, FunctionMeta, Repr, Sig, SortDef, Str, SymbolQuote, Term};

/// Implementation of ProofTracer both SAT solver clauses and theory clauses
/// to generate an eDRAT proof.
pub struct SMTProofTracer {
    proof_steps: Vec<ProofStep>,
    terms_list: HashMap<i32, (u64, Term, bool)>,
    sorts: HashMap<Str, SortDef>,
    symbol_table: HashMap<Str, Vec<(Sig, FunctionMeta)>>,
    instantiations_for_smt2: Vec<(Term, Vec<(Term, bool)>)>,
    registered_clause_callbacks: HashMap<Vec<i32>, usize>,
    /// Number of clauses deleted by CaDiCaL (for stats)
    pub(crate) deleted_clauses: u64,
    /// When true, all proof-recording methods are no-ops. Set when no proof
    /// output is requested (no --proof / --partial-proof), so the eDRAT
    /// bookkeeping — a growing step vector and two hash maps touched on every
    /// clause and literal — costs nothing on the common solve-only path. The
    /// tracer is also not connected to CaDiCaL in that case (see cdcl.rs), so
    /// the callback side is skipped too.
    pub disabled: bool,
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

fn normalize_clause(clause: &[i32]) -> Vec<i32> {
    let mut normalized = clause.to_vec();
    normalized.sort_unstable();
    normalized.dedup();
    normalized
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
            let variables = meta
                .def
                .vars
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(" ");
            format!(
                "(define-fun {} ({}) {} {})\n",
                meta.def.name.sym_quote(),
                variables,
                meta.def.out_sort,
                meta.def.body
            )
        }
        _ => String::new(),
    }
}

fn collect_global_symbols(term: &Term, symbols: &mut HashSet<Str>) {
    match term.repr() {
        Global(qid, ..) | App(qid, ..) => {
            symbols.insert(qid.0.symbol.clone());
        }
        _ => {}
    }
    for subterm in term.repr().sub_terms() {
        collect_global_symbols(subterm, symbols);
    }
}

fn format_function_declarations(symbol_table: &HashMap<Str, Vec<(Sig, FunctionMeta)>>) -> String {
    let mut symbols = symbol_table.keys().collect::<Vec<_>>();
    symbols.sort_by_key(|symbol| symbol.to_string());

    let mut output = String::new();
    let mut definitions = Vec::new();
    for symbol in symbols {
        if matches!(
            symbol_table[symbol].as_slice(),
            [(Sig::ParFunc(..), FunctionMeta::Defined(_))]
        ) {
            definitions.push(symbol);
        } else {
            output.push_str(&format_function_declaration(symbol, &symbol_table[symbol]));
        }
    }

    let dependencies = definitions
        .iter()
        .map(|symbol| {
            let symbol = *symbol;
            let [(_, FunctionMeta::Defined(meta))] = symbol_table[symbol].as_slice() else {
                unreachable!();
            };
            let mut dependencies = HashSet::new();
            collect_global_symbols(&meta.def.body, &mut dependencies);
            (symbol.clone(), dependencies)
        })
        .collect::<HashMap<_, _>>();

    let mut emitted = HashSet::new();
    while !definitions.is_empty() {
        let Some(index) = definitions.iter().position(|symbol| {
            dependencies[*symbol].iter().all(|dependency| {
                !dependencies.contains_key(dependency) || emitted.contains(dependency)
            })
        }) else {
            panic!("We do not handle recursive function definitions!");
        };
        let symbol = definitions.remove(index);
        output.push_str(&format_function_declaration(symbol, &symbol_table[symbol]));
        emitted.insert(symbol.clone());
    }

    output
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
            registered_clause_callbacks: HashMap::new(),
            deleted_clauses: 0,
            disabled: false,
        }
    }

    ////////////////////////////////////////////////////////////////////////////

    pub fn push_step(&mut self, clause: &[i32], typ: ProofStepType) {
        if self.disabled {
            return;
        }
        if !is_tautology(clause) {
            self.proof_steps.push(ProofStep {
                clause: clause.to_vec(),
                typ,
            })
        }
    }

    pub fn push_steps(&mut self, clauses: &[Vec<i32>], typ: ProofStepType) {
        for clause in clauses {
            self.push_step(clause, typ.clone());
        }
    }

    pub fn add_original_clause(&mut self, clause: &[i32]) {
        self.push_step(clause, ProofStepType::OriginalClause);
    }

    pub fn add_sat_clause(&mut self, clause: &[i32]) {
        self.push_step(clause, ProofStepType::SATClause);
    }

    pub fn record_deletion(&mut self, clause: &[i32]) {
        self.push_step(clause, ProofStepType::Deletion);
    }

    pub fn add_theory_clause(&mut self, clause: &[i32], theory: Theory) {
        self.push_step(clause, ProofStepType::TheoryClause(theory));
    }

    pub fn register_clause_for_cadical_callback(&mut self, clause: &[i32]) {
        if self.disabled {
            return;
        }
        let clause = normalize_clause(clause);
        *self.registered_clause_callbacks.entry(clause).or_default() += 1;
    }

    pub fn consume_clause_callback_registration(&mut self, clause: &[i32]) -> bool {
        match self
            .registered_clause_callbacks
            .entry(normalize_clause(clause))
        {
            Entry::Occupied(mut entry) => {
                if *entry.get() == 1 {
                    entry.remove();
                } else {
                    *entry.get_mut() -= 1;
                }
                true
            }
            Entry::Vacant(_) => false,
        }
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
        if self.disabled {
            return;
        }
        if self.get_lit_info(literal).is_none() {
            self.terms_list
                .insert(literal, (term.uid(), term.clone(), polarity));
        }
    }

    /// Returns whether a term with the `literal` (or its negation) has been registered.
    pub fn is_lit_registered(&self, literal: i32) -> bool {
        self.get_lit_info(literal).is_some() || self.get_lit_info(-literal).is_some()
    }

    /// Emits definitions for the literals in `clause`.
    fn introduce_literals(
        &self,
        literals_defined: &mut HashSet<i32>,
        clause: &[i32],
        out: &mut String,
    ) {
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
                    out.push_str(&format!("(edrat-literal {} {})\n", lit, polarized_term));
                    literals_defined.insert(lit);
                }
            } else {
                panic!(
                    "We should have introduced the literal {} in the terms list",
                    lit
                );
            }
        }
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

        output.push_str(&format_function_declarations(&self.symbol_table));

        // Depending on the proof step, introduce new eDRAT literals
        for step in &self.proof_steps {
            let clause = &step.clause;
            let typ = &step.typ;
            match typ {
                ProofStepType::OriginalClause
                | ProofStepType::TheoryClause(..)
                | ProofStepType::Instantiation => {
                    self.introduce_literals(&mut literals_defined, clause, &mut output)
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
                    // Introduce the parent before declaring symbols used by the child.
                    self.introduce_literals(
                        &mut literals_defined,
                        std::slice::from_ref(parent_term),
                        &mut output,
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
                _ => {}
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::quantifiers::skolem::skolemize;
    use yaspar_ir::ast::{ACommand, Context, Typecheck};
    use yaspar_ir::untyped::UntypedAst;

    fn parse_assertion(script: &str) -> (Context, Term) {
        let mut context = Context::new();
        let commands = UntypedAst
            .parse_script_str(script)
            .unwrap()
            .type_check(&mut context)
            .unwrap();
        let assertion = commands
            .iter()
            .find_map(|command| match command.repr() {
                ACommand::Assert(term) => Some(term.clone()),
                _ => None,
            })
            .unwrap();
        (context, assertion)
    }

    #[test]
    fn orders_defined_functions_by_dependency() {
        let script = "\
(declare-fun base () Int)
(define-fun z ((x Int)) Int (+ x base))
(define-fun a ((x Int)) Int (z (z x)))
";
        let mut context = Context::new();
        UntypedAst
            .parse_script_str(script)
            .unwrap()
            .type_check(&mut context)
            .unwrap();

        let mut tracer = SMTProofTracer::new(
            context.expose_sorts().clone(),
            context.expose_symbol_table().clone(),
        );

        let proof = tracer.generate_edrat();
        let declaration = proof.find("(declare-fun base () Int)").unwrap();
        let dependency = proof.find("(define-fun z ").unwrap();
        let dependent = proof.find("(define-fun a ").unwrap();
        assert!(declaration < dependency);
        assert!(dependency < dependent);
    }

    #[test]
    fn introduces_skolem_parent_before_declaration_and_child_after() {
        let script = "(assert (exists ((x Int)) (> x 0)))";
        let (mut context, parent) = parse_assertion(script);
        let (child, skolem_vars) = skolemize(&parent, &mut context, true);
        let skolem_name = skolem_vars[0].0.to_string();

        let mut tracer = SMTProofTracer::new(
            context.expose_sorts().clone(),
            context.expose_symbol_table().clone(),
        );
        tracer.register_term(1, &parent, true);
        tracer.register_term(2, &child, true);
        tracer.push_step(
            &[-1, 2],
            ProofStepType::Skolemization {
                parent_term: 1,
                skolem_vars,
            },
        );

        let proof = tracer.generate_edrat();
        let parent_definition = proof.find("(edrat-literal 1 ").unwrap();
        let declaration = proof
            .find(&format!("(declare-skolem 1 0 {} Int)", skolem_name))
            .unwrap();
        let child_definition = proof.find("(edrat-literal 2 ").unwrap();
        let skolem_step = proof.find("s -1 2 0").unwrap();

        assert!(parent_definition < declaration);
        assert!(declaration < child_definition);
        assert!(child_definition < skolem_step);
        assert_eq!(proof.matches("(edrat-literal 1 ").count(), 1);
    }
}
