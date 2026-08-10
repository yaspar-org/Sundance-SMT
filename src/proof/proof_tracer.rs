// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Keeps track of the eDRAT proof
//!
use crate::debug_println;
use crate::proof::{ProofStep, ProofStepType, Theory};
use core::panic;
use std::cmp::Eq;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::Hash;
use std::ops::Neg;
use yaspar_ir::ast::{
    ATerm::*, Attribute, DatatypeFunction, FunctionMeta, QualifiedIdentifier, Repr, Sig, Sort,
    SortDef, Str, SymbolQuote, Term,
};

/// Implementation of ProofTracer both SAT solver clauses and theory clauses
/// to generate an eDRAT proof.
pub struct SMTProofTracer {
    proof_steps: Vec<ProofStep>,
    terms_list: HashMap<i32, (u64, Term, bool)>,
    sorts: HashMap<Str, SortDef>,
    symbol_table: HashMap<Str, Vec<(Sig, FunctionMeta)>>,
    instantiations_for_smt2: Vec<(Term, Vec<(Term, bool)>)>,
    expected_original_clauses: HashMap<Vec<i32>, usize>,
    /// Number of clauses deleted by CaDiCaL (for stats)
    pub(crate) deleted_clauses: u64,
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

fn normalized_clause(clause: &[i32]) -> Vec<i32> {
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
fn format_function_declaration(
    symbol_name: &Str,
    sigs: &[(Sig, FunctionMeta)],
    symbol_table: &HashMap<Str, Vec<(Sig, FunctionMeta)>>,
) -> String {
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
                SmtTerm {
                    term: &meta.def.body,
                    symbol_table,
                }
            )
        }
        _ => String::new(),
    }
}

fn collect_global_symbols(term: &Term, symbols: &mut HashSet<Str>) {
    match term.repr() {
        Constant(..) | Local(..) => {}
        Global(qid, ..) => {
            symbols.insert(qid.0.symbol.clone());
        }
        App(qid, terms, ..) => {
            symbols.insert(qid.0.symbol.clone());
            for term in terms {
                collect_global_symbols(term, symbols);
            }
        }
        Let(bindings, body) => {
            for binding in bindings {
                collect_global_symbols(&binding.2, symbols);
            }
            collect_global_symbols(body, symbols);
        }
        Exists(_, body) | Forall(_, body) | Not(body) => {
            collect_global_symbols(body, symbols);
        }
        Matching(scrutinee, arms) => {
            collect_global_symbols(scrutinee, symbols);
            for arm in arms {
                collect_global_symbols(&arm.body, symbols);
            }
        }
        Annotated(term, attributes) => {
            collect_global_symbols(term, symbols);
            for attribute in attributes {
                if let Attribute::Pattern(terms) = attribute {
                    for term in terms {
                        collect_global_symbols(term, symbols);
                    }
                }
            }
        }
        Eq(left, right) => {
            collect_global_symbols(left, symbols);
            collect_global_symbols(right, symbols);
        }
        Distinct(terms) | And(terms) | Or(terms) | Xor(terms) => {
            for term in terms {
                collect_global_symbols(term, symbols);
            }
        }
        Implies(premises, conclusion) => {
            for premise in premises {
                collect_global_symbols(premise, symbols);
            }
            collect_global_symbols(conclusion, symbols);
        }
        Ite(condition, then_term, else_term) => {
            collect_global_symbols(condition, symbols);
            collect_global_symbols(then_term, symbols);
            collect_global_symbols(else_term, symbols);
        }
    }
}

fn format_function_declarations(symbol_table: &HashMap<Str, Vec<(Sig, FunctionMeta)>>) -> String {
    let mut symbols = symbol_table.keys().collect::<Vec<_>>();
    symbols.sort_by_key(|symbol| symbol.to_string());

    let mut output = String::new();
    let mut definitions = Vec::new();
    for symbol in symbols {
        if matches!(
            symbol_table.get(symbol).map(Vec::as_slice),
            Some([(Sig::ParFunc(..), FunctionMeta::Defined(_))])
        ) {
            definitions.push(symbol);
        } else {
            output.push_str(&format_function_declaration(
                symbol,
                &symbol_table[symbol],
                symbol_table,
            ));
        }
    }

    let defined_symbols = definitions
        .iter()
        .map(|symbol| (*symbol).clone())
        .collect::<HashSet<_>>();
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
                !defined_symbols.contains(dependency) || emitted.contains(dependency)
            })
        }) else {
            panic!("We do not handle recursive function definitions!");
        };
        let symbol = definitions.remove(index);
        output.push_str(&format_function_declaration(
            symbol,
            &symbol_table[symbol],
            symbol_table,
        ));
        emitted.insert(symbol.clone());
    }

    output
}

// Yaspar's generic Display omits inferred sort ascriptions. Parametric
// datatype constructors need those ascriptions to remain valid SMT-LIB.
struct SmtTerm<'a> {
    term: &'a Term,
    symbol_table: &'a HashMap<Str, Vec<(Sig, FunctionMeta)>>,
}

impl SmtTerm<'_> {
    fn is_parametric_constructor(&self, qid: &QualifiedIdentifier) -> bool {
        self.symbol_table.get(&qid.0.symbol).is_some_and(|sigs| {
            sigs.iter().any(|(sig, meta)| {
                matches!(sig, Sig::ParFunc(_, params, _, _) if !params.is_empty())
                    && matches!(
                        meta,
                        FunctionMeta::Datatype {
                            kind: DatatypeFunction::Constructor,
                            ..
                        }
                    )
            })
        })
    }

    fn fmt_identifier(
        &self,
        f: &mut fmt::Formatter<'_>,
        qid: &QualifiedIdentifier,
        inferred_sort: Option<&Sort>,
    ) -> fmt::Result {
        if qid.1.is_none()
            && self.is_parametric_constructor(qid)
            && let Some(sort) = inferred_sort
        {
            return write!(f, "(as {} {})", qid.0, sort);
        }
        write!(f, "{qid}")
    }

    fn fmt_terms(
        &self,
        f: &mut fmt::Formatter<'_>,
        terms: &[Term],
        separator: &str,
    ) -> fmt::Result {
        for (index, term) in terms.iter().enumerate() {
            if index > 0 {
                f.write_str(separator)?;
            }
            write!(
                f,
                "{}",
                SmtTerm {
                    term,
                    symbol_table: self.symbol_table,
                }
            )?;
        }
        Ok(())
    }

    fn fmt_application(
        &self,
        f: &mut fmt::Formatter<'_>,
        operator: &str,
        terms: &[Term],
    ) -> fmt::Result {
        write!(f, "({operator}")?;
        if !terms.is_empty() {
            f.write_str(" ")?;
            self.fmt_terms(f, terms, " ")?;
        }
        f.write_str(")")
    }
}

impl fmt::Display for SmtTerm<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.term.repr() {
            Constant(constant, _) => write!(f, "{constant}"),
            Global(qid, sort) => self.fmt_identifier(f, qid, sort.as_ref()),
            Local(local) => write!(f, "{}", local.symbol.sym_quote()),
            App(qid, terms, sort) => {
                f.write_str("(")?;
                self.fmt_identifier(f, qid, sort.as_ref())?;
                if !terms.is_empty() {
                    f.write_str(" ")?;
                    self.fmt_terms(f, terms, " ")?;
                }
                f.write_str(")")
            }
            Let(bindings, body) => {
                f.write_str("(let (")?;
                for (index, binding) in bindings.iter().enumerate() {
                    if index > 0 {
                        f.write_str(" ")?;
                    }
                    write!(
                        f,
                        "({} {})",
                        binding.0.sym_quote(),
                        SmtTerm {
                            term: &binding.2,
                            symbol_table: self.symbol_table,
                        }
                    )?;
                }
                write!(
                    f,
                    ") {})",
                    SmtTerm {
                        term: body,
                        symbol_table: self.symbol_table,
                    }
                )
            }
            Exists(bindings, body) | Forall(bindings, body) => {
                let binder = if matches!(self.term.repr(), Exists(..)) {
                    "exists"
                } else {
                    "forall"
                };
                write!(f, "({binder} (")?;
                for (index, binding) in bindings.iter().enumerate() {
                    if index > 0 {
                        f.write_str(" ")?;
                    }
                    write!(f, "{binding}")?;
                }
                write!(
                    f,
                    ") {})",
                    SmtTerm {
                        term: body,
                        symbol_table: self.symbol_table,
                    }
                )
            }
            Matching(scrutinee, arms) => {
                write!(
                    f,
                    "(match {} (",
                    SmtTerm {
                        term: scrutinee,
                        symbol_table: self.symbol_table,
                    }
                )?;
                for (index, arm) in arms.iter().enumerate() {
                    if index > 0 {
                        f.write_str(" ")?;
                    }
                    write!(
                        f,
                        "({} {})",
                        arm.pattern,
                        SmtTerm {
                            term: &arm.body,
                            symbol_table: self.symbol_table,
                        }
                    )?;
                }
                f.write_str("))")
            }
            Annotated(term, attributes) => {
                write!(
                    f,
                    "(! {}",
                    SmtTerm {
                        term,
                        symbol_table: self.symbol_table,
                    }
                )?;
                for attribute in attributes {
                    f.write_str(" ")?;
                    match attribute {
                        Attribute::Pattern(terms) => {
                            f.write_str(":pattern (")?;
                            self.fmt_terms(f, terms, " ")?;
                            f.write_str(")")?;
                        }
                        _ => write!(f, "{attribute}")?,
                    }
                }
                f.write_str(")")
            }
            Eq(left, right) => self.fmt_application(f, "=", &[left.clone(), right.clone()]),
            Distinct(terms) => self.fmt_application(f, "distinct", terms),
            And(terms) => self.fmt_application(f, "and", terms),
            Or(terms) => self.fmt_application(f, "or", terms),
            Xor(terms) => self.fmt_application(f, "xor", terms),
            Implies(premises, conclusion) => {
                f.write_str("(=> ")?;
                self.fmt_terms(f, premises, " ")?;
                write!(
                    f,
                    " {})",
                    SmtTerm {
                        term: conclusion,
                        symbol_table: self.symbol_table,
                    }
                )
            }
            Not(term) => self.fmt_application(f, "not", std::slice::from_ref(term)),
            Ite(condition, then_term, else_term) => self.fmt_application(
                f,
                "ite",
                &[condition.clone(), then_term.clone(), else_term.clone()],
            ),
        }
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
            expected_original_clauses: HashMap::new(),
            deleted_clauses: 0,
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

    pub fn expect_original_clause_callback(&mut self, clause: &[i32]) {
        let clause = normalized_clause(clause);
        *self.expected_original_clauses.entry(clause).or_default() += 1;
    }

    pub fn consume_expected_original_clause(&mut self, clause: &[i32]) -> bool {
        let clause = normalized_clause(clause);
        match self.expected_original_clauses.get_mut(&clause) {
            Some(count) if *count > 1 => {
                *count -= 1;
                true
            }
            Some(_) => {
                self.expected_original_clauses.remove(&clause);
                true
            }
            None => false,
        }
    }

    pub fn cancel_expected_original_clause_callback(&mut self, clause: &[i32]) {
        self.consume_expected_original_clause(clause);
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

    /// Pushes literal definitions
    /// If one of the literals is not in terms list, then this clause is useless and we return false
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
                    temp_output.push_str(&format!(
                        "(edrat-literal {} {})\n",
                        lit,
                        SmtTerm {
                            term: &polarized_term,
                            symbol_table: &self.symbol_table,
                        }
                    ));
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
                    // The declaration refers to the parent eDRAT literal, while
                    // the child literal may refer to the fresh Skolem symbols.
                    self.introduce_literals(
                        &mut literals_defined,
                        &vec![*parent_term],
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

    #[test]
    fn ascribes_polymorphic_datatype_constructors() {
        let script = "\
(declare-sort Val 0)
(declare-datatypes ((Option 1)) ((par (T) ((None) (Some (value T))))))
(define-fun empty () (Option Val) (as None (Option Val)))
(assert ((_ is None) (as None (Option Val))))
";
        let mut context = Context::new();
        let commands = UntypedAst
            .parse_script_str(script)
            .unwrap()
            .type_check(&mut context)
            .unwrap();
        let term = commands
            .iter()
            .find_map(|command| match command.repr() {
                ACommand::Assert(term) => Some(term.clone()),
                _ => None,
            })
            .unwrap();

        let mut tracer = SMTProofTracer::new(
            context.expose_sorts().clone(),
            context.expose_symbol_table().clone(),
        );
        tracer.register_term(1, &term, true);
        tracer.add_original_clause(&vec![1]);

        let proof = tracer.generate_edrat();
        assert!(proof.contains("(define-fun empty () (Option Val) (as None (Option Val)))"));
        assert!(proof.contains("((_ is None) (as None (Option Val)))"));
    }

    #[test]
    fn orders_defined_functions_by_dependency() {
        let script = "\
(declare-fun a () Int)
(define-fun f ((x Int)) Int (+ x a))
(define-fun g ((x Int)) Int (f (f x)))
(assert (= (g 0) 2))
";
        let mut context = Context::new();
        let commands = UntypedAst
            .parse_script_str(script)
            .unwrap()
            .type_check(&mut context)
            .unwrap();
        let term = commands
            .iter()
            .find_map(|command| match command.repr() {
                ACommand::Assert(term) => Some(term.clone()),
                _ => None,
            })
            .unwrap();

        let mut tracer = SMTProofTracer::new(
            context.expose_sorts().clone(),
            context.expose_symbol_table().clone(),
        );
        tracer.register_term(1, &term, true);
        tracer.add_original_clause(&vec![1]);

        let proof = tracer.generate_edrat();
        let declaration = proof.find("(declare-fun a () Int)").unwrap();
        let f_definition = proof.find("(define-fun f ").unwrap();
        let g_definition = proof.find("(define-fun g ").unwrap();
        assert!(declaration < f_definition);
        assert!(f_definition < g_definition);
    }

    #[test]
    fn introduces_skolem_parent_before_declaration_and_child_after() {
        let script = "(assert (exists ((x Int)) (> x 0)))";
        let mut context = Context::new();
        let commands = UntypedAst
            .parse_script_str(script)
            .unwrap()
            .type_check(&mut context)
            .unwrap();
        let parent = commands
            .iter()
            .find_map(|command| match command.repr() {
                ACommand::Assert(term) => Some(term.clone()),
                _ => None,
            })
            .unwrap();
        let (child, skolem_vars) = skolemize(&parent, &mut context, true);
        let skolem_name = skolem_vars[0].0.to_string();

        let mut tracer = SMTProofTracer::new(
            context.expose_sorts().clone(),
            context.expose_symbol_table().clone(),
        );
        tracer.register_term(1, &parent, true);
        tracer.register_term(2, &child, true);
        tracer.push_step(
            &vec![-1, 2],
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
