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
use std::io::{self, Write};
use std::ops::{Neg, Range};
use yaspar_ir::ast::{ATerm::*, FunctionMeta, Repr, Sig, Sort, SortDef, Str, SymbolQuote, Term};

/// Implementation of ProofTracer both SAT solver clauses and theory clauses
/// to generate an eDRAT proof.
pub struct SMTProofTracer {
    proof_steps: Vec<ProofStep>,
    terms_list: HashMap<i32, (u64, Term, bool)>,
    sorts: HashMap<Str, SortDef>,
    symbol_table: HashMap<Str, Vec<(Sig, FunctionMeta)>>,
    registered_clause_callbacks: HashMap<Vec<i32>, usize>,
    /// Number of clauses deleted by CaDiCaL (for stats)
    pub(crate) deleted_clauses: u64,
    /// CaDiCaL's LRAT information, which `write_edrat` uses to trim the proof to the clauses the
    /// refutation depends on. Only recorded after [`SMTProofTracer::track_core`].
    lrat: Option<Lrat>,
    /// Proof steps that justify a later step but never reach CaDiCaL, keyed by that later step's
    /// index. Trimming keeps them whenever it keeps the step.
    premises: HashMap<usize, Range<usize>>,
}

#[derive(Default)]
struct Lrat {
    /// The normalized clause behind each CaDiCaL clause id (original and derived).
    clause_by_id: HashMap<i64, Vec<i32>>,
    /// The antecedent clause ids of each clause CaDiCaL derived.
    antecedents: HashMap<i64, Vec<i64>>,
    /// The clause ids `conclude_unsat` reported.
    final_ids: Vec<i64>,
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

/// Collects the global symbols of `term`, visiting each shared subterm once, so it stays linear
/// in the term's DAG size. `seen` can be reused across terms.
fn collect_global_symbols(term: &Term, seen: &mut HashSet<u64>, symbols: &mut HashSet<Str>) {
    let mut stack = vec![term.clone()];
    while let Some(t) = stack.pop() {
        if !seen.insert(t.uid()) {
            continue;
        }
        if let Global(qid, ..) | App(qid, ..) = t.repr() {
            symbols.insert(qid.0.symbol.clone());
        }
        stack.extend(t.repr().sub_terms().cloned());
    }
}

/// Formats the declare-fun/define-fun commands of the symbol table. With `used`, only the
/// symbols in it are declared, plus the definitions those depend on.
fn format_function_declarations(
    symbol_table: &HashMap<Str, Vec<(Sig, FunctionMeta)>>,
    used: Option<&HashSet<Str>>,
) -> String {
    let mut symbols = symbol_table.keys().collect::<Vec<_>>();
    symbols.sort_by_key(|symbol| symbol.to_string());

    let is_definition = |symbol: &Str| {
        matches!(
            symbol_table[symbol].as_slice(),
            [(Sig::ParFunc(..), FunctionMeta::Defined(_))]
        )
    };
    let (mut definitions, declarations): (Vec<_>, Vec<_>) = symbols
        .into_iter()
        .partition(|symbol| is_definition(symbol));

    let dependencies = definitions
        .iter()
        .map(|symbol| {
            let symbol = *symbol;
            let [(_, FunctionMeta::Defined(meta))] = symbol_table[symbol].as_slice() else {
                unreachable!();
            };
            let mut dependencies = HashSet::new();
            collect_global_symbols(&meta.def.body, &mut HashSet::new(), &mut dependencies);
            (symbol.clone(), dependencies)
        })
        .collect::<HashMap<_, _>>();

    // With `used`, keep its symbols and, transitively, what the kept definitions mention
    let needed = used.map(|used| {
        let mut needed = used.clone();
        let mut stack: Vec<&Str> = used.iter().collect();
        while let Some(symbol) = stack.pop() {
            for dependency in dependencies.get(symbol).into_iter().flatten() {
                if needed.insert(dependency.clone()) {
                    stack.push(dependency);
                }
            }
        }
        needed
    });
    let is_needed = |symbol: &Str| needed.as_ref().is_none_or(|n| n.contains(symbol));

    let mut output = String::new();
    for symbol in declarations {
        if is_needed(symbol) {
            output.push_str(&format_function_declaration(symbol, &symbol_table[symbol]));
        }
    }
    definitions.retain(|symbol| is_needed(symbol));

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
            registered_clause_callbacks: HashMap::new(),
            deleted_clauses: 0,
            lrat: None,
            premises: HashMap::new(),
        }
    }

    /// Records CaDiCaL's clause ids and antecedents from now on, so that `write_edrat` can trim
    /// the proof to the clauses the refutation depends on. Call before solving; it needs the
    /// tracer to be connected with antecedents.
    pub fn track_core(&mut self) {
        self.lrat = Some(Lrat::default());
    }

    pub(crate) fn record_clause(&mut self, id: i64, clause: &[i32], antecedents: Option<&[i64]>) {
        if let Some(lrat) = &mut self.lrat {
            lrat.clause_by_id.insert(id, normalize_clause(clause));
            if let Some(a) = antecedents {
                lrat.antecedents.insert(id, a.to_vec());
            }
        }
    }

    pub(crate) fn record_conclusion(&mut self, clause_ids: &[i64]) {
        if let Some(lrat) = &mut self.lrat {
            lrat.final_ids = clause_ids.to_vec();
        }
    }

    ////////////////////////////////////////////////////////////////////////////

    pub fn push_step(&mut self, clause: &[i32], typ: ProofStepType) {
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
        if self.get_lit_info(literal).is_none() {
            self.terms_list
                .insert(literal, (term.uid(), term.clone(), polarity));
        }
    }

    /// Returns whether a term with the `literal` (or its negation) has been registered.
    pub fn is_lit_registered(&self, literal: i32) -> bool {
        self.get_lit_info(literal).is_some() || self.get_lit_info(-literal).is_some()
    }

    /// Reports the definitions of the literals in `clause` to `visit`.
    fn introduce_literals(
        &self,
        literals_defined: &mut HashSet<i32>,
        clause: &[i32],
        visit: &mut impl FnMut(ProofItem<'_>) -> io::Result<()>,
    ) -> io::Result<()> {
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

                if literals_defined.insert(lit) {
                    visit(ProofItem::Literal(lit, polarized_term))?;
                }
            } else {
                panic!(
                    "We should have introduced the literal {} in the terms list",
                    lit
                );
            }
        }
        Ok(())
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
            let first_premise = self.proof_steps.len();
            self.push_step(&child_imp, typ);
            self.add_theory_clause(&equiv_imp, Theory::Boolean);
            let premises = first_premise..self.proof_steps.len();
            self.add_sat_clause(&imp);
            // Only `imp` reaches CaDiCaL, so a trimmed proof must keep its premises with it
            if self.proof_steps.len() > premises.end {
                self.premises.insert(premises.end, premises);
            }

            // Delete any clauses mentioning the un-reduced child
            self.record_deletion(&child_imp);
            self.record_deletion(&equiv_imp);
        }
    }

    /// Marks the proof steps that a trimmed proof keeps: those whose clause is in the antecedent
    /// closure of the clauses `conclude_unsat` reported, the proof-only premises of those steps,
    /// and the final empty clause. Deletions are dropped, since every kept clause stays needed.
    ///
    /// Returns `None` when the recorded LRAT information cannot justify trimming (no core was
    /// tracked, or the closure reaches a clause id or content the tracer does not know); the
    /// caller then writes the whole proof.
    fn core_steps(&self) -> Option<Vec<bool>> {
        let lrat = self
            .lrat
            .as_ref()
            .filter(|lrat| !lrat.final_ids.is_empty())?;
        let mut core: HashSet<&[i32]> = HashSet::new();
        let mut seen = HashSet::new();
        let mut stack = lrat.final_ids.clone();
        while let Some(id) = stack.pop() {
            if !seen.insert(id) {
                continue;
            }
            let clause = lrat.clause_by_id.get(&id)?;
            core.insert(clause.as_slice());
            if let Some(antecedents) = lrat.antecedents.get(&id) {
                // A derived clause without antecedents cannot be justified from the core alone
                if antecedents.is_empty() && !clause.is_empty() {
                    return None;
                }
                stack.extend(antecedents.iter().map(|a| a.abs()));
            }
        }

        let mut keep = vec![false; self.proof_steps.len()];
        let mut found: HashSet<&[i32]> = HashSet::new();
        for (i, step) in self.proof_steps.iter().enumerate() {
            match step.typ {
                ProofStepType::Deletion => {}
                ProofStepType::SATClause if step.clause.is_empty() => {
                    keep[i] = true;
                    break;
                }
                _ => {
                    if let Some(c) = core.get(normalize_clause(&step.clause).as_slice()) {
                        keep[i] = true;
                        found.insert(c);
                    }
                }
            }
        }
        if found.len() + usize::from(core.contains(&[][..])) < core.len() {
            debug_println!(2, 0, "eDRAT: a core clause has no proof step; not trimming");
            return None;
        }
        // Premises are never derived steps themselves, so one pass closes over them
        for (&step, premises) in &self.premises {
            if keep[step] {
                keep[premises.clone()].fill(true);
            }
        }
        Some(keep)
    }

    /// Walks the proof in order and reports, for every step that is written, the literal
    /// definitions and Skolem declarations it needs and then the step itself. `keep` restricts
    /// the walk to the marked steps. Stops after the empty clause.
    fn visit_proof(
        &self,
        keep: Option<&[bool]>,
        mut visit: impl FnMut(ProofItem<'_>) -> io::Result<()>,
    ) -> io::Result<()> {
        let mut literals_defined: HashSet<i32> = HashSet::new();
        for (i, step) in self.proof_steps.iter().enumerate() {
            if keep.is_some_and(|k| !k[i]) {
                continue;
            }
            let clause = &step.clause;
            let typ = &step.typ;
            match typ {
                ProofStepType::OriginalClause
                | ProofStepType::TheoryClause(..)
                | ProofStepType::Instantiation => {
                    self.introduce_literals(&mut literals_defined, clause, &mut visit)?
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
                        &mut visit,
                    )?;
                    for (i, var) in skolem_vars.iter().enumerate() {
                        // CC TODO think about negated parent term, if (negated forall)
                        visit(ProofItem::Skolem(*parent_term, i, var))?;
                    }
                    self.introduce_literals(&mut literals_defined, clause, &mut visit)?;
                }
                _ => {}
            }

            visit(ProofItem::Step(step))?;

            // Stop adding proof steps to the output once the empty clause is derived
            if matches!(typ, ProofStepType::SATClause) && clause.is_empty() {
                break;
            }
        }
        Ok(())
    }

    /// Writes the eDRAT proof to `out`, streaming it rather than building it in memory.
    ///
    /// With `trim`, and when the solver tracked a core (see [`SMTProofTracer::track_core`]), only
    /// the steps the refutation depends on are written, together with the literals and the
    /// function declarations they use. Otherwise every step is written.
    pub fn write_edrat(&self, out: &mut impl Write, trim: bool) -> io::Result<()> {
        let keep = if trim { self.core_steps() } else { None };

        // A trimmed proof only declares the functions its literal terms mention
        let used_symbols = keep.as_deref().map(|keep| {
            let mut symbols = HashSet::new();
            let mut seen = HashSet::new();
            let _ = self.visit_proof(Some(keep), |item| {
                if let ProofItem::Literal(_, term) = item {
                    collect_global_symbols(&term, &mut seen, &mut symbols);
                }
                Ok(())
            });
            symbols
        });

        // emit the sorts, datatypes, and the symbol table
        for (sort, sort_def) in &self.sorts {
            out.write_all(format_sort_declaration(sort, sort_def).as_bytes())?;
        }
        out.write_all(format_datatype_declaration(&self.sorts).as_bytes())?;
        out.write_all(
            format_function_declarations(&self.symbol_table, used_symbols.as_ref()).as_bytes(),
        )?;

        self.visit_proof(keep.as_deref(), |item| match item {
            ProofItem::Literal(lit, term) => writeln!(out, "(edrat-literal {lit} {term})"),
            ProofItem::Skolem(parent, i, var) => {
                writeln!(out, "(declare-skolem {} {} {} {})", parent, i, var.0, var.1)
            }
            ProofItem::Step(step) => step.write_line_to(out),
        })
    }

    /// Generates the whole (untrimmed) eDRAT proof as a string.
    #[cfg(test)]
    pub(crate) fn generate_edrat(&self) -> String {
        let mut out = Vec::new();
        self.write_edrat(&mut out, false)
            .expect("writing to a Vec cannot fail");
        String::from_utf8(out).expect("eDRAT proofs are UTF-8")
    }
}

/// One line-producing element of an eDRAT proof, as reported by `SMTProofTracer::visit_proof`.
enum ProofItem<'a> {
    /// `(edrat-literal <lit> <term>)`
    Literal(i32, Term),
    /// `(declare-skolem <parent> <index> <name> <sort>)`
    Skolem(i32, usize, &'a (Str, Sort)),
    /// A clause line
    Step(&'a ProofStep),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::quantifiers::skolem::skolemize;
    use cadical_sys::ProofTracer;
    use yaspar_ir::ast::{ACommand, Context, Typecheck};
    use yaspar_ir::untyped::UntypedAst;

    /// Parses `script` and returns its context and its assertions, in order.
    fn parse_assertions(script: &str) -> (Context, Vec<Term>) {
        let mut context = Context::new();
        let commands = UntypedAst
            .parse_script_str(script)
            .unwrap()
            .type_check(&mut context)
            .unwrap();
        let assertions = commands
            .iter()
            .filter_map(|command| match command.repr() {
                ACommand::Assert(term) => Some(term.clone()),
                _ => None,
            })
            .collect();
        (context, assertions)
    }

    /// A tracer over the sorts and symbols of `context`.
    fn tracer_for(context: &Context) -> SMTProofTracer {
        SMTProofTracer::new(
            context
                .expose_sorts()
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect(),
            context
                .expose_symbol_table()
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect(),
        )
    }

    /// A tracer that tracks a core, with the Boolean constants `p`, `q`, `r` as literals 1, 2, 3.
    fn pqr_tracer() -> (SMTProofTracer, Vec<Term>) {
        let (context, terms) = parse_assertions(
            "(declare-const p Bool) (declare-const q Bool) (declare-const r Bool)
             (assert p) (assert q) (assert r)",
        );
        let mut tracer = tracer_for(&context);
        for (i, term) in terms.iter().enumerate() {
            tracer.register_term(i as i32 + 1, term, true);
        }
        tracer.track_core();
        (tracer, terms)
    }

    /// Records `clause` the way `add_clause_to_proof_and_solver` does, then reports it to the
    /// tracer as CaDiCaL would, under clause id `id`.
    fn add_input_clause(tracer: &mut SMTProofTracer, id: i64, clause: &[i32]) {
        tracer.add_original_clause(clause);
        tracer.register_clause_for_cadical_callback(clause);
        ProofTracer::add_original_clause(tracer, id, false, clause, false);
    }

    fn trimmed(tracer: &SMTProofTracer) -> String {
        let mut out = Vec::new();
        tracer.write_edrat(&mut out, true).unwrap();
        String::from_utf8(out).unwrap()
    }

    #[test]
    fn trims_proof_to_lrat_core() {
        let (mut tracer, _) = pqr_tracer();
        add_input_clause(&mut tracer, 1, &[1]);
        add_input_clause(&mut tracer, 2, &[-1, 2]);
        add_input_clause(&mut tracer, 3, &[3]);
        add_input_clause(&mut tracer, 4, &[-2]);
        ProofTracer::add_derived_clause(&mut tracer, 5, false, 0, &[], &[1, 2, 4]);
        ProofTracer::delete_clause(&mut tracer, 3, false, &[3]);
        ProofTracer::conclude_unsat(&mut tracer, 0, &[5]);

        let full = tracer.generate_edrat();
        assert!(full.contains("a 3 0\n") && full.contains("(declare-fun r () Bool)"));

        let proof = trimmed(&tracer);
        assert_eq!(
            proof,
            "(declare-fun p () Bool)\n(declare-fun q () Bool)\n\
             (edrat-literal 1 p)\na 1 0\n(edrat-literal 2 q)\na -1 2 0\na -2 0\n0\n"
        );
    }

    #[test]
    fn trimming_keeps_premises_of_derived_instances() {
        let (mut tracer, terms) = pqr_tracer();
        // 1 => 2 is an instance, 2 <=> 3 its reduction; only 1 => 3 reaches CaDiCaL
        tracer.push_skolem_or_instantiation_derivation(
            1,
            2,
            &terms[1],
            3,
            &terms[2],
            ProofStepType::Instantiation,
        );
        tracer.register_clause_for_cadical_callback(&[-1, 3]);
        ProofTracer::add_original_clause(&mut tracer, 1, false, &[-1, 3], false);
        add_input_clause(&mut tracer, 2, &[1]);
        add_input_clause(&mut tracer, 3, &[-3]);
        ProofTracer::add_derived_clause(&mut tracer, 4, false, 0, &[], &[1, 2, 3]);
        ProofTracer::conclude_unsat(&mut tracer, 0, &[4]);

        let proof = trimmed(&tracer);
        for line in [
            "q -1 2 0\n",
            "t b -2 3 0\n",
            "\n-1 3 0\n",
            "a 1 0\n",
            "a -3 0\n",
        ] {
            assert!(proof.contains(line), "missing {line:?} in\n{proof}");
        }
        assert!(!proof.contains("\nd "), "deletions are dropped:\n{proof}");
        assert!(proof.ends_with("\n0\n"));
    }

    #[test]
    fn trimming_falls_back_to_full_proof_without_core() {
        let (mut tracer, _) = pqr_tracer();
        add_input_clause(&mut tracer, 1, &[1]);
        // no conclude_unsat: nothing to trim against
        assert_eq!(trimmed(&tracer), tracer.generate_edrat());
    }

    #[test]
    fn orders_defined_functions_by_dependency() {
        let script = "\
(declare-fun base () Int)
(define-fun z ((x Int)) Int (+ x base))
(define-fun a ((x Int)) Int (z (z x)))
";
        let (context, _) = parse_assertions(script);
        let proof = tracer_for(&context).generate_edrat();
        let declaration = proof.find("(declare-fun base () Int)").unwrap();
        let dependency = proof.find("(define-fun z ").unwrap();
        let dependent = proof.find("(define-fun a ").unwrap();
        assert!(declaration < dependency);
        assert!(dependency < dependent);
    }

    #[test]
    fn introduces_skolem_parent_before_declaration_and_child_after() {
        let script = "(assert (exists ((x Int)) (> x 0)))";
        let (mut context, assertions) = parse_assertions(script);
        let parent = &assertions[0];
        let (child, skolem_vars) = skolemize(parent, &mut context, true);
        let skolem_name = skolem_vars[0].0.to_string();

        let mut tracer = tracer_for(&context);
        tracer.register_term(1, parent, true);
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
