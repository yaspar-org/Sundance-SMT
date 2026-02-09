// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Keeps track of the eDRAT proof
//!
use cadical_sys::ProofTracer;
use core::panic;
use std::collections::{HashMap, HashSet};
use yaspar_ir::ast::{
    ATerm::*, Context, FunctionMeta, ObjectAllocatorExt, Repr, Sig, Sort, SortDef, Str, Term,
};

/// Implementation of ProofTracer both SAT solver clauses and theory clauses
/// to generate an eDRAT proof.
pub struct SMTProofTracker {
    proof_steps: Vec<ProofStepData>,
    pub terms_list: HashMap<i32, (u64, Term, bool)>,
    sorts: HashMap<Str, SortDef>,
    symbol_table: HashMap<Str, Vec<(Sig, FunctionMeta)>>,
    quantifier_constants_defined: HashSet<u64>, // Track defined quantifier constants
    literals_defined: HashSet<u64>,
    instantiations_for_smt2: Vec<(Term, Vec<(Term, bool)>)>,
    pub finished_original_clauses: bool,
    skolemizations: HashSet<Vec<i32>>, // super ugly way to do this, (todo: get rid of add_original_clause clauses and everything has a specific purpose)
}

// taking out of hash map so I don't have to remove them
fn get_lit_info(
    terms_list: &HashMap<i32, (u64, Term, bool)>,
    lit: i32,
) -> Option<(i32, u64, Term, bool)> {
    if let Some((id, term, polarity)) = terms_list.get(&lit) {
        // todo: if we only check one time, then we can just .remove(&lit) here
        Some((lit, *id, term.clone(), *polarity))
    } else if let Some((id, term, polarity)) = terms_list.get(&-lit) {
        // todo: if we only check one time, then we can just .remove(&-lit) here
        Some((-lit, *id, term.clone(), *polarity))
    } else {
        None
    }
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

/// Represents a single step in the proof
#[derive(Debug, Clone)]
pub enum ProofStepData {
    /// Original clause from the input formula
    OriginalClause { clause: Vec<i32> },
    /// Clause learned by the SAT solver
    SATClause { clause: Vec<i32> },
    /// Clause learned by a theory solver
    TheoryClause { clause: Vec<i32> },
    /// Clause learned by quantifier instantiation
    Skolemization {
        clause: Vec<i32>,
        skolem_vars: Option<Vec<(Str, Sort)>>,
    },
    // InstantiationClause {
    //     quantifier: Term,
    //     other_lits: Vec<(Term, bool)>,
    //     clause: Vec<i32>,
    //     // skolemized: bool,
    // },
    /// Clause deletion
    Deletion { id: u64 },
}

/// Format a sort definition as a declare-sort command
fn format_sort_declaration(sort_name: &Str, sort_def: &SortDef) -> String {
    // Skip default sorts that are predefined in SMT-LIB
    let default_sorts = [
        "Bool",
        "Int",
        "Real",
        "String",
        "Reglan",
        "Float128",
        "Float64",
        "Float32",
        "Float16",
        "Float8",
        "Float4",
        "Float2",
        "Float1",
        "RoundingMode",
        "Array",
    ];
    if default_sorts.contains(&sort_name.as_str()) {
        return String::new();
    }

    match sort_def {
        SortDef::Opaque(arity) => {
            format!("(declare-sort {} {})\n", sort_name, arity)
        }
        SortDef::Transparent { params, sort } => {
            if params.is_empty() {
                format!("(define-sort {} {})\n", sort_name, sort)
            } else {
                let params_str = params
                    .iter()
                    .map(|p| p.to_string())
                    .collect::<Vec<_>>()
                    .join(" ");
                format!("(define-sort {} ({}) {})\n", sort_name, params_str, sort)
            }
        }
        SortDef::Datatype(..) => {
            // datatypes handled by `format_datatype_declaration`
            String::new()
        }
    }
}

/// Format a sort definition as a declare-sort command
fn format_datatype_declaration(sorts: &HashMap<Str, SortDef>) -> (String, HashSet<&Str>) {
    let mut sort_str = vec![];
    let mut ctor_strs = vec![];
    let mut datatype_funs = HashSet::new();
    for (sort_name, sort_def) in sorts {
        match sort_def {
            SortDef::Opaque(..) | SortDef::Transparent { .. } => {}
            SortDef::Datatype(data) => {
                sort_str.push(format!("({} 0)", sort_name));

                let mut ctors_list = vec![];
                for ctor in &data.constructors {
                    let ctor_str = ctor.to_string();
                    datatype_funs.insert(&ctor.ctor);
                    for sel in &ctor.args {
                        datatype_funs.insert(&sel.0);
                    }

                    ctors_list.push(ctor_str);
                }

                ctor_strs.push(format!(
                    "({})",
                    &data
                        .constructors
                        .iter()
                        .map(|c| c.to_string())
                        .collect::<Vec<_>>()
                        .join(" ")
                ));
                // TODO: support datatypes in proof
                // assert!(data.params.len() == 0); // do not support polymorphic datatypes
                // let mut ctors_str = vec![];
                // for ctor in &data.constructors {
                //     ctors_str.push(ctor.to_string());
                // }
                // let ctors_str = ctors_str.join(" ");
                // format!("(declare-datatypes (({} 0)) ({}))\n", sort_name, ctors_str)
            }
        }
    }

    if sort_str.is_empty() {
        (String::new(), datatype_funs)
    } else {
        (
            format!(
                "(declare-datatypes ({}) ({}))\n",
                sort_str.join(" "),
                ctor_strs.join(" ")
            ),
            datatype_funs,
        )
    }
}

/// Format a function signature as a declare-fun command
fn format_function_declaration(symbol_name: &Str, sigs: &[(Sig, FunctionMeta)]) -> String {
    // Skip default functions that are predefined in SMT-LIB theories
    let default_functions = [
        // TODO: there's gotta be a cleaner way to just avoid this
        "=",
        "distinct",
        "ite",
        "and",
        "or",
        "not",
        "=>",
        "xor",
        "+",
        "-",
        "*",
        "/",
        "div",
        "mod",
        "abs",
        "<",
        "<=",
        ">",
        ">=",
        "char",
        // "str.++", "str.len", "str.<", "str.to_re", "str.in_re",
        // "re.none", "re.all", "re.allchar", "re.++", "re.union", "re.inter", "re.*",
        "select",
        "store",
        "RTP",
        "RNA",
        "roundTowardZero",
        "roundTowardPositive",
        "roundTowardNegative",
        "roundNearestTiesToEven",
        "roundNearestTiesToAway",
        "to_real",
        "is_int",
        "RNE",
        "RTZ",
        "str_from_int",
        "to_int",
        "RTN",
    ];

    let symbol_as_str = symbol_name.as_str();
    if default_functions.contains(&symbol_as_str) {
        return String::new();
    }

    if symbol_as_str.starts_with("re.") || symbol_as_str.starts_with("str.") {
        return String::new();
    }

    if symbol_as_str == "is" {
        return String::new();
    }

    assert_eq!(
        sigs.len(),
        1,
        "We only support one signature per symbol: {:?}",
        symbol_name
    );
    let sig = &sigs[0].0;

    match sig {
        Sig::ParFunc(_, sort_vars, input_sorts, output_sort) => {
            if sort_vars.is_empty() {
                // Non-polymorphic function
                if symbol_name.starts_with("is-") {
                    return String::new();
                }
                let input_sorts_str = input_sorts
                    .iter()
                    .map(|s| s.to_string())
                    .collect::<Vec<_>>()
                    .join(" ");
                format!(
                    "(declare-fun {} ({}) {})\n",
                    symbol_name, input_sorts_str, output_sort
                )
            } else {
                // Polymorphic function - we'll skip these for now as they're more complex
                // and typically not needed in basic eDRAT proofs
                panic!("Polymorphic functions are not supported");
            }
        }
        Sig::VarLenFunc(input_sort, min_args, output_sort) => {
            // For variable length functions, we'll declare them with the minimum number of arguments
            let input_sorts_str = (0..*min_args)
                .map(|_| input_sort.to_string())
                .collect::<Vec<_>>()
                .join(" ");
            format!(
                "(declare-fun {} ({}) {})\n",
                symbol_name, input_sorts_str, output_sort
            )
        }
        // TODO: look at the rest of the cases (bitvector stuff)
        _ => String::new(),
    }
}

fn replace_quantifier_constants(
    term: &Term,
    context: &mut Context,
    quantifier_constants_defined: &mut HashSet<u64>,
    output: &mut String,
) -> Term {
    // println!("We have term {} with uid {}", term , term.uid());
    let return_term = context.simple_symbol(format!("aux!{}", term.uid()).as_str());
    if quantifier_constants_defined.contains(&term.uid()) {
        return return_term;
    }
    output.push_str(&format!("(define-let {} {})\n", return_term, term));
    quantifier_constants_defined.insert(term.uid());
    return_term
}

impl SMTProofTracker {
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
            quantifier_constants_defined: HashSet::new(),
            literals_defined: HashSet::new(),
            instantiations_for_smt2: Vec::new(),
            finished_original_clauses: false,
            skolemizations: HashSet::new(),
        }
    }

    /// Add a skolemization clause to the proof
    /// The caller must provide a closure to map each literal to (uid, Term)
    pub fn add_skolem_clause(&mut self, clause: Vec<i32>, skolem_vars: Option<Vec<(Str, Sort)>>) {
        let mut c = clause.clone();
        self.proof_steps.push(ProofStepData::Skolemization {
            clause,
            skolem_vars,
        });
        c.reverse();
        self.skolemizations.insert(c);
    }

    /// Pushes literal definitions
    /// If one of the literals is not in terms list, then this clause is useless and we return false
    fn introduce_literals(&mut self, clause: &Vec<i32>, out: &mut String) {
        let mut temp_output = String::new();
        for &lit in clause {
            debug_println!(12, 2, "Introducing the literal {}", lit);
            if let Some((lit, id, term, polarity)) = get_lit_info(&self.terms_list, lit) {
                debug_println!(9, 2, "The lit exists with term {}", term);
                let lit = lit.abs();
                let mut context = Context::new();
                let polarized_term = polarize_term(&term, polarity);

                debug_println!(
                    19,
                    2,
                    "we go from term {} to polarized_term {}",
                    term,
                    polarized_term
                );

                let output = replace_quantifier_constants(
                    &polarized_term,
                    &mut context,
                    &mut self.quantifier_constants_defined,
                    &mut temp_output,
                );
                if !self.literals_defined.contains(&id) {
                    temp_output.push_str(&format!("(define-literal {} {})\n", lit, output));
                    self.literals_defined.insert(id);
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

    /// Generate eDRAT proof as a string
    pub fn generate_edrat(&mut self) -> String {
        let mut output = String::new();
        self.instantiations_for_smt2.clear(); // Clear previous instantiations

        // emit the sorts and symbol table
        for (sort, sort_def) in &self.sorts {
            output.push_str(&format_sort_declaration(sort, sort_def));
        }

        let (datatype_string, datatype_funs) = &format_datatype_declaration(&self.sorts);

        output.push_str(datatype_string);

        // emit the symbol table
        for (symbol, sigs) in &self.symbol_table {
            // skip the ctors/selectors that are already part of datatype decl
            if datatype_funs.contains(symbol) {
                continue;
            }
            output.push_str(&format_function_declaration(symbol, sigs));
        }
        // Clone proof_steps to avoid borrow checker issues
        let proof_steps = self.proof_steps.clone();
        for step in &proof_steps {
            match step {
                ProofStepData::OriginalClause { clause, .. } => {
                    self.introduce_literals(clause, &mut output);
                    output.push_str("a ");
                    for &lit in clause {
                        output.push_str(&format!("{} ", lit));
                    }
                    output.push_str("0\n");
                }
                ProofStepData::SATClause { clause, .. } => {
                    for &lit in clause {
                        output.push_str(&format!("{} ", lit));
                    }
                    output.push_str("0\n");
                }
                ProofStepData::TheoryClause { clause, .. } => {
                    self.introduce_literals(clause, &mut output);
                    output.push_str("t ");
                    for &lit in clause {
                        output.push_str(&format!("{} ", lit));
                    }
                    output.push_str("0\n");
                }
                ProofStepData::Skolemization {
                    clause,
                    skolem_vars,
                } => {
                    // for right now we assume skolemization to be true
                    if let Some(vars) = skolem_vars {
                        for var in vars {
                            output.push_str(&format!("(declare-fun {} () {})\n", var.0, var.1));
                        }
                    }

                    self.introduce_literals(clause, &mut output);

                    output.push_str("a ");
                    for &lit in clause {
                        output.push_str(&format!("{} ", lit));
                    }
                    output.push_str("0\n");
                }
                ProofStepData::Deletion { id } => {
                    output.push_str(&format!("d {} 0\n", id));
                }
            }
        }
        output
    }
}

impl ProofTracer for SMTProofTracker {
    fn add_original_clause(&mut self, _id: u64, _redundant: bool, clause: &[i32], _restored: bool) {
        if self.skolemizations.contains(clause) {
            return;
        }
        if !self.finished_original_clauses {
            // println!("original_clause {:?}", clause);
            self.proof_steps.push(ProofStepData::OriginalClause {
                clause: clause.to_vec(),
            });
        } else {
            debug_println!(19, 0, "We are adding the theory clause {:?}", clause);
            self.proof_steps.push(ProofStepData::TheoryClause {
                clause: clause.to_vec(),
            });
        }
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

        self.proof_steps.push(ProofStepData::SATClause {
            clause: clause.to_vec(),
        });
    }

    fn delete_clause(&mut self, id: u64, _redundant: bool, _clause: &[i32]) {
        self.proof_steps.push(ProofStepData::Deletion { id });
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
        // Optional: track assumption resets
        panic!("Do not currently support assumptions")
    }

    fn add_assumption_clause(&mut self, _id: u64, _clause: &[i32], _antecedents: &[u64]) {
        panic!("Do not currently support assumptions")
    }

    fn conclude_sat(&mut self, _conclusion_type: i32, _model: &[i32]) {}

    fn conclude_unsat(&mut self, _conclusion_type: i32, _clause_ids: &[u64]) {}

    fn conclude_unknown(&mut self, _trail: &[i32]) {}
}
