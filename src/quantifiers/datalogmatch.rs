// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::debug_println;
use crate::egraphs::egraph::Egraph;
use crate::utils::DeterministicHashMap;
use std::collections::{HashMap, HashSet};
use yaspar_ir::ast::ATerm::*;
use yaspar_ir::ast::{Repr, Term};

// ============================================================
// Data types for flattened patterns
// ============================================================

/// Represents a variable in a flattened pattern.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum FlatVar {
    /// An original quantifier-bound variable, identified by name.
    Quantified(String),
    /// A fresh intermediate variable introduced during flattening.
    Fresh(usize),
    /// A ground term (constant/global) with a known uid.
    Ground(u64),
}

/// A single flattened relational atom: func(args...) = output.
/// All arguments and the output are variables — no nested function applications.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FlatAtom {
    /// The function symbol name (matches the keys used in `function_maps`).
    pub func: String,
    /// The argument variables (all flat — no nesting).
    pub args: Vec<FlatVar>,
    /// The output/result variable.
    pub output: FlatVar,
}

// ============================================================
// Pattern flattening (compile phase)
// ============================================================

/// Flatten a single pattern term into a list of relational atoms.
///
/// Returns the list of atoms and the variable representing the root of the pattern.
/// `quant_vars` is the set of quantifier-bound variable names.
/// `fresh_counter` is used to generate globally unique fresh variable IDs.
pub fn flatten_pattern(
    term: &Term,
    quant_vars: &[String],
    fresh_counter: &mut usize,
) -> (Vec<FlatAtom>, FlatVar) {
    match term.repr() {
        Local(local) => {
            let name = local.symbol.to_string();
            debug_assert!(
                quant_vars.contains(&name),
                "Local variable {} not in quantifier variables {:?}",
                name,
                quant_vars
            );
            (vec![], FlatVar::Quantified(name))
        }

        App(func, args, _) => {
            let func_indices = &func.0.indices;
            let func_name = if func_indices.is_empty() {
                func.id_str().get().clone()
            } else {
                debug_assert_eq!(*func.id_str().get(), "is".to_string());
                debug_assert_eq!(func_indices.len(), 1);
                format!("(is {})", func_indices[0])
            };
            flatten_application(func_name, args.iter().collect(), quant_vars, fresh_counter)
        }

        Ite(b, t1, t2) => flatten_application(
            "ite".to_string(),
            vec![b, t1, t2],
            quant_vars,
            fresh_counter,
        ),

        Eq(left, right) => flatten_application(
            "=".to_string(),
            vec![left, right],
            quant_vars,
            fresh_counter,
        ),

        Not(t) => flatten_application("not".to_string(), vec![t], quant_vars, fresh_counter),

        Constant(..) | Global(..) => (vec![], FlatVar::Ground(term.uid())),

        other => panic!(
            "Unexpected term variant in pattern during flattening: {:?}",
            other
        ),
    }
}

fn flatten_application(
    func_name: String,
    args: Vec<&Term>,
    quant_vars: &[String],
    fresh_counter: &mut usize,
) -> (Vec<FlatAtom>, FlatVar) {
    let mut all_atoms = Vec::new();
    let mut arg_vars = Vec::new();

    for arg in args {
        let (atoms, var) = flatten_pattern(arg, quant_vars, fresh_counter);
        all_atoms.extend(atoms);
        arg_vars.push(var);
    }

    let output = FlatVar::Fresh(*fresh_counter);
    *fresh_counter += 1;

    all_atoms.push(FlatAtom {
        func: func_name,
        args: arg_vars,
        output: output.clone(),
    });

    (all_atoms, output)
}

/// Compile all multipatterns for a quantifier into flattened atoms.
pub fn compile_multipatterns(
    triggers: &[Vec<&Term>],
    quant_vars: &[String],
    fresh_counter: &mut usize,
) -> Vec<Vec<FlatAtom>> {
    let mut result = Vec::new();
    for multipattern in triggers {
        let mut atoms_for_multipattern = Vec::new();
        for pattern_term in multipattern {
            let (atoms, _root) = flatten_pattern(pattern_term, quant_vars, fresh_counter);
            atoms_for_multipattern.extend(atoms);
        }
        result.push(atoms_for_multipattern);
    }
    result
}

// ============================================================
// Relational matching engine
// ============================================================

/// A canonical entry in a function table.
#[derive(Clone)]
struct CanonEntry {
    /// Canonical e-class of the term itself (output).
    output: u64,
    /// Canonical e-classes of the arguments.
    args: Vec<u64>,
}

/// Pre-built index for a single function symbol.
struct FuncTable {
    /// All canonical entries (deduplicated by canonical form).
    entries: Vec<CanonEntry>,
    /// Per-argument index: arg_index[i][eclass] = entry indices where arg i has that eclass.
    arg_index: Vec<HashMap<u64, Vec<usize>>>,
    /// Output index: output_index[eclass] = entry indices with that output eclass.
    output_index: HashMap<u64, Vec<usize>>,
    /// Number of entries that existed before the current round (for semi-naive).
    old_count: usize,
}

/// The matching index, built once at the start of each matching round.
struct MatchingIndex {
    tables: HashMap<String, FuncTable>,
}

type Binding = HashMap<FlatVar, u64>;

/// Build the matching index from function_maps, canonicalizing all e-classes.
fn build_matching_index(egraph: &Egraph) -> MatchingIndex {
    let mut tables = HashMap::new();

    for (func_name, raw_entries) in &egraph.function_maps {
        let old_watermark = egraph
            .function_maps_watermark
            .get(func_name)
            .copied()
            .unwrap_or(0);

        let arity = raw_entries.first().map(|(_, args)| args.len()).unwrap_or(0);

        // Track which canonical entries are "old" (existed before this round)
        let mut old_canonical: HashSet<(u64, Vec<u64>)> = HashSet::new();

        // First pass: identify old canonical entries
        for (term_uid, arg_uids) in raw_entries.iter().take(old_watermark) {
            let canon_output = egraph.find(*term_uid);
            let canon_args: Vec<u64> = arg_uids.iter().map(|a| egraph.find(*a)).collect();
            old_canonical.insert((canon_output, canon_args));
        }

        // Build entries partitioned: old entries first, then new entries.
        let mut old_entries = Vec::new();
        let mut new_entries = Vec::new();
        for (term_uid, arg_uids) in raw_entries {
            let canon_output = egraph.find(*term_uid);
            let canon_args: Vec<u64> = arg_uids.iter().map(|a| egraph.find(*a)).collect();
            let key = (canon_output, canon_args);
            if old_canonical.contains(&key) {
                old_entries.push(key);
            } else {
                new_entries.push(key);
            }
        }
        // Dedup within each group
        let mut final_entries = Vec::new();
        let mut final_seen: HashSet<(u64, Vec<u64>)> = HashSet::new();
        let mut final_arg_index: Vec<HashMap<u64, Vec<usize>>> = vec![HashMap::new(); arity];
        let mut final_output_index: HashMap<u64, Vec<usize>> = HashMap::new();

        for key in old_entries.iter().chain(new_entries.iter()) {
            // Skip entries with mismatched arity (overloaded function symbols)
            if key.1.len() != arity {
                continue;
            }
            if !final_seen.insert(key.clone()) {
                continue;
            }
            let idx = final_entries.len();
            for (i, &eclass) in key.1.iter().enumerate() {
                final_arg_index[i].entry(eclass).or_default().push(idx);
            }
            final_output_index.entry(key.0).or_default().push(idx);
            final_entries.push(CanonEntry {
                output: key.0,
                args: key.1.clone(),
            });
        }

        let old_count_final = final_entries
            .iter()
            .take_while(|e| old_canonical.contains(&(e.output, e.args.clone())))
            .count();

        tables.insert(
            func_name.clone(),
            FuncTable {
                entries: final_entries,
                arg_index: final_arg_index,
                output_index: final_output_index,
                old_count: old_count_final,
            },
        );
    }

    MatchingIndex { tables }
}

/// Compute join order: sort atoms by estimated table size (smaller first).
/// This is our simple query optimizer.
fn compute_join_order(atoms: &[FlatAtom], index: &MatchingIndex) -> Vec<usize> {
    let mut order: Vec<usize> = (0..atoms.len()).collect();
    order.sort_by_key(|&i| {
        index
            .tables
            .get(&atoms[i].func)
            .map(|t| t.entries.len())
            .unwrap_or(0)
    });
    order
}

/// Try to extend a binding with a function table entry for a given atom.
/// Returns None if the entry is inconsistent with the current binding.
fn try_extend_binding(binding: &Binding, atom: &FlatAtom, entry: &CanonEntry) -> Option<Binding> {
    let mut new_binding = binding.clone();

    // Check/bind each argument
    for (var, &eclass) in atom.args.iter().zip(entry.args.iter()) {
        match new_binding.get(var) {
            Some(&bound) if bound == eclass => {} // consistent
            Some(_) => return None,               // conflict
            None => {
                new_binding.insert(var.clone(), eclass);
            }
        }
    }

    // Check/bind output
    match new_binding.get(&atom.output) {
        Some(&bound) if bound == entry.output => {} // consistent
        Some(_) => return None,                     // conflict
        None => {
            new_binding.insert(atom.output.clone(), entry.output);
        }
    }

    Some(new_binding)
}

/// Get candidate entry indices for an atom given the current binding.
/// Uses the best available index for efficiency.
fn get_candidates(
    table: &FuncTable,
    atom: &FlatAtom,
    binding: &Binding,
    delta_only: bool,
) -> Vec<usize> {
    let mut best_candidates: Option<&Vec<usize>> = None;
    let mut best_size = usize::MAX;

    // Check argument indices
    for (i, var) in atom.args.iter().enumerate() {
        if let Some(&eclass) = binding.get(var) {
            if let Some(candidates) = table.arg_index[i].get(&eclass) {
                if candidates.len() < best_size {
                    best_size = candidates.len();
                    best_candidates = Some(candidates);
                }
            } else {
                return vec![]; // No entries match this bound argument
            }
        }
    }

    // Check output index
    if let Some(&eclass) = binding.get(&atom.output) {
        if let Some(candidates) = table.output_index.get(&eclass) {
            if candidates.len() < best_size {
                best_candidates = Some(candidates);
            }
        } else {
            return vec![]; // No entries match bound output
        }
    }

    match best_candidates {
        Some(candidates) => {
            if delta_only {
                candidates
                    .iter()
                    .filter(|&&idx| idx >= table.old_count)
                    .copied()
                    .collect()
            } else {
                candidates.clone()
            }
        }
        None => {
            // No bound variables — full scan
            let start = if delta_only { table.old_count } else { 0 };
            (start..table.entries.len()).collect()
        }
    }
}

/// Execute a left-deep join in the given atom order.
/// If `delta_position` is Some(i), position i in the order uses only delta (new) entries.
fn execute_join(
    order: &[usize],
    atoms: &[FlatAtom],
    index: &MatchingIndex,
    delta_position: Option<usize>,
    initial_binding: Binding,
) -> Vec<Binding> {
    let mut bindings = vec![initial_binding];

    for (pos, &atom_idx) in order.iter().enumerate() {
        let atom = &atoms[atom_idx];
        let table = match index.tables.get(&atom.func) {
            Some(t) => t,
            None => return vec![], // Function not in egraph
        };
        let use_delta = delta_position == Some(pos);

        let mut new_bindings = Vec::new();
        for binding in &bindings {
            let candidates = get_candidates(table, atom, binding, use_delta);
            for entry_idx in candidates {
                let entry = &table.entries[entry_idx];
                if let Some(new_binding) = try_extend_binding(binding, atom, entry) {
                    new_bindings.push(new_binding);
                }
            }
        }

        bindings = new_bindings;
        if bindings.is_empty() {
            break;
        }
    }

    bindings
}

/// Evaluate a single multipattern (conjunctive query) with semi-naive evaluation.
fn evaluate_multipattern(atoms: &[FlatAtom], index: &MatchingIndex, egraph: &Egraph) -> Vec<Binding> {
    if atoms.is_empty() {
        return vec![];
    }

    let order = compute_join_order(atoms, index);

    // Initialize binding with ground variables
    let mut initial_binding = Binding::new();
    for atom in atoms {
        for var in atom.args.iter().chain(std::iter::once(&atom.output)) {
            if let FlatVar::Ground(uid) = var {
                initial_binding.insert(var.clone(), egraph.find(*uid));
            }
        }
    }

    // Semi-naive optimization: check if any atom has new (delta) entries.
    // Watermarks are reset on backtracks (detected via predecessor_hash change),
    // so after a backtrack all entries are treated as new.
    let any_has_delta = order.iter().any(|&atom_idx| {
        index
            .tables
            .get(&atoms[atom_idx].func)
            .map(|t| t.old_count < t.entries.len())
            .unwrap_or(false)
    });

    if !any_has_delta {
        return vec![];
    }

    // For each atom position that has delta, run a pass where that atom
    // uses only new entries (all others use all entries). Union results.
    let mut all_bindings = Vec::new();
    let mut seen: HashSet<Vec<u64>> = HashSet::new();

    for (pos, &atom_idx) in order.iter().enumerate() {
        let func = &atoms[atom_idx].func;
        let has_delta = index
            .tables
            .get(func)
            .map(|t| t.old_count < t.entries.len())
            .unwrap_or(false);

        if !has_delta {
            continue;
        }

        let bindings = execute_join(&order, atoms, index, Some(pos), initial_binding.clone());

        for b in bindings {
            let mut key: Vec<u64> = b
                .iter()
                .filter_map(|(k, v)| {
                    if let FlatVar::Quantified(_) = k {
                        Some(*v)
                    } else {
                        None
                    }
                })
                .collect();
            key.sort();

            if seen.insert(key) {
                all_bindings.push(b);
            }
        }
    }

    all_bindings
}

/// Reset watermarks if a backtrack has occurred since the last matching round.
/// Must be called before building the matching index.
pub fn datalog_check_backtrack(egraph: &mut Egraph) {
    if egraph.predecessor_hash != egraph.watermark_hash {
        egraph.function_maps_watermark.clear();
    }
}

/// Main entry point: find all new variable assignments for all quantifiers.
///
/// Returns: Vec<(quantifier_uid, list of variable assignments)>
pub fn datalog_find_assignments(
    egraph: &Egraph,
) -> Vec<(u64, Vec<DeterministicHashMap<String, Term>>)> {
    let index = build_matching_index(egraph);
    let flat_patterns = &egraph.flat_patterns;

    let mut results = Vec::new();

    for quantifier in &egraph.quantifiers {
        if let Some(multipatterns) = flat_patterns.get(&quantifier.id) {
            let mut quant_assignments = Vec::new();

            for atoms in multipatterns {
                let bindings = evaluate_multipattern(atoms, &index, egraph);

                for binding in bindings {
                    // Convert binding to DeterministicHashMap<String, Term>
                    let mut assignment = DeterministicHashMap::new();
                    for (var, eclass) in &binding {
                        if let FlatVar::Quantified(name) = var {
                            assignment.insert(name.clone(), egraph.get_term(*eclass));
                        }
                    }

                    // Only include if all quantifier variables are bound
                    if quantifier.variables.iter().all(|v| assignment.contains_key(v)) {
                        quant_assignments.push(assignment);
                    }
                }
            }

            if !quant_assignments.is_empty() {
                debug_println!(
                    24,
                    0,
                    "Datalog matcher found {} assignments for quantifier {}",
                    quant_assignments.len(),
                    egraph.get_term(quantifier.id)
                );
                results.push((quantifier.id, quant_assignments));
            }
        }
    }

    results
}

/// Update watermarks after a matching round.
pub fn datalog_update_watermarks(egraph: &mut Egraph) {
    for (func_name, entries) in &egraph.function_maps {
        egraph
            .function_maps_watermark
            .insert(func_name.clone(), entries.len());
    }
    egraph.watermark_hash = egraph.predecessor_hash;
}

// ============================================================
// Display implementations
// ============================================================

impl std::fmt::Display for FlatVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FlatVar::Quantified(name) => write!(f, "?{}", name),
            FlatVar::Fresh(id) => write!(f, "?v{}", id),
            FlatVar::Ground(uid) => write!(f, "#{}", uid),
        }
    }
}

impl std::fmt::Display for FlatAtom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}(", self.func)?;
        for (i, arg) in self.args.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", arg)?;
        }
        write!(f, ") = {}", self.output)
    }
}
