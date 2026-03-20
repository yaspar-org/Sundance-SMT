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
            // Use func.to_string() to match the key format used in function_maps
            let func_name = func.to_string();
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
    /// Raw (original) argument UIDs — used for producing final variable bindings.
    /// These are actual terms that exist in the egraph.
    raw_args: Vec<u64>,
    /// Raw (original) term UID for the output.
    raw_output: u64,
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

/// Build the matching index from the canonical function_maps and function_indices.
///
/// Since function_maps and function_indices are already maintained in canonical form
/// (updated on every union), we just need to:
/// 1. Collect all f-node UIDs from function_maps (output index)
/// 2. Look up their raw args from function_entries
/// 3. Build per-entry CanonEntry structs
/// 4. Build the per-argument and output hash indices for the matching engine
fn build_matching_index(egraph: &Egraph) -> MatchingIndex {
    let mut tables = HashMap::new();

    for (func_name, output_map) in &egraph.function_maps {
        // Collect all f-node UIDs and determine arity from function_entries
        let raw_entries_opt = egraph.function_entries.get(func_name);
        if raw_entries_opt.is_none() {
            continue;
        }

        // Build a lookup: term_uid -> raw arg_uids from function_entries
        let raw_lookup: HashMap<u64, &Vec<u64>> = raw_entries_opt
            .unwrap()
            .iter()
            .map(|(uid, args)| (*uid, args))
            .collect();

        let arity = raw_entries_opt
            .unwrap()
            .first()
            .map(|(_, args)| args.len())
            .unwrap_or(0);

        let mut final_entries = Vec::new();
        let mut final_arg_index: Vec<HashMap<u64, Vec<usize>>> = vec![HashMap::new(); arity];
        let mut final_output_index: HashMap<u64, Vec<usize>> = HashMap::new();
        let mut seen: HashSet<u64> = HashSet::new(); // dedup by f-node UID

        // Iterate over the canonical output index
        for (canon_output, fnode_uids) in output_map {
            for &fnode_uid in fnode_uids {
                if !seen.insert(fnode_uid) {
                    continue;
                }
                let raw_args = match raw_lookup.get(&fnode_uid) {
                    Some(args) => args,
                    None => continue,
                };
                if raw_args.len() != arity {
                    continue;
                }
                // Get canonical args from function_indices (they're already canonical there)
                let canon_args: Vec<u64> = raw_args.iter().map(|a| egraph.find(*a)).collect();
                let idx = final_entries.len();
                for (i, &canon_arg) in canon_args.iter().enumerate() {
                    final_arg_index[i].entry(canon_arg).or_default().push(idx);
                }
                final_output_index
                    .entry(*canon_output)
                    .or_default()
                    .push(idx);
                final_entries.push(CanonEntry {
                    output: *canon_output,
                    args: canon_args,
                    raw_args: (*raw_args).clone(),
                    raw_output: fnode_uid,
                });
            }
        }

        // For semi-naive: all entries are treated as new (old_count = 0) since the
        // canonical indices are always up-to-date. The watermark tracking is no longer
        // needed because the persistent data structure handles backtracks.
        // TODO: re-implement semi-naive with the persistent indices if performance requires it
        tables.insert(
            func_name.clone(),
            FuncTable {
                entries: final_entries,
                arg_index: final_arg_index,
                output_index: final_output_index,
                old_count: 0,
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
///
/// The binding stores **raw** UIDs (actual terms in the egraph). Consistency is
/// checked using canonical e-classes (via `find()`), but new variables are bound
/// to the raw UIDs from the entry. This ensures we only bind variables to terms
/// that actually exist in the egraph.
fn try_extend_binding(
    binding: &Binding,
    atom: &FlatAtom,
    entry: &CanonEntry,
    egraph: &Egraph,
) -> Option<Binding> {
    let mut new_binding = binding.clone();

    // Check/bind each argument: compare canonically, bind raw
    for (var, (&canon_eclass, &raw_uid)) in atom
        .args
        .iter()
        .zip(entry.args.iter().zip(entry.raw_args.iter()))
    {
        match new_binding.get(var) {
            Some(&bound) if egraph.find(bound) == canon_eclass => {} // consistent
            Some(_) => return None,                                  // conflict
            None => {
                new_binding.insert(var.clone(), raw_uid);
            }
        }
    }

    // Check/bind output: compare canonically, bind raw
    match new_binding.get(&atom.output) {
        Some(&bound) if egraph.find(bound) == entry.output => {} // consistent
        Some(_) => return None,                                  // conflict
        None => {
            new_binding.insert(atom.output.clone(), entry.raw_output);
        }
    }

    Some(new_binding)
}

/// Get candidate entry indices for an atom given the current binding.
/// Uses the best available index for efficiency.
/// Binding values are raw UIDs, so we canonicalize via `find()` before index lookup.
fn get_candidates(
    table: &FuncTable,
    atom: &FlatAtom,
    binding: &Binding,
    delta_only: bool,
    egraph: &Egraph,
) -> Vec<usize> {
    let mut best_candidates: Option<&Vec<usize>> = None;
    let mut best_size = usize::MAX;

    // Check argument indices (canonicalize binding values for lookup)
    for (i, var) in atom.args.iter().enumerate() {
        if let Some(&raw_uid) = binding.get(var) {
            let canon = egraph.find(raw_uid);
            if let Some(candidates) = table.arg_index[i].get(&canon) {
                debug_println!(
                    26,
                    0,
                    "      get_candidates: arg[{}] {} bound to raw={} canon={} -> {} candidates",
                    i,
                    var,
                    raw_uid,
                    canon,
                    candidates.len()
                );
                if candidates.len() < best_size {
                    best_size = candidates.len();
                    best_candidates = Some(candidates);
                }
            } else {
                debug_println!(
                    26,
                    0,
                    "      get_candidates: arg[{}] {} bound to raw={} canon={} -> NO MATCH (index keys: {:?})",
                    i,
                    var,
                    raw_uid,
                    canon,
                    table.arg_index[i].keys().collect::<Vec<_>>()
                );
                return vec![]; // No entries match this bound argument
            }
        }
    }

    // Check output index (canonicalize binding value for lookup)
    if let Some(&raw_uid) = binding.get(&atom.output) {
        let canon = egraph.find(raw_uid);
        if let Some(candidates) = table.output_index.get(&canon) {
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
    egraph: &Egraph,
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
            let candidates = get_candidates(table, atom, binding, use_delta, egraph);
            for entry_idx in candidates {
                let entry = &table.entries[entry_idx];
                if let Some(new_binding) = try_extend_binding(binding, atom, entry, egraph) {
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
fn evaluate_multipattern(
    atoms: &[FlatAtom],
    index: &MatchingIndex,
    egraph: &Egraph,
) -> Vec<Binding> {
    if atoms.is_empty() {
        debug_println!(26, 0, "  evaluate_multipattern: empty atoms, returning");
        return vec![];
    }

    debug_println!(26, 0, "  evaluate_multipattern: {} atoms", atoms.len());
    for (i, atom) in atoms.iter().enumerate() {
        let table_size = index
            .tables
            .get(&atom.func)
            .map(|t| t.entries.len())
            .unwrap_or(0);
        let table_old = index
            .tables
            .get(&atom.func)
            .map(|t| t.old_count)
            .unwrap_or(0);
        debug_println!(
            26,
            0,
            "    atom[{}]: {}  (table size={}, old={})",
            i,
            atom,
            table_size,
            table_old
        );
    }

    let order = compute_join_order(atoms, index);
    debug_println!(26, 0, "  join order: {:?}", order);

    // Initialize binding with ground variables
    let mut initial_binding = Binding::new();
    for atom in atoms {
        for var in atom.args.iter().chain(std::iter::once(&atom.output)) {
            if let FlatVar::Ground(uid) = var {
                initial_binding.insert(var.clone(), *uid);
            }
        }
    }
    if !initial_binding.is_empty() {
        debug_println!(
            26,
            0,
            "  initial ground bindings: {:?}",
            initial_binding
                .iter()
                .map(|(k, v)| format!("{} -> {} (canon={})", k, v, egraph.find(*v)))
                .collect::<Vec<_>>()
        );
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
        debug_println!(26, 0, "  no delta entries for any atom, skipping");
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
            debug_println!(
                26,
                0,
                "  pass pos={}: atom[{}] ({}) has no delta, skipping",
                pos,
                atom_idx,
                func
            );
            continue;
        }

        debug_println!(
            26,
            0,
            "  pass pos={}: atom[{}] ({}) using delta",
            pos,
            atom_idx,
            func
        );

        let bindings = execute_join(
            &order,
            atoms,
            index,
            Some(pos),
            initial_binding.clone(),
            egraph,
        );

        debug_println!(
            26,
            0,
            "    join produced {} raw bindings",
            bindings.len()
        );

        for b in bindings {
            // Dedup key uses canonical e-classes (bindings store raw UIDs).
            // We pair each variable name with its canonical value to preserve
            // the variable-to-value mapping (sorting by name, not by value).
            let mut key: Vec<(String, u64)> = b
                .iter()
                .filter_map(|(k, v)| {
                    if let FlatVar::Quantified(name) = k {
                        Some((name.clone(), egraph.find(*v)))
                    } else {
                        None
                    }
                })
                .collect();
            key.sort_by(|a, b| a.0.cmp(&b.0));
            let key_vals: Vec<u64> = key.into_iter().map(|(_, v)| v).collect();

            if seen.insert(key_vals) {
                debug_println!(
                    26,
                    0,
                    "    new binding: {:?}",
                    b.iter()
                        .filter_map(|(k, v)| {
                            if let FlatVar::Quantified(name) = k {
                                Some(format!(
                                    "{}={} (canon={})",
                                    name,
                                    egraph.get_term(*v),
                                    egraph.find(*v)
                                ))
                            } else {
                                None
                            }
                        })
                        .collect::<Vec<_>>()
                );
                all_bindings.push(b);
            }
        }
    }

    debug_println!(
        26,
        0,
        "  total unique bindings: {}",
        all_bindings.len()
    );
    all_bindings
}

/// Reset watermarks if a backtrack has occurred since the last matching round.
/// With persistent canonical indices, backtracking is handled by snapshot/restore
/// in notify_backtrack, so this just updates the watermark hash.
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
                    if quantifier
                        .variables
                        .iter()
                        .all(|v| assignment.contains_key(v))
                    {
                        quant_assignments.push(assignment);
                    }
                }
            }

            // if !quant_assignments.is_empty() {
                debug_println!(
                    26,
                    0,
                    "Datalog matcher found {} assignments for quantifier {}",
                    quant_assignments.len(),
                    egraph.get_term(quantifier.id)
                );
                results.push((quantifier.id, quant_assignments));
            // }
        }
    }

    results
}

/// Update watermarks after a matching round.
pub fn datalog_update_watermarks(egraph: &mut Egraph) {
    for (func_name, entries) in &egraph.function_entries {
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
