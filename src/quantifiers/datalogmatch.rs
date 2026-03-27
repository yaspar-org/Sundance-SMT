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

type Binding = HashMap<FlatVar, u64>;

/// Estimate the number of entries for a function in the egraph.
fn table_size(egraph: &Egraph, func: &str) -> usize {
    egraph
        .function_entries
        .get(func)
        .map(|e| e.len())
        .unwrap_or(0)
}

/// Compute join order: sort atoms by estimated table size (smaller first).
fn compute_join_order(atoms: &[FlatAtom], egraph: &Egraph) -> Vec<usize> {
    let mut order: Vec<usize> = (0..atoms.len()).collect();
    order.sort_by_key(|&i| table_size(egraph, &atoms[i].func));
    order
}

/// Try to extend a binding with a candidate fnode for a given atom.
/// Returns None if the candidate is inconsistent with the current binding.
///
/// The binding stores **raw** UIDs (actual terms in the egraph). Consistency is
/// checked using canonical e-classes (via `find()`), but new variables are bound
/// to the raw UIDs from the entry.
fn try_extend_binding(
    binding: &Binding,
    atom: &FlatAtom,
    fnode_uid: u64,
    raw_args: &[u64],
    egraph: &Egraph,
) -> Option<Binding> {
    let mut new_binding = binding.clone();

    // Check/bind each argument: compare canonically, bind raw
    for (var, &raw_uid) in atom.args.iter().zip(raw_args.iter()) {
        let canon_eclass = egraph.find(raw_uid);
        match new_binding.get(var) {
            Some(&bound) if egraph.find(bound) == canon_eclass => {} // consistent
            Some(_) => return None,                                  // conflict
            None => {
                new_binding.insert(var.clone(), raw_uid);
            }
        }
    }

    // Check/bind output: compare canonically, bind raw
    let canon_output = egraph.find(fnode_uid);
    match new_binding.get(&atom.output) {
        Some(&bound) if egraph.find(bound) == canon_output => {} // consistent
        Some(_) => return None,                                  // conflict
        None => {
            new_binding.insert(atom.output.clone(), fnode_uid);
        }
    }

    Some(new_binding)
}

/// Eagerly intersect a new candidate set into a running result.
/// If result is None, initializes it. Otherwise retains only UIDs present in both.
fn intersect_candidates(result: &mut Option<HashSet<u64>>, candidates: &[u64]) {
    match result {
        None => {
            *result = Some(candidates.iter().copied().collect());
        }
        Some(set) => {
            let other: HashSet<u64> = candidates.iter().copied().collect();
            set.retain(|uid| other.contains(uid));
        }
    }
}

/// Get candidate fnode UIDs for an atom given the current binding.
/// Queries function_maps (output index) and function_indices (arg index) directly.
///
/// For each bound variable, we look up the corresponding index and eagerly intersect
/// into a running candidate set. Each new index lookup narrows the set further.
/// If the set becomes empty at any point, we return immediately.
///
/// If no variables are bound (e.g., the first atom in the join and no ground constants),
/// we fall back to returning all fnode UIDs for the function — the only constraint is
/// the function symbol itself. `try_extend_binding` then does all the work of binding
/// variables and checking consistency.
fn get_candidates(
    atom: &FlatAtom,
    binding: &Binding,
    delta_only: bool,
    egraph: &Egraph,
) -> Vec<u64> {
    let mut result: Option<HashSet<u64>> = None;
    let matching_round = egraph.matching_round;

    // Check argument indices (canonicalize binding values for lookup)
    if let Some(arg_idx) = egraph.function_indices.get(&atom.func) {
        for (i, var) in atom.args.iter().enumerate() {
            if i >= arg_idx.args.len() {
                break;
            }
            if let Some(&raw_uid) = binding.get(var) {
                let canon = egraph.find(raw_uid);
                let candidates: Vec<u64> = if delta_only {
                    arg_idx.args[i].get_delta(canon, matching_round)
                } else {
                    arg_idx.args[i].get_all(canon)
                };
                debug_println!(
                    26,
                    0,
                    "      get_candidates: arg[{}] {} bound to raw={} canon={} -> {} candidates (delta={})",
                    i,
                    var,
                    raw_uid,
                    canon,
                    candidates.len(),
                    delta_only
                );
                if candidates.is_empty() {
                    return vec![];
                }
                intersect_candidates(&mut result, &candidates);
                if result.as_ref().unwrap().is_empty() {
                    return vec![];
                }
            }
        }
    }

    // Check output index (canonicalize binding value for lookup)
    if let Some(&raw_uid) = binding.get(&atom.output) {
        let canon = egraph.find(raw_uid);
        if let Some(func_out) = egraph.function_maps.get(&atom.func) {
            let candidates: Vec<u64> = if delta_only {
                func_out.output.get_delta(canon, matching_round)
            } else {
                func_out.output.get_all(canon)
            };
            if candidates.is_empty() {
                return vec![];
            }
            intersect_candidates(&mut result, &candidates);
        }
    }

    match result {
        Some(set) => set.into_iter().collect(),
        None => {
            // No bound variables — full scan: return all fnode UIDs for this function.
            // This happens for the first atom in the join order when it has no ground
            // constants. try_extend_binding will bind all unbound variables.
            if let Some(func_out) = egraph.function_maps.get(&atom.func) {
                if delta_only {
                    // Only collect fnodes from e-class keys with delta entries
                    func_out.output.index.values()
                        .flat_map(|ts| ts.delta(matching_round))
                        .collect()
                } else {
                    func_out.output.index.values()
                        .flat_map(|ts| ts.all())
                        .collect()
                }
            } else {
                vec![]
            }
        }
    }
}

/// Execute a left-deep join in the given atom order.
/// If `delta_position` is Some(i), position i uses only delta entries (hot check).
fn execute_join(
    order: &[usize],
    atoms: &[FlatAtom],
    delta_position: Option<usize>,
    initial_binding: Binding,
    egraph: &Egraph,
) -> Vec<Binding> {
    // Build a raw-arg lookup for each function we need
    let func_lookups: HashMap<&str, HashMap<u64, &Vec<u64>>> = {
        let mut lookups = HashMap::new();
        for &atom_idx in order {
            let func = &atoms[atom_idx].func;
            if !lookups.contains_key(func.as_str())
                && let Some(entries) = egraph.function_entries.get(func) {
                    let lookup: HashMap<u64, &Vec<u64>> =
                        entries.iter().map(|(uid, args)| (*uid, args)).collect();
                    lookups.insert(func.as_str(), lookup);
                }
        }
        lookups
    };

    let mut bindings = vec![initial_binding];

    for (pos, &atom_idx) in order.iter().enumerate() {
        let atom = &atoms[atom_idx];
        let use_delta = delta_position == Some(pos);

        let raw_lookup = match func_lookups.get(atom.func.as_str()) {
            Some(l) => l,
            None => return vec![], // Function not in egraph
        };

        let mut new_bindings = Vec::new();
        for binding in &bindings {
            let candidates = get_candidates(atom, binding, use_delta, egraph);
            debug_println!(28, 0, "We have the following candidates for atom {}", atom);
            for fnode_uid in candidates {
                debug_println!(28, 4, "{}", egraph.get_term(fnode_uid));
                if let Some(raw_args) = raw_lookup.get(&fnode_uid)
                    && let Some(new_binding) =
                        try_extend_binding(binding, atom, fnode_uid, raw_args, egraph)
                    {
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

/// Check if a function has any delta entries (timestamp >= matching_round).
fn func_has_delta(egraph: &Egraph, func: &str) -> bool {
    let mr = egraph.matching_round;
    egraph
        .function_maps
        .get(func)
        .map(|f| f.output.has_delta(mr))
        .unwrap_or(false)
}

/// Evaluate a single multipattern (conjunctive query) with semi-naive evaluation.
///
/// If `full_pass` is true (e.g., for a newly registered quantifier), we do a single
/// full join over all atoms (no delta filtering). Otherwise, we run k passes where
/// pass i restricts atom i to delta-only entries, ensuring we only find new derivations.
fn evaluate_multipattern(
    atoms: &[FlatAtom],
    full_pass: bool,
    egraph: &Egraph,
) -> Vec<Binding> {
    if atoms.is_empty() {
        debug_println!(26, 0, "  evaluate_multipattern: empty atoms, returning");
        return vec![];
    }

    debug_println!(
        26,
        0,
        "  evaluate_multipattern: {} atoms, full_pass={}, matching_round={}",
        atoms.len(),
        full_pass,
        egraph.matching_round
    );
    for (i, atom) in atoms.iter().enumerate() {
        let size = table_size(egraph, &atom.func);
        let has_delta = func_has_delta(egraph, &atom.func);
        debug_println!(
            26,
            0,
            "    atom[{}]: {}  (table size={}, has_delta={})",
            i,
            atom,
            size,
            has_delta
        );
    }

    let order = compute_join_order(atoms, egraph);
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

    // Dedup helper: canonical key for a binding
    let mut all_bindings = Vec::new();
    let mut seen: HashSet<Vec<u64>> = HashSet::new();

    let mut add_bindings = |bindings: Vec<Binding>,
                            all_bindings: &mut Vec<Binding>,
                            seen: &mut HashSet<Vec<u64>>,
                            egraph: &Egraph| {
        for b in bindings {
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
    };

    if full_pass {
        // Full pass: single join with no delta filtering
        debug_println!(26, 0, "  running full pass (no delta filtering)");
        let bindings = execute_join(&order, atoms, None, initial_binding, egraph);
        debug_println!(26, 0, "    join produced {} raw bindings", bindings.len());
        add_bindings(bindings, &mut all_bindings, &mut seen, egraph);
    } else {
        // Semi-naive: check if any atom has delta entries
        let any_has_delta = order
            .iter()
            .any(|&atom_idx| func_has_delta(egraph, &atoms[atom_idx].func));

        if !any_has_delta {
            debug_println!(26, 0, "  no delta entries for any atom, skipping");
            return vec![];
        }

        // Run k passes: in pass i, atom at position i uses delta-only
        for (pos, &atom_idx) in order.iter().enumerate() {
            let func = &atoms[atom_idx].func;
            if !func_has_delta(egraph, func) {
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

            let bindings =
                execute_join(&order, atoms, Some(pos), initial_binding.clone(), egraph);
            debug_println!(
                26,
                0,
                "    pass {} produced {} raw bindings",
                pos,
                bindings.len()
            );
            add_bindings(bindings, &mut all_bindings, &mut seen, egraph);
        }
    }

    debug_println!(26, 0, "  total unique bindings: {}", all_bindings.len());
    all_bindings
}

/// Reset watermarks if a backtrack has occurred since the last matching round.
/// Backtracking is handled by snapshot/restore which marks all indices hot.
pub fn datalog_check_backtrack(_egraph: &mut Egraph) {}

/// Main entry point: find all new variable assignments for all quantifiers.
///
/// Returns: Vec<(quantifier_uid, list of variable assignments)>
pub fn datalog_find_assignments(
    egraph: &mut Egraph,
) -> Vec<(u64, Vec<DeterministicHashMap<String, Term>>)> {
    // Collect per-quantifier info before the immutable borrow
    let quant_info: Vec<(u64, Vec<String>, bool)> = egraph
        .quantifiers
        .iter()
        .map(|q| (q.id, q.variables.clone(), q.needs_full_pass))
        .collect();

    let flat_patterns = &egraph.flat_patterns;
    let mut results = Vec::new();

    for (qid, variables, needs_full_pass) in &quant_info {
        if let Some(multipatterns) = flat_patterns.get(qid) {
            let mut quant_assignments = Vec::new();

            for atoms in multipatterns {
                let bindings = evaluate_multipattern(atoms, *needs_full_pass, egraph);

                for binding in bindings {
                    let mut assignment = DeterministicHashMap::new();
                    for (var, eclass) in &binding {
                        if let FlatVar::Quantified(name) = var {
                            assignment.insert(name.clone(), egraph.get_term(*eclass));
                        }
                    }

                    if variables.iter().all(|v| assignment.contains_key(v)) {
                        quant_assignments.push(assignment);
                    }
                }
            }

            debug_println!(
                26,
                0,
                "Datalog matcher found {} assignments for quantifier {}",
                quant_assignments.len(),
                egraph.get_term(*qid)
            );
            results.push((*qid, quant_assignments));
        }
    }

    // Clear needs_full_pass for all quantifiers after the matching round
    for quantifier in &mut egraph.quantifiers {
        quantifier.needs_full_pass = false;
    }

    results
}

/// Increment matching_round after each matching round for semi-naive evaluation.
pub fn datalog_update_watermarks(egraph: &mut Egraph) {
    egraph.matching_round += 1;
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
