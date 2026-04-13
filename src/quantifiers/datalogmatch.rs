// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::debug_println;
use crate::egraphs::egraph::Egraph;
use crate::utils::DeterministicHashMap;
use std::collections::{HashMap, HashSet};
use std::time::Instant;
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

        Constant(f, _)=> flatten_application(f.to_string(), vec![], quant_vars, fresh_counter),
        Global(f, _) => flatten_application(f.to_string(), vec![], quant_vars, fresh_counter),
        // Constant(..) | Global(..) => (vec![], FlatVar::Ground(term.uid())),

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

/// A binding is a pair of fixed-size slot vectors, one per variable in the
/// multipattern. Each slot stores both the canonical e-class root (for
/// consistency checks and dedup) and the raw term UID (for substitution).
/// `u64::MAX` in the root slot represents an unbound variable.
///
/// Storing the root avoids repeated `egraph.find()` calls in the hot path,
/// and the root vector doubles as the canonical dedup key.
#[derive(Clone, Debug)]
struct Binding {
    roots: Vec<u64>,
    raws: Vec<u64>,
}

const UNBOUND: u64 = u64::MAX;

impl Binding {
    fn new(num_vars: usize) -> Self {
        Binding {
            roots: vec![UNBOUND; num_vars],
            raws: vec![UNBOUND; num_vars],
        }
    }

    fn root(&self, idx: usize) -> Option<u64> {
        let v = self.roots[idx];
        if v == UNBOUND { None } else { Some(v) }
    }

    fn raw(&self, idx: usize) -> Option<u64> {
        let v = self.raws[idx];
        if v == UNBOUND { None } else { Some(v) }
    }

    fn set(&mut self, idx: usize, root: u64, raw: u64) {
        self.roots[idx] = root;
        self.raws[idx] = raw;
    }
}

/// Maps each FlatVar in a multipattern to a numeric index for use in Binding.
fn build_var_index(atoms: &[FlatAtom]) -> HashMap<FlatVar, usize> {
    let mut index = HashMap::new();
    for atom in atoms {
        for var in atom.args.iter().chain(std::iter::once(&atom.output)) {
            let len = index.len();
            index.entry(var.clone()).or_insert(len);
        }
    }
    index
}

/// Estimate the number of entries for a function in the egraph.
fn table_size(egraph: &Egraph, func: &str) -> usize {
    egraph
        .function_entries
        .get(func)
        .map(|e| e.len())
        .unwrap_or(0)
}

/// Collect all variables (non-Ground) from an atom.
fn atom_vars(atom: &FlatAtom) -> HashSet<&FlatVar> {
    atom.args
        .iter()
        .chain(std::iter::once(&atom.output))
        .filter(|v| !matches!(v, FlatVar::Ground(_)))
        .collect()
}

/// Compute join order using a greedy heuristic that avoids cartesian products.
///
/// 1. Pick the first atom by smallest table size.
/// 2. For each subsequent position, among the remaining atoms, prefer the one that
///    shares the most variables with the already-bound set (avoids cartesian products).
///    Break ties by smallest table size.
fn compute_join_order(atoms: &[FlatAtom], egraph: &Egraph) -> Option<Vec<usize>> {
    let n = atoms.len();
    if n == 0 {
        return Some(vec![]);
    }

    // Short-circuit: if any atom's function has zero entries in the egraph,
    // no binding can satisfy the conjunction — return None to signal empty result.
    for (i, atom) in atoms.iter().enumerate() {
        if table_size(egraph, &atom.func) == 0 {
            debug_println!(27, 0, "[join-order] atom[{}] '{}' has table_size=0, short-circuiting to empty result",
                i, atom.func);
            return None;
        }
    }

    // Fast path: single-atom pattern, trivial order.
    if n == 1 {
        return Some(vec![0]);
    }

    let mut remaining: Vec<usize> = (0..n).collect();
    let mut order = Vec::with_capacity(n);
    let mut bound_vars: HashSet<FlatVar> = HashSet::new();

    if crate::log::is_important(27) {
        debug_println!(27, 0, "[join-order] computing order for {} atoms:", n);
        for (i, atom) in atoms.iter().enumerate() {
            let size = table_size(egraph, &atom.func);
            let vars: Vec<String> = atom_vars(atom).iter().map(|v| format!("{}", v)).collect();
            debug_println!(27, 0, "[join-order]   atom[{}]: {} (table_size={}, vars={{{}}})", i, atom, size, vars.join(", "));
        }
    }

    // First atom: pick the smallest table
    remaining.sort_by_key(|&i| table_size(egraph, &atoms[i].func));
    if crate::log::is_important(27) {
        debug_println!(27, 0, "[join-order] first-atom candidates (sorted by table size):");
        for &i in &remaining {
            debug_println!(27, 0, "[join-order]   atom[{}] '{}' table_size={}", i, atoms[i].func, table_size(egraph, &atoms[i].func));
        }
    }
    let first = remaining.remove(0);
    for v in atom_vars(&atoms[first]) {
        bound_vars.insert(v.clone());
    }
    order.push(first);
    if crate::log::is_important(27) {
        let bv: Vec<String> = bound_vars.iter().map(|v| format!("{}", v)).collect();
        debug_println!(27, 0, "[join-order] >>> chose first: atom[{}] '{}' (table_size={}); bound_vars={{{}}}",
            first, atoms[first].func, table_size(egraph, &atoms[first].func), bv.join(", "));
    }

    // Greedily pick the next atom that shares the most variables with bound set
    while !remaining.is_empty() {
        if crate::log::is_important(27) {
            debug_println!(27, 0, "[join-order] step {} candidates:", order.len());
            for &atom_idx in &remaining {
                let vars = atom_vars(&atoms[atom_idx]);
                let shared = vars.iter().filter(|v| bound_vars.contains(*v)).count();
                let size = table_size(egraph, &atoms[atom_idx].func);
                let shared_vars: Vec<String> = vars.iter()
                    .filter(|v| bound_vars.contains(*v))
                    .map(|v| format!("{}", v))
                    .collect();
                debug_println!(27, 0, "[join-order]   atom[{}] '{}': shared={} {{{}}}, table_size={}",
                    atom_idx, atoms[atom_idx].func, shared, shared_vars.join(", "), size);
            }
        }

        let best_pos = remaining
            .iter()
            .enumerate()
            .max_by_key(|&(_, &atom_idx)| {
                let vars = atom_vars(&atoms[atom_idx]);
                let shared = vars.iter().filter(|v| bound_vars.contains(*v)).count();
                let size = table_size(egraph, &atoms[atom_idx].func);
                // Primary: maximize shared variables. Secondary: minimize table size.
                // Encode as (shared, MAX - size) so both sort ascending-is-better via max_by_key.
                (shared, usize::MAX - size)
            })
            .map(|(pos, _)| pos)
            .unwrap();

        let chosen = remaining.swap_remove(best_pos);
        if crate::log::is_important(27) {
            let prev_bound = bound_vars.clone();
            let chosen_vars = atom_vars(&atoms[chosen]);
            let shared = chosen_vars.iter().filter(|v| prev_bound.contains(*v)).count();
            let newly_bound: Vec<String> = chosen_vars.iter()
                .filter(|v| !prev_bound.contains(*v))
                .map(|v| format!("{}", v))
                .collect();
            debug_println!(27, 0, "[join-order] >>> chose atom[{}] '{}' (shared={}, table_size={}); newly bound: {{{}}}",
                chosen, atoms[chosen].func, shared, table_size(egraph, &atoms[chosen].func), newly_bound.join(", "));
        }
        for v in atom_vars(&atoms[chosen]) {
            bound_vars.insert(v.clone());
        }
        order.push(chosen);
    }

    if crate::log::is_important(27) {
        let order_str: Vec<String> = order.iter().map(|i| format!("{}", i)).collect();
        debug_println!(27, 0, "[join-order] final order: [{}]", order_str.join(", "));
    }

    Some(order)
}

/// Try to extend a binding with a candidate fnode for a given atom.
/// Returns None if the candidate is inconsistent with the current binding.
///
/// The binding stores **raw** term UIDs — the actual syntactic terms at the
/// fnode's argument slots. This matches the classic matcher, which binds each
/// variable to the literal subterm encountered during matching. Preserving raw
/// uids keeps substitution results stable across rounds (the fnode's raw args
/// don't change when unions happen), so `added_instantiations` dedup works
/// correctly and we don't re-instantiate the same quantifier with different
/// class representatives.
///
/// The root is computed once via `find()` at bind time, stored alongside the
/// raw uid, and reused for cheap consistency checks and dedup (no repeated
/// `find()` calls in the hot path).
fn try_extend_binding(
    binding: &Binding,
    atom: &FlatAtom,
    fnode_uid: u64,
    raw_args: &[u64],
    egraph: &Egraph,
    var_index: &HashMap<FlatVar, usize>,
) -> Option<Binding> {
    let mut new_binding = binding.clone();

    // Check/bind each argument: compare on pre-computed root, store both
    for (var, &raw_uid) in atom.args.iter().zip(raw_args.iter()) {
        let idx = var_index[var];
        let canon_eclass = egraph.find(raw_uid);
        match new_binding.root(idx) {
            Some(bound_root) if bound_root == canon_eclass => {} // consistent
            Some(_) => return None,                              // conflict
            None => {
                new_binding.set(idx, canon_eclass, raw_uid);
            }
        }
    }

    // Check/bind output: compare on pre-computed root, store both
    let out_idx = var_index[&atom.output];
    let canon_output = egraph.find(fnode_uid);
    match new_binding.root(out_idx) {
        Some(bound_root) if bound_root == canon_output => {} // consistent
        Some(_) => return None,                              // conflict
        None => {
            new_binding.set(out_idx, canon_output, fnode_uid);
        }
    }

    Some(new_binding)
}

/// Eagerly intersect a new candidate set into a running result.
/// If result is None, initializes it. Otherwise retains only UIDs present in both.
/// Uses sorted-vec merge intersection to avoid all hashing overhead.
fn intersect_candidates(result: &mut Option<Vec<u64>>, candidates: &mut Vec<u64>) {
    candidates.sort_unstable();
    candidates.dedup();
    match result {
        None => {
            *result = Some(std::mem::take(candidates));
        }
        Some(existing) => {
            let mut merged = Vec::with_capacity(existing.len().min(candidates.len()));
            let (mut i, mut j) = (0, 0);
            while i < existing.len() && j < candidates.len() {
                match existing[i].cmp(&candidates[j]) {
                    std::cmp::Ordering::Less => i += 1,
                    std::cmp::Ordering::Greater => j += 1,
                    std::cmp::Ordering::Equal => {
                        merged.push(existing[i]);
                        i += 1;
                        j += 1;
                    }
                }
            }
            *existing = merged;
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
    var_index: &HashMap<FlatVar, usize>,
    log: bool,
) -> Vec<u64> {
    let mut result: Option<Vec<u64>> = None;
    let matching_round = egraph.matching_round;
    let mut candidates: Vec<u64> = Vec::new();
    let mut ic_time = std::time::Duration::ZERO;
    let mut ic_calls = 0u64;

    // Check argument indices using pre-computed canonical roots
    // todo: dont do function index lookup and pick the specific variables of which you are joining on
    if let Some(arg_idx) = egraph.function_indices.get(&atom.func) {
        debug_println!(26, 0, "      get_candidates for '{}': found in function_indices, arity={}", atom.func, arg_idx.args.len());
        for (i, var) in atom.args.iter().enumerate() {
            if i >= arg_idx.args.len() {
                break;
            }
            if let Some(canon) = binding.root(var_index[var]) {
                if delta_only {
                    arg_idx.args[i].get_delta_into(canon, matching_round, &mut candidates);
                } else {
                    arg_idx.args[i].get_all_into(canon, &mut candidates);
                }
                debug_println!(27, 0, "[matching]        arg[{}] {} (var={:?}): canon={} -> {} candidates", i, var, var_index.get(var), canon, candidates.len());
                debug_println!(
                    26,
                    0,
                    "      get_candidates: arg[{}] {} bound to canon={} -> {} candidates (delta={})",
                    i,
                    var,
                    canon,
                    candidates.len(),
                    delta_only
                );
                if candidates.is_empty() {
                    if log {
                        let mut pt = egraph.datalog_phase_timers.borrow_mut();
                        pt.intersect_candidates_time += ic_time;
                        pt.intersect_candidates_calls += ic_calls;
                    }
                    return vec![];
                }
                let ic_start = log.then(Instant::now);
                intersect_candidates(&mut result, &mut candidates);
                if let Some(t) = ic_start {
                    ic_time += t.elapsed();
                    ic_calls += 1;
                }
                if result.as_ref().unwrap().is_empty() {
                    if log {
                        let mut pt = egraph.datalog_phase_timers.borrow_mut();
                        pt.intersect_candidates_time += ic_time;
                        pt.intersect_candidates_calls += ic_calls;
                    }
                    return vec![];
                }
            }
        }
    }

    // Check output index using pre-computed root
    if let Some(canon) = binding.root(var_index[&atom.output]) {
        if let Some(func_out) = egraph.function_maps.get(&atom.func) {
            if delta_only {
                func_out.output.get_delta_into(canon, matching_round, &mut candidates);
            } else {
                func_out.output.get_all_into(canon, &mut candidates);
            }
            debug_println!(27, 0, "[matching]        output (var={:?}): canon={} -> {} candidates", &atom.output, canon, candidates.len());
            if candidates.is_empty() {
                if log {
                    let mut pt = egraph.datalog_phase_timers.borrow_mut();
                    pt.intersect_candidates_time += ic_time;
                    pt.intersect_candidates_calls += ic_calls;
                }
                return vec![];
            }
            let ic_start = log.then(Instant::now);
            intersect_candidates(&mut result, &mut candidates);
            if let Some(t) = ic_start {
                ic_time += t.elapsed();
                ic_calls += 1;
            }
        }
    }

    if log {
        let mut pt = egraph.datalog_phase_timers.borrow_mut();
        pt.intersect_candidates_time += ic_time;
        pt.intersect_candidates_calls += ic_calls;
    }

    match result {
        Some(vec) => vec,
        None => {
            // No bound variables — full scan: return all fnode UIDs for this function.
            // This happens for the first atom in the join order when it has no ground
            // constants. try_extend_binding will bind all unbound variables.
            if let Some(func_out) = egraph.function_maps.get(&atom.func) {
                candidates.clear();
                if delta_only {
                    for ts in func_out.output.index.values() {
                        candidates.extend(ts.delta(matching_round));
                    }
                } else {
                    for ts in func_out.output.index.values() {
                        candidates.extend(ts.all());
                    }
                }
                debug_println!(27, 0, "[matching]        NO BOUND VARS: full scan {} candidates from {} eclasses", candidates.len(), func_out.output.index.len());
                debug_println!(26, 0, "      full scan for '{}': {} candidates (uids={:?}), delta_only={}, index has {} eclasses, matching_round={}", atom.func, candidates.len(), candidates, delta_only, func_out.output.index.len(), matching_round);
                candidates
            } else {
                debug_println!(24, 0, "      full scan for '{}': NOT in function_maps! keys={:?}", atom.func, egraph.function_maps.keys().collect::<Vec<_>>());
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
    var_index: &HashMap<FlatVar, usize>,
    log: bool,
) -> Vec<Binding> {
    // Build a raw-arg lookup for each function we need
    // todo: I feel like we are doing redundant work here -> try to get rid of this
    // let func_lookups: HashMap<&str, HashMap<u64, &Vec<u64>>> = {
    //     let mut lookups = HashMap::new();
    //     for &atom_idx in order {
    //         let func = &atoms[atom_idx].func;
    //         if !lookups.contains_key(func.as_str())
    //             && let Some(entries) = egraph.function_entries.get(func) {
    //                 let lookup: HashMap<u64, &Vec<u64>> =
    //                     entries.iter().map(|(uid, args)| (*uid, args)).collect();
    //                 lookups.insert(func.as_str(), lookup);
    //             }
    //     }
    //     lookups
    // };

    let ej_start = log.then(Instant::now);
    let mut bindings = vec![initial_binding];

    for (pos, &atom_idx) in order.iter().enumerate() {
        // Wrap the whole iteration body with a step_work timer so we can
        // compare execute_join_time against sum(step_work). The gap between
        // the two is purely loop-iteration overhead and RefCell commit cost.
        let step_body_start = log.then(Instant::now);
        let atom = &atoms[atom_idx];
        let use_delta = delta_position == Some(pos);

        let rl_outer_start = log.then(Instant::now);
        let raw_lookup = match egraph.function_entries.get(atom.func.as_str()) {
            Some(l) => {
                // debug_println!(26, 0, "    raw_lookup for '{}': {} entries, keys={:?}", atom.func, l.len(), l.keys().collect::<Vec<_>>());
                l
            },
            None => {
                debug_println!(
                    26,
                    0,
                    "No entries for function '{}' in egraph, skipping atom {}",
                    atom.func,
                    atom
                );
                if let Some(t) = rl_outer_start {
                    let mut pt = egraph.datalog_phase_timers.borrow_mut();
                    pt.raw_lookup_time += t.elapsed();
                    pt.raw_lookup_calls += 1;
                }
                if let Some(t) = ej_start {
                    let mut pt = egraph.datalog_phase_timers.borrow_mut();
                    pt.execute_join_time += t.elapsed();
                    pt.execute_join_calls += 1;
                }
                return vec![];
            }, // Function not in egraph
        };
        let outer_rl_elapsed = rl_outer_start.map(|t| t.elapsed()).unwrap_or_default();

        let _input_count = bindings.len();
        let mut _total_candidates = 0usize;
        let mut candidates_time = std::time::Duration::ZERO;
        let mut raw_lookup_inner_calls = 0u64;
        let mut get_candidates_calls = 0u64;
        let mut try_extend_calls = 0u64;
        let mut new_bindings_push_calls = 0u64;
        let mut candidates_iter_time = std::time::Duration::ZERO;
        let mut candidates_iter_calls = 0u64;

        let bl_start = log.then(Instant::now);
        let mut new_bindings = Vec::new();
        for binding in &bindings {
            let gc_start = log.then(Instant::now);
            let candidates = get_candidates(atom, binding, use_delta, egraph, var_index, log);
            if let Some(t) = gc_start {
                candidates_time += t.elapsed();
                get_candidates_calls += 1;
            }
            debug_println!(27, 0, "We have the following candidates for atom {}", atom);
            _total_candidates += candidates.len();
            // Time the candidates-iteration loop as a whole: it wraps the
            // per-candidate raw_lookup probe, try_extend_binding call, and Vec
            // push. We intentionally avoid per-candidate Instant::now() calls
            // here because the timer overhead would dominate the actual work
            // (each candidate does a few dozen nanoseconds of real work;
            // Instant::now pairs cost 100-500 ns on macOS). Counts are still
            // tracked so we can see throughput.
            let iter_start = log.then(Instant::now);
            for fnode_uid in candidates {
                debug_println!(27, 4, "{}", egraph.get_term(fnode_uid));
                let raw_args_opt = raw_lookup.get(&fnode_uid);
                if log {
                    raw_lookup_inner_calls += 1;
                }
                if let Some(raw_args) = raw_args_opt {
                    let ext = try_extend_binding(binding, atom, fnode_uid, raw_args, egraph, var_index);
                    if log {
                        try_extend_calls += 1;
                    }
                    if let Some(new_binding) = ext {
                        new_bindings.push(new_binding);
                        if log {
                            new_bindings_push_calls += 1;
                        }
                    } else {
                        debug_println!(26, 0, "      try_extend_binding FAILED for uid={} ({}) raw_args={:?}", fnode_uid, egraph.get_term(fnode_uid), raw_args);
                    }
                } else {
                    debug_println!(26, 0, "      uid={} NOT in raw_lookup for '{}'", fnode_uid, atom.func);
                }
            }
            if let Some(t) = iter_start {
                candidates_iter_time += t.elapsed();
                candidates_iter_calls += 1;
            }
        }
        let binding_loop_elapsed = bl_start.map(|t| t.elapsed()).unwrap_or_default();

        // Dedup bindings on canonical key: bindings that differ only in which raw
        // representative they picked for each e-class are semantically the same
        // assignment. Without this, multiple fnodes sharing the same canonical
        // classes produce duplicate bindings that explode across subsequent join
        // steps. We keep one representative per canonical equivalence class,
        // preserving raw uids in the binding so substitution later uses literal
        // subterms (matching the classic matcher). Dedup directly on the
        // precomputed roots vector (no `find()` calls).
        let dedup_start = log.then(Instant::now);
        let _before_dedup = new_bindings.len();
        new_bindings.sort_unstable_by(|a, b| a.roots.cmp(&b.roots));
        new_bindings.dedup_by(|a, b| a.roots == b.roots);
        bindings = new_bindings;
        let dedup_elapsed = dedup_start.map(|t| t.elapsed()).unwrap_or_default();

        if log {
            let mut pt = egraph.datalog_phase_timers.borrow_mut();
            pt.binding_loop_time += binding_loop_elapsed;
            pt.binding_loop_calls += 1;
            pt.get_candidates_time += candidates_time;
            pt.get_candidates_calls += get_candidates_calls;
            pt.candidates_iter_time += candidates_iter_time;
            pt.candidates_iter_calls += candidates_iter_calls;
            // Per-candidate sub-phases inside the iteration loop are tracked
            // by count only. Their wall time is captured in aggregate by
            // candidates_iter_time (no per-call Instant::now() to avoid the
            // observation overhead dominating real work).
            pt.try_extend_calls += try_extend_calls;
            pt.new_bindings_push_calls += new_bindings_push_calls;
            pt.dedup_time += dedup_elapsed;
            pt.dedup_calls += 1;
            pt.raw_lookup_time += outer_rl_elapsed;
            pt.raw_lookup_calls += 1 + raw_lookup_inner_calls;
            drop(pt);
        }

        // Level 28: show binding set after this join step
        debug_println!(28, 0, "    After step {} (atom[{}] = {}{}):", pos, atom_idx, atom, if use_delta { " [DELTA]" } else { "" });
        debug_println!(28, 0, "      {} bindings", bindings.len());
        if !bindings.is_empty() {
            // Show up to 5 example bindings
            for (bi, b) in bindings.iter().enumerate().take(5) {
                let bound_vars: Vec<String> = var_index.iter()
                    .filter_map(|(var, &idx)| {
                        b.raw(idx).map(|uid| format!("{}={}", var, egraph.get_term(uid)))
                    })
                    .collect();
                debug_println!(28, 0, "        [{}] {{ {} }}", bi, bound_vars.join(", "));
            }
            if bindings.len() > 5 {
                debug_println!(28, 0, "        ... and {} more", bindings.len() - 5);
            }
        }

        // Commit step_work time — wraps everything from the start of the
        // iteration body (incl. outer raw_lookup, the inner step work, dedup,
        // and the RefCell commit above) so the gap between execute_join_time
        // and step_work_time is purely the `for` loop iteration overhead.
        if let Some(t) = step_body_start {
            egraph.datalog_phase_timers.borrow_mut().step_work_time += t.elapsed();
            egraph.datalog_phase_timers.borrow_mut().step_work_calls += 1;
        }

        if bindings.is_empty() {
            break;
        }
    }

    if let Some(t) = ej_start {
        let mut pt = egraph.datalog_phase_timers.borrow_mut();
        pt.execute_join_time += t.elapsed();
        pt.execute_join_calls += 1;
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
    log: bool,
) -> (Vec<Binding>, HashMap<FlatVar, usize>) {
    if atoms.is_empty() {
        debug_println!(26, 0, "  evaluate_multipattern: empty atoms, returning");
        return (vec![], HashMap::new());
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

    // Build variable index: maps each FlatVar to a slot number
    let vi_start = log.then(Instant::now);
    let var_index = build_var_index(atoms);
    if let Some(t) = vi_start {
        let mut pt = egraph.datalog_phase_timers.borrow_mut();
        pt.var_index_time += t.elapsed();
        pt.var_index_calls += 1;
    }

    let jo_start = log.then(Instant::now);
    let join_order_result = compute_join_order(atoms, egraph);
    if let Some(t) = jo_start {
        let mut pt = egraph.datalog_phase_timers.borrow_mut();
        pt.join_order_time += t.elapsed();
        pt.join_order_calls += 1;
    }
    let order = match join_order_result {
        Some(o) => o,
        None => {
            // Some atom has zero entries — the join is guaranteed empty.
            debug_println!(26, 0, "  compute_join_order short-circuited (atom with table_size=0)");
            return (vec![], var_index);
        }
    };
    debug_println!(26, 0, "  join order: {:?}", order);

    // Level 28: show the join order with atom details
    debug_println!(28, 0, "  Join order (smallest table first):");
    for (pos, &atom_idx) in order.iter().enumerate() {
        let atom = &atoms[atom_idx];
        let size = table_size(egraph, &atom.func);
        let has_delta = func_has_delta(egraph, &atom.func);
        debug_println!(28, 0, "    step {}: atom[{}] {}  (table_size={}, delta={})", pos, atom_idx, atom, size, has_delta);
    }
    let num_vars = var_index.len();

    // Collect which slots correspond to quantified variables (for dedup)
    // let mut quant_slots: Vec<(String, usize)> = var_index
    //     .iter()
    //     .filter_map(|(var, &idx)| {
    //         if let FlatVar::Quantified(name) = var {
    //             Some((name.clone(), idx))
    //         } else {
    //             None
    //         }
    //     })
    //     .collect();
    // quant_slots.sort_by(|a, b| a.0.cmp(&b.0));

    // Initialize binding with ground variables: store the raw uid and its
    // canonical root so subsequent matching steps can use the root directly.
    let ib_start = log.then(Instant::now);
    let mut initial_binding = Binding::new(num_vars);
    for atom in atoms {
        for var in atom.args.iter().chain(std::iter::once(&atom.output)) {
            if let FlatVar::Ground(uid) = var {
                initial_binding.set(var_index[var], egraph.find(*uid), *uid);
            }
        }
    }
    if let Some(t) = ib_start {
        let mut pt = egraph.datalog_phase_timers.borrow_mut();
        pt.init_binding_time += t.elapsed();
        pt.init_binding_calls += 1;
    }

    // Dedup helper: canonical key for a binding
    let mut all_bindings = Vec::new();
    // let mut seen: HashSet<Vec<u64>> = HashSet::new();

    let mut add_bindings = |bindings: Vec<Binding>,
                            all_bindings: &mut Vec<Binding>|
                            // seen: &mut HashSet<Vec<u64>>,
                            // egraph: &Egraph,
                            // var_index: &HashMap<FlatVar, usize>| 
                            {
        for b in bindings {
            // let key_vals: Vec<u64> = var_index.keys().into_iter();

            // if seen.insert(key_vals) {
                // debug_println!(
                //     26,
                //     0,
                //     "    new binding: {:?}",
                //     quant_slots
                //         .iter()
                //         .map(|(name, idx)| {
                //             let v = b.slots[*idx];
                //             format!(
                //                 "{}={} (canon={})",
                //                 name,
                //                 egraph.get_term(v),
                //                 egraph.find(v)
                //             )
                //         })
                //         .collect::<Vec<_>>()
                // );
                all_bindings.push(b);
            // }
        }
    };

    if full_pass {
        // Full pass: single join with no delta filtering
        debug_println!(26, 0, "  running full pass (no delta filtering)");
        debug_println!(28, 0, "  --- Full pass (all entries, no delta filtering) ---");
        debug_println!(27, 0, "[matching]  full pass ({} atoms):", atoms.len());
        let fp_start = log.then(Instant::now);
        let pass_t0 = log.then(Instant::now);
        let bindings = execute_join(&order, atoms, None, initial_binding, egraph, &var_index, log);
        if let Some(t0) = pass_t0 {
            debug_println!(27, 0, "[matching]  full pass done: {} bindings, {:.3}ms", bindings.len(), t0.elapsed().as_secs_f64() * 1000.0);
        }
        debug_println!(26, 0, "    join produced {} raw bindings", bindings.len());
        debug_println!(28, 0, "  Full pass produced {} bindings", bindings.len());
        add_bindings(bindings, &mut all_bindings);
        if let Some(t) = fp_start {
            let mut pt = egraph.datalog_phase_timers.borrow_mut();
            pt.full_pass_time += t.elapsed();
            pt.full_pass_calls += 1;
        }
    } else {
        let sn_start = log.then(Instant::now);
        // Semi-naive: check if any atom has delta entries
        let any_has_delta = order
            .iter()
            .any(|&atom_idx| func_has_delta(egraph, &atoms[atom_idx].func));

        if !any_has_delta {
            debug_println!(26, 0, "  no delta entries for any atom, skipping");
            if let Some(t) = sn_start {
                let mut pt = egraph.datalog_phase_timers.borrow_mut();
                pt.semi_naive_time += t.elapsed();
                pt.semi_naive_calls += 1;
            }
            return (vec![], var_index);
        }

        // Run k passes: in pass i, atom at position i uses delta-only
        debug_println!(28, 0, "  --- Semi-naive: {} passes ---", order.len());
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
                debug_println!(28, 0, "  Pass {}/{}: atom[{}] {} -- SKIPPED (no delta)", pos + 1, order.len(), atom_idx, atoms[atom_idx]);
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
            debug_println!(28, 0, "  Pass {}/{}: atom[{}] {} -- delta atom for this pass", pos + 1, order.len(), atom_idx, atoms[atom_idx]);

            debug_println!(27, 0, "[matching]  semi-naive pass {}/{}: delta atom '{}'", pos + 1, order.len(), func);
            let pass_t0 = log.then(Instant::now);
            let bindings =
                execute_join(&order, atoms, Some(pos), initial_binding.clone(), egraph, &var_index, log);
            if let Some(t0) = pass_t0 {
                debug_println!(27, 0, "[matching]  pass {}/{} done: {} bindings, {:.3}ms", pos + 1, order.len(), bindings.len(), t0.elapsed().as_secs_f64() * 1000.0);
            }
            debug_println!(
                26,
                0,
                "    pass {} produced {} raw bindings",
                pos,
                bindings.len()
            );
            debug_println!(28, 0, "    -> pass produced {} bindings", bindings.len());
            add_bindings(bindings, &mut all_bindings);
        }
        if let Some(t) = sn_start {
            let mut pt = egraph.datalog_phase_timers.borrow_mut();
            pt.semi_naive_time += t.elapsed();
            pt.semi_naive_calls += 1;
        }
    }

    debug_println!(26, 0, "  total unique bindings: {}", all_bindings.len());
    debug_println!(28, 0, "  Total unique bindings: {}", all_bindings.len());
    (all_bindings, var_index)
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
    let log = egraph.log_matching_time;
    if log {
        egraph.datalog_phase_timers.borrow_mut().reset();
    }

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
            let quant_start = if crate::log::is_important(28) { Some(Instant::now()) } else { None };

            for atoms in multipatterns {
                // Fast pre-check: skip the quantifier entirely before touching any
                // per-quantifier state if the join is guaranteed to produce no new
                // bindings. Two conditions let us bail out:
                //   1. Some atom has zero entries in the egraph — join is empty.
                //   2. In semi-naive mode, no atom has delta entries — no new
                //      bindings since the last round.
                // This avoids `build_var_index`, `compute_join_order`, and binding
                // allocations for the overwhelming majority of quantifiers in a
                // typical matching round.
                let pc_start = log.then(Instant::now);
                let mut any_zero = false;
                let mut any_delta = false;
                for atom in atoms {
                    let size = table_size(egraph, &atom.func);
                    if size == 0 {
                        any_zero = true;
                        break;
                    }
                    if !*needs_full_pass && func_has_delta(egraph, &atom.func) {
                        any_delta = true;
                    }
                }
                let skip = any_zero || (!*needs_full_pass && !any_delta);
                if let Some(t) = pc_start {
                    let mut pt = egraph.datalog_phase_timers.borrow_mut();
                    pt.precheck_time += t.elapsed();
                    pt.precheck_calls += 1;
                    if skip {
                        pt.precheck_skipped += 1;
                    }
                }
                if skip {
                    debug_println!(
                        26,
                        0,
                        "Skipping quantifier {}: {}",
                        egraph.get_term(*qid),
                        if any_zero { "atom with table_size=0" } else { "no delta entries in semi-naive mode" }
                    );
                    continue;
                }

                debug_println!(
                    26,
                    0,
                    "Matching quantifier {} with {} atoms {:?} (needs_full_pass={})",
                    egraph.get_term(*qid),
                    atoms.len(),
                    atoms,
                    needs_full_pass
                );

                // Level 28: high-level overview of the flattened pattern
                debug_println!(28, 0, "");
                debug_println!(28, 0, "=== Relational Match for quantifier {} ===", egraph.get_term(*qid));
                debug_println!(28, 0, "  Flattened pattern ({} atoms):", atoms.len());
                for (i, atom) in atoms.iter().enumerate() {
                    let has_delta = func_has_delta(egraph, &atom.func);
                    debug_println!(28, 0, "    [{}] {}  {}", i, atom, if has_delta { "<-- DELTA" } else { "" });
                }
                debug_println!(28, 0, "  Mode: {}", if *needs_full_pass { "FULL PASS (new quantifier)" } else { "SEMI-NAIVE" });

                if crate::log::is_important(27) {
                    debug_println!(27, 0, "[matching] quantifier '{}': {} atoms, mode={}",
                        egraph.get_term(*qid), atoms.len(),
                        if *needs_full_pass { "full" } else { "semi-naive" });
                    for (i, atom) in atoms.iter().enumerate() {
                        debug_println!(27, 0, "[matching]   atom[{}]: {} (table_size={})", i, atom, table_size(egraph, &atom.func));
                    }
                }
                let em_start = log.then(Instant::now);
                let (bindings, var_index) = evaluate_multipattern(atoms, *needs_full_pass, egraph, log);
                if let Some(t) = em_start {
                    let mut pt = egraph.datalog_phase_timers.borrow_mut();
                    pt.evaluate_multipattern_time += t.elapsed();
                    pt.evaluate_multipattern_calls += 1;
                }

                debug_println!(28, 0, "  Result: {} total bindings", bindings.len());
                // Show final bindings (quantified variables only) at level 28
                for (bi, binding) in bindings.iter().enumerate().take(10) {
                    let qvars: Vec<String> = var_index.iter()
                        .filter_map(|(var, &idx)| {
                            if let FlatVar::Quantified(name) = var {
                                binding.raw(idx).map(|uid| format!("?{}={}", name, egraph.get_term(uid)))
                            } else {
                                None
                            }
                        })
                        .collect();
                    debug_println!(28, 0, "    [{}] {{ {} }}", bi, qvars.join(", "));
                }
                if bindings.len() > 10 {
                    debug_println!(28, 0, "    ... and {} more", bindings.len() - 10);
                }
                debug_println!(28, 0, "");

                let ex_start = log.then(Instant::now);
                for binding in bindings {
                    let mut assignment = DeterministicHashMap::new();
                    for (var, &idx) in &var_index {
                        if let FlatVar::Quantified(name) = var {
                            if let Some(raw) = binding.raw(idx) {
                                assignment.insert(name.clone(), egraph.get_term(raw));
                            }
                        }
                    }

                    if variables.iter().all(|v| assignment.contains_key(v)) {
                        quant_assignments.push(assignment);
                    }
                }
                if let Some(t) = ex_start {
                    let mut pt = egraph.datalog_phase_timers.borrow_mut();
                    pt.extract_assignments_time += t.elapsed();
                    pt.extract_assignments_calls += 1;
                }
            }

            debug_println!(
                26,
                0,
                "Datalog matcher found {} assignments for quantifier {}",
                quant_assignments.len(),
                egraph.get_term(*qid)
            );
            if let Some(start) = quant_start {
                let quant_elapsed = start.elapsed();
                debug_println!(28, 0, "=== Quantifier {}: {} assignments in {:.3}ms ===",
                    egraph.get_term(*qid), quant_assignments.len(), quant_elapsed.as_secs_f64() * 1000.0);
            }
            results.push((*qid, quant_assignments));
        }
    }

    // Clear needs_full_pass for all quantifiers after the matching round
    for quantifier in &mut egraph.quantifiers {
        quantifier.needs_full_pass = false;
    }

    if log {
        egraph.datalog_phase_timers.borrow().report(egraph.matching_round);
    }

    results
}

/// Increment matching_round after each matching round for semi-naive evaluation.
pub fn datalog_update_watermarks(egraph: &mut Egraph) {
    debug_println!(24, 0, "Incrementing matching_round from {} to {}", egraph.matching_round, egraph.matching_round + 1);
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
