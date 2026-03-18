// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use yaspar_ir::ast::ATerm::*;
use yaspar_ir::ast::{Repr, Term};

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
        // Quantifier-bound variable: no atoms, just return the variable.
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

        // Function application: recursively flatten args, then emit one atom.
        App(func, args, _) => {
            let func_indices = &func.0.indices;
            let func_name = if func_indices.is_empty() {
                func.id_str().get().clone()
            } else {
                // "is" constructor test, e.g. ((_ is Cons) x)
                debug_assert_eq!(*func.id_str().get(), "is".to_string());
                debug_assert_eq!(func_indices.len(), 1);
                format!("(is {})", func_indices[0])
            };

            flatten_application(func_name, args.iter().collect(), quant_vars, fresh_counter)
        }

        // ITE is treated like a ternary function application.
        Ite(b, t1, t2) => flatten_application(
            "ite".to_string(),
            vec![b, t1, t2],
            quant_vars,
            fresh_counter,
        ),

        // Equality is treated like a binary function application.
        Eq(left, right) => flatten_application(
            "=".to_string(),
            vec![left, right],
            quant_vars,
            fresh_counter,
        ),

        // Not is treated like a unary function application.
        Not(t) => flatten_application("not".to_string(), vec![t], quant_vars, fresh_counter),

        // Ground terms (constants and globals): no atoms, return a ground variable.
        Constant(..) | Global(..) => (vec![], FlatVar::Ground(term.uid())),

        other => panic!(
            "Unexpected term variant in pattern during flattening: {:?}",
            other
        ),
    }
}

/// Helper: flatten a function-like application with the given name and arguments.
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
///
/// Takes the trigger patterns (outer = disjunctive multipatterns,
/// inner = conjunctive patterns within a multipattern) and the quantifier variable names.
///
/// Returns a `Vec<Vec<FlatAtom>>`: one inner Vec per disjunctive multipattern,
/// containing all the flattened atoms for that multipattern's conjunctive patterns.
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
