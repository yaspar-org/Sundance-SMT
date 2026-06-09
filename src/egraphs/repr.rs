// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Internal term representation for the Sundance egraph.
//! These types are specific to our egraph implementation, not part of the generic trait.

use yaspar_ir::ast::Str;

/// Operator type for congruence closure.
/// Two terms are congruent iff they have the same Op and pairwise-equal children.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Op {
    /// Uninterpreted function application
    App(Str),
    /// Equality (=)
    Eq,
    /// If-then-else
    Ite,
    /// Negation
    Not,
    /// Conjunction
    And,
    /// Disjunction
    Or,
    /// Implication
    Implies,
    /// Distinct
    Distinct,
    /// Pattern variable (only used in e-matching, never registered)
    Local(String),
    /// Global constant (variable name)
    Constant(Str),
}

impl Op {
    /// Convert to the string key used in function_maps.
    pub fn to_function_map_key(&self) -> String {
        match self {
            Op::App(s) => s.get().to_string(),
            Op::Eq => "=".to_string(),
            Op::Ite => "ite".to_string(),
            Op::Not => "not".to_string(),
            Op::And => "and".to_string(),
            Op::Or => "or".to_string(),
            Op::Implies => "=>".to_string(),
            Op::Distinct => "distinct".to_string(),
            Op::Local(_) => String::new(),
            Op::Constant(s) => s.get().to_string(),
        }
    }
}

/// Children of a term, stored inline for common arities to avoid heap allocation.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Children {
    Arity0,
    Arity1([u64; 1]),
    Arity2([u64; 2]),
    Arity3([u64; 3]),
    Arity4([u64; 4]),
    Arity5([u64; 5]),
    Arity6([u64; 6]),
    ArityN(Vec<u64>),
}

impl Children {
    pub fn from_slice(children: &[u64]) -> Self {
        match children.len() {
            0 => Children::Arity0,
            1 => Children::Arity1([children[0]]),
            2 => Children::Arity2([children[0], children[1]]),
            3 => Children::Arity3([children[0], children[1], children[2]]),
            4 => Children::Arity4([children[0], children[1], children[2], children[3]]),
            5 => Children::Arity5([children[0], children[1], children[2], children[3], children[4]]),
            6 => Children::Arity6([children[0], children[1], children[2], children[3], children[4], children[5]]),
            _ => Children::ArityN(children.to_vec()),
        }
    }

    pub fn as_slice(&self) -> &[u64] {
        match self {
            Children::Arity0 => &[],
            Children::Arity1(a) => a,
            Children::Arity2(a) => a,
            Children::Arity3(a) => a,
            Children::Arity4(a) => a,
            Children::Arity5(a) => a,
            Children::Arity6(a) => a,
            Children::ArityN(v) => v,
        }
    }

    pub fn len(&self) -> usize {
        match self {
            Children::Arity0 => 0,
            Children::Arity1(_) => 1,
            Children::Arity2(_) => 2,
            Children::Arity3(_) => 3,
            Children::Arity4(_) => 4,
            Children::Arity5(_) => 5,
            Children::Arity6(_) => 6,
            Children::ArityN(v) => v.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        matches!(self, Children::Arity0)
    }
}

/// Internal representation of a term stored in the egraph.
#[derive(Debug, Clone)]
pub struct TermEntry {
    pub op: Op,
    pub children: Children,
}
