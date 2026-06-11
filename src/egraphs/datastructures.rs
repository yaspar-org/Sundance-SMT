// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Important datastructures that are used elsewhere
use std::{cmp::Ordering, fmt};

use yaspar_ir::ast::{QualifiedIdentifier, Str, Term};

/// Keeps track of disequalities used between multiple terms
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DisequalTerm {
    pub term: u32,
    pub level: usize,
    pub diseq_lit: i32,
    pub hash: u32,
    pub original_disequality: (u32, u32),
}

impl fmt::Display for DisequalTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "DisequalTerm(term: {}, level: {}, hash: {}, original_disequality: {:?})",
            self.term, self.level, self.hash, self.original_disequality
        )
    }
}

/// Identifies the "operator" of a canonical term form for the purposes of
/// congruence-closure lookup. Replaces a previous `String`-based encoding.
///
/// For App terms, carries the full `QualifiedIdentifier` (symbol + indices +
/// optional sort), which is required to distinguish polymorphic constructor
/// instances like `(as nil (List Int))` vs `(as nil (List Bool))`. Hashing
/// and equality are cheap because the inner `Str` and `Sort` types are
/// hash-consed and hash/compare by uid.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CanonicalOp {
    App(String),
    Eq,
    Ite,
}

/// The canonical form of a term, produced by `Egraph::get_canonical_form`.
///
/// Represents how the term looks after walking each subterm's union-find root,
/// which is what congruence closure uses to detect "same operator, same
/// equivalent arguments" matches between two terms.
#[derive(Debug, Clone)]
pub struct CanonicalForm {
    /// Raw uids of the term's subterms (not canonicalized). Used to build
    /// pairwise term equalities for the congruence proof.
    pub original_subterms: Vec<u32>,
    /// The operator (function name / Eq / Ite).
    pub op: CanonicalOp,
    /// The union-find roots of each subterm. Together with `op` these form
    /// the congruence key — two terms with the same `op` and `canonical_subterms`
    /// must be equal by congruence.
    pub canonical_subterms: Vec<u32>,
}

/// Represents a predecessor of a term
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Predecessor {
    pub level: usize,
    pub hash: u32,
    pub predecessor: u32,
    pub inner_term: u32,
}

impl Ord for Predecessor {
    fn cmp(&self, other: &Self) -> Ordering {
        self.level.cmp(&(other.level))
    }
}

impl PartialOrd for Predecessor {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Represents an assertion that we may need to process
#[derive(Debug, Clone, PartialEq)]
pub enum Assertion {
    Equality {
        t1: u64,
        t2: u64,
        level: usize,
        hash: u32,
    },
    Disequality {
        t1: u64,
        t2: u64,
        level: usize,
        hash: u32,
    },
    Distinct {
        terms: Vec<u64>,
        level: usize,
        hash: u32,
    },
    // ConstructorEquality {
    //     ctor_name: String,
    //     terms: Vec<Term>,
    //     constructor_term: Term,
    //     equal_term: Term,
    //     equality: Term,
    //     level: usize
    // },
    // ConstructorMultiEquality { // todo: I need to think about whether this case can be forced into constructorEquality
    //     ctor_name1: String,
    //     term1: Term,
    //     terms1: Vec<Term>,
    //     ctor_name2: String,
    //     term2: Term,
    //     terms2: Vec<Term>,
    //     equality: Term,
    //     level: usize
    // },
    Tester {
        // todo: change the following to Str
        ctor_name: Str,
        inner_term: Term,
        term: Term,
    },
    Other,
}

/// Represents a Datatype Type
pub enum ConstructorType {
    Uninitialized,
    // NonDatatype,
    Constructor {
        name: Str,
        tester_term: Term,
        level: usize,
        hash: u32,
    },
}

// TODO: the Level here is probalby not needed
// since we are not adding fixed literals anywhere
// we can probably remove this
// #[derive(Debug,Clone,PartialEq, Copy)]
// pub struct Level {
//     pub fixed: bool,
//     pub level: usize
// }

#[derive(Debug, Clone, PartialEq)]
pub struct Quantifier {
    pub triggers: Vec<Vec<crate::egraphs::repr::PatternId>>,
    pub variables: Vec<String>,
    pub body: u64,
    pub id: u64,
    pub guard: Option<u64>, // term that is required in order to instantiate the quantifier
    pub polarity: Polarity, // keep track of whether it is a universal or existential quantifier
    pub skolemized: bool,   // keeps track if the quantifier has been skolemized yet
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Polarity {
    Universal,
    Existential,
}

/// An enum representing different states of a term
#[derive(Debug, Clone, PartialEq)]
pub enum TermOption {
    /// No term is present
    None,
    /// A term is present and initialized
    Some(Term),
    /// A term is present but uninitialized
    Uninitialized(Term),
}

impl TermOption {
    /// Unwraps the term value, assuming the enum is Some or Uninitialized
    ///
    /// # Panics
    ///
    /// This function will panic if the enum is `None`
    pub fn unwrap(self) -> Term {
        match self {
            TermOption::Some(term) => term,
            TermOption::Uninitialized(term) => term,
            TermOption::None => panic!("called `TermOption::unwrap()` on a `None` value"),
        }
    }

    pub fn is_none(&self) -> bool {
        matches!(self, TermOption::None)
    }

    pub fn display(&self) -> String {
        match self {
            TermOption::Some(term) => term.to_string(),
            TermOption::Uninitialized(term) => term.to_string(),
            TermOption::None => "None".to_string(),
        }
    }
}

impl fmt::Display for TermOption {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.display())
    }
}
