// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Results and errors related to tableau operations

use std::collections::{BTreeMap, BTreeSet};
use std::error;
use std::fmt;

use dashu::Rational;

use crate::arithmetic::lia::tableau::TableauError;
use crate::arithmetic::lia::variables::{Var, VarInfo};

/// Generic error type for solver operations
#[derive(Debug)]
pub struct SolverError(pub String);
impl fmt::Display for SolverError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl error::Error for SolverError {}

impl From<TableauError> for SolverError {
    fn from(err: TableauError) -> Self {
        SolverError(format!("TableauError: {}", err))
    }
}

/// Generic simplex result
pub type SolverResult<T> = Result<T, SolverError>;

/// Variable assignments, returned after finding a solution
///
/// T is the type representing arithmetic literals; typically either [Var] or [Term]
#[derive(Debug, PartialEq, Eq)]
pub struct Assignment<T: Ord>(BTreeMap<T, Rational>);

impl<T: Ord + Eq> Assignment<T> {
    /// Create a new assignment
    pub fn new(assignments: BTreeMap<T, Rational>) -> Self {
        Self(assignments)
    }

    /// Return number of variables in the assignment
    pub fn nvars(&self) -> usize {
        self.0.len()
    }

    /// Get the value assigned to a variable
    pub fn get(&self, var: &T) -> Option<&Rational> {
        self.0.get(var)
    }

    /// Iterate over the variables and their values in an assignment
    pub fn iter(&self) -> std::collections::btree_map::Iter<'_, T, Rational> {
        self.0.iter()
    }
}

impl Assignment<Var> {
    /// Convert from a Vec<VarInfo<Rational>> to an Assignment
    /// This is a helper method for backward compatibility during refactoring
    pub fn from_var_info(var_infos: Vec<VarInfo<Rational>>) -> Self {
        let mut assignments = BTreeMap::new();
        for var_info in var_infos {
            assignments.insert(var_info.var, var_info.val);
        }
        Self(assignments)
    }
}

impl<T: Ord> IntoIterator for Assignment<T> {
    type Item = (T, Rational);
    type IntoIter = std::collections::btree_map::IntoIter<T, Rational>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<T: fmt::Display + Ord> fmt::Display for Assignment<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut first = true;
        for (var, val) in &self.0 {
            if !first {
                writeln!(f)?;
            }
            write!(f, "({}, val={})", var, val)?;
            first = false;
        }
        Ok(())
    }
}

/// Represent a conflict; a subset of the asserted theory literals
///
/// This is mostly a container for a type representing literals (could be Var, Term, ...)
/// and a resolution algorithm.
///
/// BTreeSet is used because reporting conflicts downstream needs to be in a deterministic order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Conflict<T>(BTreeSet<T>);

type ConflictIter<'a, T> = std::collections::btree_set::Iter<'a, T>;

impl<T: Ord + Clone> Conflict<T> {
    /// Create a new [Conflict]
    ///
    /// Use `collect::<T>` to construct a new conflict from an iterator
    pub fn new() -> Self {
        Self(BTreeSet::new())
    }

    /// Construct conflicts from a set
    pub fn from_set(set: BTreeSet<T>) -> Self {
        Conflict(set)
    }

    /// Return an [Iter] over the conflict basic_vars
    pub fn iter(&self) -> ConflictIter<'_, T> {
        self.0.iter()
    }

    /// Return the number of basic_vars in the conflict
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Determine if the conflict set is empty
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Determine if a conflict contains the given element
    pub fn contains(&self, var: &T) -> bool {
        self.0.contains(var)
    }

    /// Add an element to the conflict set
    pub fn insert(&mut self, var: T) -> bool {
        self.0.insert(var)
    }

    /// Remove an element to the conflict set
    pub fn remove(&mut self, var: &T) -> bool {
        self.0.remove(var)
    }

    /// Union conflict sets
    pub fn union(&self, other: &Self) -> Self {
        Self(self.0.union(&other.0).cloned().collect())
    }

    /// Resolve two conflict sets relative to a literal corresponding to `var`.
    ///
    /// The basic logic is:
    /// 1. if one of the conflict sets doesn't contain `var`, return it
    /// 2. if they both contain var, then return (self \union other) \ {var}
    pub fn resolve(&self, var: T, other: &Self) -> Self {
        // TODO: Conflict::resolve: optimization when !other.contains(var) && other.len() < self.len()
        if !self.contains(&var) {
            self.clone()
        } else if !other.contains(&var) {
            other.clone()
        } else {
            let mut union: BTreeSet<T> = self.0.union(&other.0).cloned().collect();
            union.remove(&var);
            Conflict::from_set(union)
        }
    }

    // TODO: Conflict: add linear reduction method?
    // TODO: Conflict: add better reduction, e.g. quickXplain?
}

impl<T: Copy + Ord> Default for Conflict<T> {
    fn default() -> Self {
        Conflict::new()
    }
}

impl<T: Ord> FromIterator<T> for Conflict<T> {
    fn from_iter<U: IntoIterator<Item = T>>(iter: U) -> Self {
        Conflict(iter.into_iter().collect::<BTreeSet<T>>())
    }
}

/// High level decision of the general simplex algorithm
#[derive(Debug, PartialEq, Eq)]
pub enum SolverDecision {
    /// Simplex is in-progress
    UNKNOWN,
    /// The original linear real arithmetic problem is sat
    /// TODO: make model construction lazy
    FEASIBLE(Assignment<Var>),
    /// The original linear real arithmetic problem is UNSAT
    INFEASIBLE(Conflict<Var>),
}

impl Default for SolverDecision {
    fn default() -> Self {
        Self::UNKNOWN
    }
}

/// Return a default model for a set of variable id's
///
/// TODO: default_model: leaving in place until there's a better model type
pub fn default_model<T: Ord>(vars: impl Iterator<Item = T>) -> Assignment<T> {
    let mut assignments = BTreeMap::new();
    for var in vars {
        assignments.insert(var, Rational::ZERO);
    }
    Assignment::new(assignments)
}
