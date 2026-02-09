// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Variable representation at the level of the LRA/LIA solver.

use core::fmt;

use dashu::Rational;
use num_traits::Zero;

use crate::arithmetic::lia::bounds::Bounds;

/// Types of variables
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VarType {
    /// Real (Rational) variable
    Real,
    /// Integer variable
    Int,
}

impl fmt::Display for VarType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VarType::Real => write!(f, "R"),
            VarType::Int => write!(f, "Z"),
        }
    }
}

/// Variable identity; represented by a unique index and a type
///
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Var {
    /// Unique variable id
    pub id: usize,
    /// Variable type (sort)
    pub typ: VarType,
}

impl Var {
    /// Create a new variable
    pub fn new(id: usize, typ: VarType) -> Self {
        Var { id, typ }
    }

    /// Create a real variable
    pub fn real(id: usize) -> Self {
        Var {
            id,
            typ: VarType::Real,
        }
    }

    /// Create a integer variable
    pub fn int(id: usize) -> Self {
        Var {
            id,
            typ: VarType::Int,
        }
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "V({0},{1})", self.id, self.typ)
    }
}

/// Indicated whether a variable is basic or non-basic and which row/col it currently owns
#[derive(Clone, Debug)]
pub enum Owner {
    /// A Basic variable owning a given row
    Basic(/* row */ usize),
    /// A Non-Basic variable owning a given column
    NonBasic(/* col */ usize),
}

impl fmt::Display for Owner {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Owner::Basic(r) => write!(f, "Basic({r})"),
            Owner::NonBasic(c) => write!(f, "NonBasic({c})"),
        }
    }
}

/// Variable information used in simplex operations and integer solving.
///
/// VarInfo contains an `order` field, which should be unique across all variables.
/// There are used in several of the algorithms inside the solver.
///
/// TODO: add variable type
///
/// Example:
///
/// ```
/// use std::cmp;
/// use sundance_smt::arithmetic::lia::variables::*;
/// let x = VarInfo::dummy(0);
/// let y = VarInfo::dummy(1);
/// assert_eq!(x.cmp(&y), cmp::Ordering::Less);
/// ```
///
/// Variables contain a currently assigned value and bounds:
///
/// ```
/// use sundance_smt::arithmetic::lia::variables::*;
/// use dashu::rbig;
/// let mut x = VarInfo::dummy(0);
/// x.update_assignment(rbig!(1/3));
/// assert!(x.in_bounds());
/// x.update_lower(2);
/// assert!(!x.in_bounds());
/// ```
///
#[derive(Clone, Debug)]
pub struct VarInfo<T> {
    /// Variable whose info is represented
    pub var: Var,
    /// current value assigned to the variable
    pub val: T,
    /// current bounds placed on the variable
    pub bounds: Bounds<T>,
    /// basic or non-basic variable and row/col ownership
    pub owner: Owner,
}

impl<T> fmt::Display for VarInfo<T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "({0}, val={1}, {2}, {3})",
            self.var, self.val, self.bounds, self.owner
        )
    }
}

/// Variables are equal if and only if their `id`s are equal
impl<T> PartialEq for VarInfo<T> {
    fn eq(&self, other: &Self) -> bool {
        self.get_id() == other.get_id()
    }
}

impl<T> Eq for VarInfo<T> {}

/// Variables are ordered by their `var` field
///
/// Note: `Var` is currently ordered lexicographically (by derive) by `id` and `VarType`. In
/// practice variable id's are unique so the type never comes into play.
impl<T> Ord for VarInfo<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.var.cmp(&other.var)
    }
}

impl<T> PartialOrd for VarInfo<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: Zero> VarInfo<T> {
    /// Allocate a new variable, assigned to zero and unbounded
    pub fn new(var: Var, owner: Owner) -> Self {
        Self {
            var,
            val: T::zero(),
            bounds: Bounds::unbounded(),
            owner,
        }
    }

    /// Replace bounds with the ones given
    pub fn with_bounds(self, b: Bounds<T>) -> Self {
        Self { bounds: b, ..self }
    }

    /// Replace val with the one given
    pub fn with_val(self, v: T) -> Self {
        Self { val: v, ..self }
    }
}

impl<T> VarInfo<T> {
    /// Returns the variable id
    pub fn get_id(&self) -> usize {
        self.var.id
    }

    /// Returns Some(row) if the variable is basic and owns `row`
    pub fn is_basic(&self) -> Option<usize> {
        match self.owner {
            Owner::Basic(r) => Some(r),
            _ => None,
        }
    }

    /// Returns Some(col) if the variable is basic and owns `col`
    pub fn is_non_basic(&self) -> Option<usize> {
        match self.owner {
            Owner::NonBasic(c) => Some(c),
            _ => None,
        }
    }
}
impl<T: Ord> VarInfo<T> {
    /// Determine if the current assignment satisfies the bounds
    pub fn in_bounds(&self) -> bool {
        self.bounds.in_bounds(&self.val)
    }

    /// Determine if the current assignment is at the variable's lower bound
    ///
    /// ```
    /// use sundance_smt::arithmetic::lia::bounds::*;
    /// use sundance_smt::arithmetic::lia::variables::*;
    /// use dashu::rbig;
    ///
    /// let mut y = VarInfo::dummy(0).with_bounds(Bounds::above_of(10));
    /// assert!(!y.at_upper()); // y = 0 is not +inf
    /// y.update_assignment(10);
    /// assert!(!y.at_upper()); // y = 10 is still not +inf
    /// y.bounds.upper = Some(rbig!(10));
    /// assert!(y.at_upper());
    /// ```
    pub fn at_upper(&self) -> bool {
        self.bounds.upper.as_ref().is_some_and(|u| u == &self.val)
    }

    /// Determine if the current assignment is at the variable's lower bound
    ///
    /// ```
    /// use sundance_smt::arithmetic::lia::bounds::*;
    /// use sundance_smt::arithmetic::lia::variables::*;
    /// use dashu::rbig;
    ///
    /// // x = 0 with bounds [0, 10]
    /// let mut x = VarInfo::dummy(0)
    ///   .with_bounds(Bounds::new(Some(rbig!(0)), Some(rbig!(10))));
    /// assert!(x.at_lower());
    /// x.update_assignment(10);
    /// assert!(!x.at_lower());
    /// x.bounds.lower = Some(rbig!(10));
    /// assert!(x.at_lower());
    /// ```
    pub fn at_lower(&self) -> bool {
        self.bounds.lower.as_ref().is_some_and(|l| l == &self.val)
    }

    /// Check if the variable assignment is below the lower bound
    /// ```
    /// use sundance_smt::arithmetic::lia::variables::*;
    ///
    /// let mut x = VarInfo::dummy(0);
    /// assert!(!x.below_lower());
    /// x.update_lower(1);
    /// assert!(x.below_lower()); // x = 0 < 1
    /// x.update_assignment(2);
    /// assert!(!x.below_lower()); // x = 2 > 1
    /// ```
    pub fn below_lower(&self) -> bool {
        self.bounds.lower.as_ref().is_some_and(|l| &self.val < l)
    }

    /// Check if the variable assignment is above the upper bound
    pub fn above_upper(&self) -> bool {
        self.bounds.upper.as_ref().is_some_and(|u| &self.val > u)
    }

    /// Update the current assignment
    pub fn update_assignment(&mut self, val: impl Into<T>) {
        self.val = val.into()
    }

    /// Update the current lower bound
    pub fn update_lower(&mut self, lower: impl Into<T>) {
        self.bounds.lower = Some(lower.into())
    }

    /// Update the current upper bound
    pub fn update_upper(&mut self, upper: impl Into<T>) {
        self.bounds.upper = Some(upper.into())
    }
}

impl VarInfo<Rational> {
    /// Create a new dummy variable with given id
    ///
    /// Dummy variables should only be used in tests and the like.
    pub fn dummy(id: usize) -> Self {
        VarInfo::new(Var::real(id), Owner::Basic(0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arithmetic::lia::types::Rational;

    #[test]
    fn update_lower() {
        let mut v = VarInfo::<Rational>::new(Var::real(0), Owner::Basic(0));
        assert!(v.in_bounds());
        v.update_lower(10);
        assert!(!v.in_bounds());
    }

    #[test]
    fn update_val() {
        let mut v = VarInfo::<Rational>::new(Var::real(0), Owner::Basic(0));
        assert!(v.in_bounds());
        v.update_assignment(10);
        assert!(v.in_bounds());
        v.update_upper(-10);
        assert!(!v.in_bounds());
    }
}
