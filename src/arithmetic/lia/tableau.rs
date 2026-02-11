// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Trait specifying common behavior for low-level tableaux

use crate::arithmetic::lia::types::Rational;
use std::error;
use std::fmt;

/// Generic error type for tableau operations
#[derive(Debug)]
pub struct TableauError(pub String);
impl fmt::Display for TableauError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl error::Error for TableauError {}

impl From<array2d::Error> for TableauError {
    fn from(err: array2d::Error) -> Self {
        TableauError(format!("{}", err))
    }
}

/// Generic result type for tableau operations
pub type TableauResult<T> = Result<T, TableauError>;
/// Tableau represents a low level tableau.
///
/// Tableau logically provides a 2d array of rationals that can be pivoted on selected
/// rows/columns and inspected. It doesn't support arbitrary modification. The
/// underlying array implementation is private.
pub trait Tableau
where
    Self: fmt::Debug + Sized,
{
    /// Pivoting exchanges a row owning variable for a column owning variable by solving
    /// the row equation for the column variable (forms the new row) and then substituting
    /// all other occurrences of the column variable with the solution.
    ///
    /// `self` is modified by this method.
    ///
    /// Returns Ok(()) if the pivot was successful (i.e. when `tableau[row][col] != 0`) and an
    /// error otherwise.
    fn pivot(&mut self, row: usize, col: usize) -> TableauResult<()>;

    /// Get an element of the tableau
    fn get(&self, row: usize, col: usize) -> TableauResult<&Rational>;
}
