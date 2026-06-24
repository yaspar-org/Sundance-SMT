// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Trait specifying common behavior for low-level tableaux

use crate::arithmetic::lia::tableau_dense::TableauDense;
use crate::arithmetic::lia::tableau_sparse::TableauSparse;
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

/// Selector for which tableau implementation to use at runtime.
#[derive(Debug, Clone, Copy)]
pub enum TableauKind {
    /// Dense tableau backed by a 2D array
    Dense,
    /// Sparse tableau backed by a sparse matrix
    Sparse,
}

/// Tableau represents a low level tableau.
///
/// Tableau logically provides a 2d array of rationals that can be pivoted on selected
/// rows/columns and inspected. It doesn't support arbitrary modification. The
/// underlying array implementation is private.
pub trait Tableau
where
    Self: fmt::Debug + Sized,
{
    /// Construct a tableau from a vector of (row, col, value) tuples.
    fn from_tuples(
        nrows: usize,
        ncols: usize,
        t: Vec<(usize, usize, Rational)>,
    ) -> TableauResult<Self>;

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

    /// Return the number of rows in the tableau
    fn nrows(&self) -> usize;

    /// Return the number of columns in the tableau
    fn ncols(&self) -> usize;

    /// Return the number of non-zero entries in the given column
    fn col_nnz(&self, col: usize) -> usize {
        (0..self.nrows())
            .filter(|r| self.get(*r, col).is_ok_and(|v| !v.is_zero()))
            .count()
    }
}

/// Enum-dispatched tableau that selects between dense and sparse at runtime.
#[derive(Debug, Clone)]
pub enum TableauImpl {
    /// Dense tableau variant
    Dense(TableauDense),
    /// Sparse tableau variant
    Sparse(TableauSparse),
}

/// Equality on tableau is only directly implemented for the Dense variant. To compare sparse
/// tableau with dense or with each other we convert to dense first. This is potentially expensive
/// and should only be needed/used in testing.
impl PartialEq for TableauImpl {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (TableauImpl::Dense(a), TableauImpl::Dense(b)) => a == b,
            (TableauImpl::Dense(a), TableauImpl::Sparse(b)) => *a == b.to_dense(),
            (TableauImpl::Sparse(a), TableauImpl::Dense(b)) => a.to_dense() == *b,
            (TableauImpl::Sparse(a), TableauImpl::Sparse(b)) => a.to_dense() == b.to_dense(),
        }
    }
}

impl Eq for TableauImpl {}

impl Tableau for TableauImpl {
    fn from_tuples(
        nrows: usize,
        ncols: usize,
        t: Vec<(usize, usize, Rational)>,
    ) -> TableauResult<Self> {
        // Default to sparse; use TableauImpl::new() for runtime selection
        Ok(TableauImpl::Sparse(TableauSparse::from_tuples(
            nrows, ncols, t,
        )?))
    }

    fn pivot(&mut self, row: usize, col: usize) -> TableauResult<()> {
        match self {
            TableauImpl::Dense(t) => t.pivot(row, col),
            TableauImpl::Sparse(t) => t.pivot(row, col),
        }
    }

    fn get(&self, row: usize, col: usize) -> TableauResult<&Rational> {
        match self {
            TableauImpl::Dense(t) => t.get(row, col),
            TableauImpl::Sparse(t) => t.get(row, col),
        }
    }

    fn nrows(&self) -> usize {
        match self {
            TableauImpl::Dense(t) => t.nrows(),
            TableauImpl::Sparse(t) => t.nrows(),
        }
    }

    fn ncols(&self) -> usize {
        match self {
            TableauImpl::Dense(t) => t.ncols(),
            TableauImpl::Sparse(t) => t.ncols(),
        }
    }

    fn col_nnz(&self, col: usize) -> usize {
        match self {
            TableauImpl::Dense(t) => t.col_nnz(col),
            TableauImpl::Sparse(t) => t.col_nnz(col),
        }
    }
}

impl TableauImpl {
    /// Construct a TableauImpl of the given kind from tuples.
    pub fn new(
        kind: TableauKind,
        nrows: usize,
        ncols: usize,
        t: Vec<(usize, usize, Rational)>,
    ) -> TableauResult<Self> {
        match kind {
            TableauKind::Dense => Ok(TableauImpl::Dense(TableauDense::from_tuples(
                nrows, ncols, t,
            )?)),
            TableauKind::Sparse => Ok(TableauImpl::Sparse(TableauSparse::from_tuples(
                nrows, ncols, t,
            )?)),
        }
    }
}
