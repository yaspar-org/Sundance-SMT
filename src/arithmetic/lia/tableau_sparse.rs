// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! This module implements a sparse tableaux for use in the linear real arithmetic simplex
//! algorithm.
//!
//! The idea is that when the underlying tableau matrix has a very small number of non-zero
//! entries, a sparse matrix is much more efficient at doing critical operations like pivoting
//! which the simplex solver performs on every step.
//!
//! The intuition is that most arithmetic problems arising in SMT, and in program verification in
//! particular, have very few non-zero coefficients compared to the number of variables and
//! relations. In some examples the density of non-zero entries is ~5-10%. Simple benchmarking
//! shows for some specific problems with ~5% density the sparse implementation is >20x faster than
//! the dense one.
//!
//! The tradeoff is that the spare implementation is considerably more complicated and harder to
//! debug. See [crate::arithmetic::lia::sparse].

use crate::arithmetic::lia::sparse;
use crate::arithmetic::lia::tableau::{Tableau, TableauError, TableauResult};
use crate::arithmetic::lia::types::Rational;

/// [TableauSparse] wraps a sparse matrix over the [Rational]s and implements
/// the [Tableau] interface.
#[allow(dead_code)]
#[derive(Debug)]
pub struct TableauSparse {
    matrix: sparse::Matrix<Rational>,
}

impl TableauSparse {
    /// Make a new Tableau from a vector of tuples (row, col, value).
    pub fn from_tuples(
        nrows: usize,
        ncols: usize,
        t: Vec<(usize, usize, Rational)>,
    ) -> TableauResult<Self> {
        let matrix = sparse::Matrix::from_tuples(nrows, ncols, t).map_err(|e| TableauError(e.0))?;
        Ok(TableauSparse { matrix })
    }

    /// Return the number of rows in the tableau (= number of basic variables)
    pub fn nrows(&self) -> usize {
        self.matrix.nrows()
    }

    /// Return the number of columns in the tableau (= number of basic + non-basic variables)
    pub fn ncols(&self) -> usize {
        self.matrix.ncols()
    }
}

impl Tableau for TableauSparse {
    fn pivot(&mut self, row: usize, col: usize) -> TableauResult<()> {
        self.matrix.pivot(row, col).map_err(|e| TableauError(e.0))
    }

    fn get(&self, row: usize, col: usize) -> TableauResult<&Rational> {
        self.matrix
            .get(row, col)
            .ok_or_else(|| TableauError(format!("Index out of bounds: ({}, {})", row, col)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arithmetic::lia::types::rbig;

    // Validate construction of a 3x2 sparse tableau from tuples
    #[test]
    fn from_tuples_3x2() {
        let tuples = vec![
            (0, 0, rbig!(1)),
            (0, 1, rbig!(1)),
            (1, 0, rbig!(2)),
            (1, 1, rbig!(-1)),
            (2, 0, rbig!(-1)),
            (2, 1, rbig!(2)),
        ];
        let tab = TableauSparse::from_tuples(3, 2, tuples).unwrap();

        assert_eq!(tab.nrows(), 3);
        assert_eq!(tab.ncols(), 2);
        assert_eq!(*tab.get(0, 0).unwrap(), rbig!(1));
        assert_eq!(*tab.get(0, 1).unwrap(), rbig!(1));
        assert_eq!(*tab.get(1, 0).unwrap(), rbig!(2));
        assert_eq!(*tab.get(1, 1).unwrap(), rbig!(-1));
        assert_eq!(*tab.get(2, 0).unwrap(), rbig!(-1));
        assert_eq!(*tab.get(2, 1).unwrap(), rbig!(2));
    }
}
