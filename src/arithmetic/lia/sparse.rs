// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Sparse matrix implementation using mirrored row/column FxHashMaps.
//!
//! Each entry (i, j, v) is stored in both `rows[i]` and `cols[j]`, enabling
//! O(1) access by either row or column. This is the pattern used by most SMT
//! simplex implementations (Yices2, Z3, CVC5).

use num_traits::Zero;
use rustc_hash::FxHashMap;
use std::error;
use std::fmt;

/// Generic error type for sparse matrix operations
#[derive(Debug, PartialEq, Eq)]
pub struct SparseError(pub String);
impl fmt::Display for SparseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl error::Error for SparseError {}

/// Generic result type for sparse matrix operations
pub type SparseResult<T> = Result<T, SparseError>;

/// Sparse matrix stored as row vectors with a mirrored column index.
///
/// Both `rows[i]` and `cols[j]` store the same coefficient for entry (i, j),
/// enabling O(1) access by either row or column during pivot operations.
#[derive(Clone)]
pub struct Matrix<V> {
    rows: Vec<FxHashMap<usize, V>>, // rows[i]: col -> coefficient
    cols: Vec<FxHashMap<usize, V>>, // cols[j]: row -> coefficient
    zero: V,
}

impl<V: fmt::Debug + Zero + Clone> fmt::Debug for Matrix<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        writeln!(f, "Matrix {}x{}:", self.nrows(), self.ncols())?;
        for (i, row) in self.rows.iter().enumerate() {
            write!(f, "  row {i}: ")?;
            let mut entries: Vec<_> = row.iter().collect();
            entries.sort_by_key(|(col, _)| *col);
            for (col, val) in entries {
                write!(f, "({col}, {val:?}) ")?;
            }
            writeln!(f)?;
        }
        Ok(())
    }
}

impl<V: Zero + Clone + fmt::Debug> Matrix<V> {
    /// Create a new sparse zero matrix of nrows x ncols.
    pub fn new(nrows: usize, ncols: usize) -> SparseResult<Self> {
        if nrows == 0 || ncols == 0 {
            return Err(SparseError("nrows and ncols must be > 0".to_string()));
        }
        Ok(Self {
            rows: vec![FxHashMap::default(); nrows],
            cols: vec![FxHashMap::default(); ncols],
            zero: V::zero(),
        })
    }

    /// Create a new sparse matrix from a vector of tuples (row, col, value).
    ///
    /// Returns an error if any tuple contains row or col indices out of bounds.
    /// Zero values are not inserted.
    pub fn from_tuples(
        nrows: usize,
        ncols: usize,
        t: Vec<(usize, usize, V)>,
    ) -> SparseResult<Self> {
        let mut matrix = Self::new(nrows, ncols)?;
        for (row, col, value) in t {
            if !value.is_zero() {
                matrix.update_or_insert(row, col, value)?;
            }
        }
        Ok(matrix)
    }

    /// Return the number of rows in the matrix.
    pub fn nrows(&self) -> usize {
        self.rows.len()
    }

    /// Return the number of columns in the matrix.
    pub fn ncols(&self) -> usize {
        self.cols.len()
    }

    /// Get the value of an element in the matrix.
    ///
    /// Returns `Some(&zero)` if the element coordinates are in-bounds but no
    /// entry exists. Returns `None` if the indices are out of bounds.
    pub fn get(&self, row: usize, col: usize) -> Option<&V> {
        if row >= self.rows.len() || col >= self.cols.len() {
            return None;
        }
        Some(self.rows[row].get(&col).unwrap_or(&self.zero))
    }

    /// Insert or update an entry in the matrix.
    ///
    /// If `val` is zero, the entry is removed (maintaining sparsity).
    /// Returns `Ok(true)` if an existing entry was updated, `Ok(false)` if a
    /// new entry was inserted. Returns `Err` if indices are out of bounds.
    ///
    /// This is an O(1) operation.
    pub fn update_or_insert(&mut self, row: usize, col: usize, val: V) -> SparseResult<bool> {
        self.validate_row_col(row, col)?;

        if val.is_zero() {
            let existed = self.rows[row].remove(&col).is_some();
            self.cols[col].remove(&row);
            return Ok(existed);
        }

        let existed = self.rows[row].contains_key(&col);
        self.rows[row].insert(col, val.clone());
        self.cols[col].insert(row, val);
        Ok(existed)
    }

    /// Return the number of non-zero entries in the given column.
    pub fn col_nnz(&self, col: usize) -> usize {
        self.cols.get(col).map_or(0, |c| c.len())
    }

    /// Perform a pivot operation on the NxM matrix at the specified row and column.
    ///
    /// The pivot transforms matrix elements according to:
    ///
    /// - Pivot element: a -> 1/a
    /// - Pivot row (non-pivot col): b -> -b/a
    /// - Pivot column (non-pivot row): c -> c/a
    /// - Other elements: d -> d - b*c/a (where b is from the original pivot row, c from pivot col)
    ///
    /// Entries that become zero are removed from the sparse representation.
    pub fn pivot(&mut self, row: usize, col: usize) -> SparseResult<()>
    where
        V: std::ops::Div<Output = V>
            + std::ops::Mul<Output = V>
            + std::ops::Sub<Output = V>
            + std::ops::Neg<Output = V>
            + From<i32>,
    {
        self.validate_row_col(row, col)?;

        let pivot_value = match self.rows[row].get(&col) {
            Some(v) if !v.is_zero() => v.clone(),
            Some(_) => return Err(SparseError("pivot element is zero".to_string())),
            None => return Err(SparseError("pivot element is zero".to_string())),
        };

        let inv_pivot = V::from(1) / pivot_value.clone();

        // Step 1: Snapshot the original pivot row (before modification)
        // Worst case O(M)
        let pivot_row_snapshot = std::mem::take(&mut self.rows[row]);

        // Step 2: Update the pivot row in-place
        // Collect new values first, then write them
        // Worst case O(M)
        let mut new_pivot_row: FxHashMap<usize, V> =
            FxHashMap::with_capacity_and_hasher(pivot_row_snapshot.len(), Default::default());
        for (j, b) in pivot_row_snapshot.iter() {
            if *j == col {
                new_pivot_row.insert(*j, inv_pivot.clone());
            } else {
                new_pivot_row.insert(*j, -(b.clone() * inv_pivot.clone()));
            }
        }

        self.rows[row] = new_pivot_row;
        // Update cols to reflect new pivot row values (same set of columns, just new values)
        // Worst case O(M)
        for (j, new_val) in self.rows[row].iter() {
            self.cols[*j].insert(row, new_val.clone());
        }

        // Step 3: Snapshot the pivot column (rows that have nonzero in column `col`, excluding pivot row)
        // Worst case O(N)
        let pivot_col_rows: Vec<(usize, V)> = self.cols[col]
            .iter()
            .filter(|(r, _)| **r != row)
            .map(|(r, c)| (*r, c.clone()))
            .collect();

        // Step 4: Update non-pivot rows
        for (i, c_val) in pivot_col_rows.iter() {
            // Hoist c/a: same for every column j in this row
            let c_over_a = c_val.clone() * inv_pivot.clone();

            // For each column j in the original pivot row snapshot:
            for (j, b_val) in pivot_row_snapshot.iter() {
                if *j == col {
                    // Pivot column entry: c -> c/a
                    if c_over_a.is_zero() {
                        self.rows[*i].remove(j);
                        self.cols[*j].remove(i);
                    } else {
                        self.rows[*i].insert(*j, c_over_a.clone());
                        self.cols[*j].insert(*i, c_over_a.clone());
                    }
                } else {
                    // General case: d -> d - b*c/a
                    let d_val = self.rows[*i].get(j).cloned().unwrap_or_else(V::zero);
                    let new_val = d_val - b_val.clone() * c_over_a.clone();
                    if new_val.is_zero() {
                        self.rows[*i].remove(j);
                        self.cols[*j].remove(i);
                    } else {
                        self.rows[*i].insert(*j, new_val.clone());
                        self.cols[*j].insert(*i, new_val);
                    }
                }
            }

            // Handle columns NOT in the pivot row snapshot — these rows have
            // entries that are unaffected (d -> d - 0 = d), so nothing to do.
        }

        Ok(())
    }

    fn validate_row_col(&self, row: usize, col: usize) -> SparseResult<()> {
        if row >= self.rows.len() || col >= self.cols.len() {
            return Err(SparseError(format!(
                "pivot position ({}, {}) is out of bounds for matrix with dimensions {} x {}",
                row,
                col,
                self.rows.len(),
                self.cols.len()
            )));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arithmetic::lia::types::{Rational, rbig};

    #[test]
    fn new_sparse_matrix() {
        let sp = Matrix::<i32>::new(2, 2);
        assert!(sp.is_ok());
    }

    #[test]
    fn test_update_or_insert() {
        let mut sp = Matrix::<i32>::new(2, 2).expect("failed to create new sparse matrix");
        assert_eq!(sp.update_or_insert(0, 0, 1), Ok(false)); // element did not exist previously
        assert_eq!(sp.update_or_insert(0, 0, 2), Ok(true)); // element **did** exist previously
        assert!(sp.update_or_insert(2, 0, 3).is_err()); // element out of bounds
    }

    #[test]
    fn test_multiple_update_or_insert() {
        let mut sp = Matrix::<i32>::new(2, 2).expect("failed to create new sparse matrix");
        assert_eq!(sp.update_or_insert(0, 0, 1), Ok(false));
        assert_eq!(sp.update_or_insert(1, 1, 2), Ok(false));
    }

    #[test]
    fn test_2x2_single_insert_get() {
        let mut sp = Matrix::<i32>::new(2, 2).expect("failed to create new sparse matrix");
        assert!(sp.update_or_insert(0, 0, 1).is_ok());
        assert_eq!(sp.get(0, 0), Some(&1));
        assert_eq!(sp.get(0, 1), Some(&0));
        assert_eq!(sp.get(1, 0), Some(&0));
        assert_eq!(sp.get(1, 1), Some(&0));
        assert_eq!(sp.get(2, 2), None);
    }

    #[test]
    fn from_tuples_3x3() {
        let m = Matrix::<i32>::from_tuples(3, 3, vec![(2, 0, -1), (1, 1, 0), (0, 2, 1)])
            .expect("failed to create matrix from tuples");
        assert_eq!(m.get(2, 0), Some(&-1));
        assert_eq!(m.get(1, 1), Some(&0));
        assert_eq!(m.get(0, 2), Some(&1));
        // out of bounds
        assert_eq!(m.get(4, 2), None);
        // test skipping over a non-existent node
        assert_eq!(m.get(0, 1), Some(&0));
        assert_eq!(m.get(1, 0), Some(&0));
        assert_eq!(m.get(2, 2), Some(&0));
    }

    #[test]
    fn test_pivot_validation() {
        let mut m = Matrix::<Rational>::from_tuples(2, 2, vec![(0, 0, rbig!(2)), (0, 1, rbig!(4))])
            .expect("failed to create matrix");

        // Valid pivot should not error on validation
        assert!(m.pivot(0, 0).is_ok());

        // Out of bounds
        assert!(m.pivot(2, 0).is_err());
        assert!(m.pivot(0, 2).is_err());

        // Zero pivot element
        let mut m2 = Matrix::<Rational>::new(2, 2).expect("failed to create matrix");
        assert!(m2.pivot(0, 0).is_err());
    }

    #[test]
    fn test_delete_node() {
        // [ 1   2   0 ]
        // [ 0   3   0 ]
        // [ 0   0   0 ]
        let mut m = Matrix::<Rational>::from_tuples(
            3,
            3,
            vec![(0, 0, rbig!(1)), (0, 1, rbig!(2)), (1, 1, rbig!(3))],
        )
        .expect("failed to create matrix");

        // Delete existing node by inserting zero
        assert_eq!(m.update_or_insert(0, 1, rbig!(0)), Ok(true));
        assert_eq!(m.get(0, 1), Some(&rbig!(0)));

        // Delete non-existent node
        assert_eq!(m.update_or_insert(2, 2, rbig!(0)), Ok(false));

        // Verify other nodes still exist
        assert_eq!(m.get(0, 0), Some(&rbig!(1)));
        assert_eq!(m.get(1, 1), Some(&rbig!(3)));
    }

    #[test]
    fn test_delete_node_skipping() {
        // [ 1   2   0 ]
        // [ 0   3   0 ]
        // [ 4   0   0 ]
        let mut m = Matrix::<Rational>::from_tuples(
            3,
            3,
            vec![
                (0, 0, rbig!(1)),
                (0, 1, rbig!(2)),
                (1, 1, rbig!(3)),
                (2, 0, rbig!(4)),
            ],
        )
        .expect("failed to create matrix");

        // Delete existing node
        assert_eq!(m.update_or_insert(0, 0, rbig!(0)), Ok(true));
        assert_eq!(m.get(0, 0), Some(&rbig!(0)));
        // Verify other nodes still exist
        assert_eq!(m.get(0, 1), Some(&rbig!(2)));
        assert_eq!(m.get(2, 0), Some(&rbig!(4)));
    }

    #[test]
    fn test_pivot_3x3() {
        // Starting matrix:
        // [ 2   4   6 ]
        // [ 1   3   5 ]
        // [ 3   6   9 ]
        let mut m = Matrix::<Rational>::from_tuples(
            3,
            3,
            vec![
                (0, 0, rbig!(2)),
                (0, 1, rbig!(4)),
                (0, 2, rbig!(6)),
                (1, 0, rbig!(1)),
                (1, 1, rbig!(3)),
                (1, 2, rbig!(5)),
                (2, 0, rbig!(3)),
                (2, 1, rbig!(6)),
                (2, 2, rbig!(9)),
            ],
        )
        .expect("failed to create matrix");

        // Pivot on (0, 0) with value 2
        assert!(m.pivot(0, 0).is_ok());

        // Expected result:
        // [ 1/2  -2   -3 ]
        // [ 1/2   1    2 ]
        // [ 3/2   0    0 ]

        // Check pivot element: 2 -> 1/2
        assert_eq!(m.get(0, 0), Some(&rbig!(1 / 2)));

        // Check rest of the pivot row: b -> -b/a
        assert_eq!(m.get(0, 1), Some(&rbig!(-2)));
        assert_eq!(m.get(0, 2), Some(&rbig!(-3)));

        // Check pivot column: c -> c/a
        assert_eq!(m.get(1, 0), Some(&rbig!(1 / 2)));
        assert_eq!(m.get(2, 0), Some(&rbig!(3 / 2)));

        // Check other elements: d - b*c/a
        // (1,1): 3 - 4*1/2 = 1
        assert_eq!(m.get(1, 1), Some(&rbig!(1)));
        // (1,2): 5 - 6*1/2 = 2
        assert_eq!(m.get(1, 2), Some(&rbig!(2)));
        // (2,1): 6 - 4*3/2 = 0 (should be deleted)
        assert_eq!(m.get(2, 1), Some(&rbig!(0)));
        // (2,2): 9 - 6*3/2 = 0 (should be deleted)
        assert_eq!(m.get(2, 2), Some(&rbig!(0)));
    }

    #[test]
    fn test_pivot_sparse_matrix() {
        // Sparse matrix with many zeros
        // [ 5   0   0 ]
        // [ 0   2   0 ]
        // [ 0   0   1 ]
        let mut m = Matrix::<Rational>::from_tuples(
            3,
            3,
            vec![(0, 0, rbig!(5)), (1, 1, rbig!(2)), (2, 2, rbig!(1))],
        )
        .expect("failed to create matrix");

        // Pivot on (0, 0)
        assert!(m.pivot(0, 0).is_ok());

        // Expected:
        // [ 1/5  0   0 ]
        // [ 0    2   0 ]
        // [ 0    0   1 ]
        assert_eq!(m.get(0, 0), Some(&rbig!(1 / 5)));
        assert_eq!(m.get(1, 1), Some(&rbig!(2)));
        assert_eq!(m.get(2, 2), Some(&rbig!(1)));
    }

    #[test]
    fn test_pivot_creates_zeros() {
        // Matrix where pivot creates zeros
        // [ 2   4 ]
        // [ 1   2 ]
        let mut m = Matrix::<Rational>::from_tuples(
            2,
            2,
            vec![
                (0, 0, rbig!(2)),
                (0, 1, rbig!(4)),
                (1, 0, rbig!(1)),
                (1, 1, rbig!(2)),
            ],
        )
        .expect("failed to create matrix");

        // Pivot on (0, 0)
        assert!(m.pivot(0, 0).is_ok());

        // Expected:
        // [ 1/2  -2 ]
        // [ 1/2   0 ]
        assert_eq!(m.get(0, 0), Some(&rbig!(1 / 2)));
        assert_eq!(m.get(0, 1), Some(&rbig!(-2)));
        assert_eq!(m.get(1, 0), Some(&rbig!(1 / 2)));
        assert_eq!(m.get(1, 1), Some(&rbig!(0)));
    }

    #[test]
    fn test_multiple_pivots() {
        // Test sequential pivots
        let mut m = Matrix::<Rational>::from_tuples(
            2,
            2,
            vec![
                (0, 0, rbig!(3)),
                (0, 1, rbig!(6)),
                (1, 0, rbig!(2)),
                (1, 1, rbig!(5)),
            ],
        )
        .expect("failed to create matrix");

        // First pivot on (0, 0)
        assert!(m.pivot(0, 0).is_ok());

        // After first pivot:
        // [ 1/3  -2 ]
        // [ 2/3   1 ]
        assert_eq!(m.get(0, 0), Some(&rbig!(1 / 3)));
        assert_eq!(m.get(0, 1), Some(&rbig!(-2)));
        assert_eq!(m.get(1, 0), Some(&rbig!(2 / 3)));
        assert_eq!(m.get(1, 1), Some(&rbig!(1)));

        // Second pivot on (1, 1)
        assert!(m.pivot(1, 1).is_ok());

        // After second pivot:
        // [ 5/3  -2 ]
        // [-2/3   1 ]
        assert_eq!(m.get(0, 0), Some(&rbig!(5 / 3)));
        assert_eq!(m.get(0, 1), Some(&rbig!(-2)));
        assert_eq!(m.get(1, 0), Some(&rbig!(-2 / 3)));
        assert_eq!(m.get(1, 1), Some(&rbig!(1)));
    }

    #[test]
    fn test_pivot_zero_to_nonzero() {
        let mut m = Matrix::<Rational>::from_tuples(
            2,
            2,
            vec![
                (0, 0, rbig!(2)),
                (0, 1, rbig!(1)),
                (1, 0, rbig!(1)),
                (1, 1, rbig!(0)),
            ],
        )
        .expect("failed to create matrix");
        // Before pivot:
        // [ 2  1 ]
        // [ 1  0 ]
        assert!(m.pivot(0, 0).is_ok());

        // After pivot:
        // [ 1/2  -1/2 ]
        // [ 1/2  -1/2 ]
        assert_eq!(m.get(0, 0), Some(&rbig!(1 / 2)));
        assert_eq!(m.get(0, 1), Some(&rbig!(-1 / 2)));
        assert_eq!(m.get(1, 0), Some(&rbig!(1 / 2)));
        assert_eq!(m.get(1, 1), Some(&rbig!(-1 / 2)));
    }

    #[test]
    fn test_pivot_0_0_diag_plus_row() {
        let tuples = vec![(0, 0, rbig!(2)), (1, 1, rbig!(3)), (0, 1, rbig!(4))];
        let mut m = Matrix::from_tuples(2, 2, tuples).expect("Failed to create matrix");
        m.pivot(0, 0).expect("first pivot failed");
        assert_eq!(m.get(0, 0), Some(&rbig!(1 / 2)));
        m.pivot(0, 0).expect("second pivot failed");
        assert_eq!(m.get(0, 0), Some(&rbig!(2)));
    }

    #[test]
    fn test_pivot_0_0_20diag_plus_row() {
        // Generate 20 tuples with values > 1
        let mut tuples: Vec<(usize, usize, Rational)> = (0..20)
            .map(|i| {
                let row = i;
                let col = i;
                let value = Rational::from(i as i64 + 2); // values >= 2
                (row, col, value)
            })
            .collect();
        // add a non-zero row
        tuples.extend(
            (0..20)
                .map(|i| {
                    let row = 0;
                    let col = i;
                    let value = Rational::from(i as i64 + 3);
                    (row, col, value)
                })
                .collect::<Vec<_>>(),
        );
        let mut m = Matrix::from_tuples(20, 20, tuples).expect("Failed to create matrix");
        m.pivot(0, 0).expect("first pivot failed");
        assert_eq!(m.get(0, 0), Some(&rbig!(1 / 3)));
        m.pivot(0, 0).expect("second pivot failed");
        assert_eq!(m.get(0, 0), Some(&rbig!(3)));
    }

    #[test]
    fn test_pivot_0_0_20diag_plus_row_plus_col() {
        let mut tuples: Vec<(usize, usize, Rational)> = (0..20)
            .map(|i| {
                let row = i;
                let col = i;
                let value = Rational::from(i as i64 + 2); // values >= 2
                (row, col, value)
            })
            .collect();
        // add 5 non-zero entries to the pivot row
        tuples.extend(
            (0..5)
                .map(|i| {
                    let row = 0;
                    let col = (4 * i + 2) % 20;
                    let value = Rational::from(10 * i as i64 + 2);
                    (row, col, value)
                })
                .collect::<Vec<_>>(),
        );
        // add 5 non-zero entries to the pivot col
        tuples.extend(
            (0..5)
                .map(|i| {
                    let row = (4 * i + 3) % 20;
                    let col = 0;
                    let value = Rational::from(100 * i as i64 + 2);
                    (row, col, value)
                })
                .collect::<Vec<_>>(),
        );
        let mut m = Matrix::from_tuples(20, 20, tuples).expect("Failed to create matrix");

        m.pivot(0, 0).expect("first pivot failed");
        assert_eq!(m.get(0, 0), Some(&rbig!(1 / 2)));
        m.pivot(0, 0).expect("second pivot failed");
        assert_eq!(m.get(0, 0), Some(&rbig!(2)));
    }
}
