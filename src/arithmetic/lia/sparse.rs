// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Sparse matrix implementation
//!
//! Matrix representation:
//!
//! ```text
//!                        basecol
//!                           |
//!                          ...
//!                           ^
//!                           |
//! baserow  <    [ r | c |  up  ] <-- ...
//!           \   [ value | left ]
//!            \______________/
//!
//!                      ^
//!                      |
//!                     ...
//! ```

use num_traits::Zero;
use slotmap;
use std::collections::{HashMap, HashSet};
use std::error;
use std::fmt;

/// Generic error type for spare matrix operations
#[derive(Debug, PartialEq, Eq)]
pub struct SparseError(pub String);
impl fmt::Display for SparseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl error::Error for SparseError {}

/// Generic result type for tableau operations
pub type SparseResult<T> = Result<T, SparseError>;

// pointer to a matrix node
type K = slotmap::DefaultKey;

/// Sparse matrix node
#[derive(Debug)]
struct Node<V> {
    // Some if the node is not a column header
    row: Option<usize>,
    // Some if the node is not a row header
    col: Option<usize>,
    value: V,
    // pointer to the next left entry
    left: K,
    // pointer to the next up entry
    up: K,
}

/// todo:
pub struct Matrix<V> {
    arena: slotmap::SlotMap<K, Node<V>>,
    baserows: Vec<K>, // length = # rows
    basecols: Vec<K>, // length = # cols
    zero: V,
}

impl<V: fmt::Debug> fmt::Debug for Matrix<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        writeln!(f, "Matrix: (zero = {:?}", self.zero)?;
        write!(f, "  baserows: ")?;
        for k in self.baserows.iter() {
            write!(f, "{k:?},")?;
        }
        writeln!(f)?;
        write!(f, "  basecols: ")?;
        for k in self.basecols.iter() {
            write!(f, "{k:?},")?;
        }
        writeln!(f)?;
        for n in self.arena.iter() {
            writeln!(f, "    {n:?}")?;
        }
        Ok(())
    }
}

impl<V: Zero + fmt::Debug> Matrix<V> {
    /// Create a new sparse matrix from a vector of tuples (row, col, value).
    ///
    /// The matrix dimensions are explicitly specified by nrows and ncols.
    /// Returns an error if any tuple contains row or col indices out of bounds.
    pub fn from_tuples(
        nrows: usize,
        ncols: usize,
        t: Vec<(usize, usize, V)>,
    ) -> SparseResult<Self> {
        // Create a new matrix with the specified dimensions
        let mut matrix = Self::new(nrows, ncols)?;

        // Insert each tuple into the matrix, validating bounds. Zero values are not
        // inserted into the matrix.
        for (row, col, value) in t {
            if !value.is_zero() && matrix.update_or_insert(row, col, value).is_none() {
                return Err(SparseError(format!(
                    "tuple ({}, {}) is out of bounds for matrix with dimensions {} x {}",
                    row, col, nrows, ncols
                )));
            }
        }

        Ok(matrix)
    }

    /// Create a new sparse zero matrix of nrows x ncols, i.e. there are no nodes in the matrix
    /// representation except for the base rows and columns.
    ///
    /// Zero Matrix representation:
    ///
    /// ```text
    /// For a 3x3 matrix (nrows=3, ncols=3):
    ///
    ///    basecol[0]  basecol[1]  basecol[2]
    ///         ↓          ↓          ↓
    ///    ┌─────────┬─────────┬─────────┐
    ///    │ r:None  │ r:None  │ r:None  │
    ///    │ c:0     │ c:1     │ c:2     │
    ///  ┌─┼─left: ←─┼─left: ←─┼─left:   │←┐
    ///  │ │ up:─┐   │ up:─┐   │ up:─┐   │ │
    ///  │ └─────┼───┴─────┼───┴─────┼───┘ │
    ///  │    │  ↓      │  ↓      │  ↓     │
    ///  │    │  │      │  │      │  │     │
    ///  │    └──┘      └──┘      └──┘     │
    ///  └─────────────────────────────────┘
    ///
    /// ```
    ///
    ///  and similarly for the baserows but they are arranged in a single column at the left.
    ///
    pub fn new(nrows: usize, ncols: usize) -> SparseResult<Self> {
        if nrows == 0 || ncols == 0 {
            return Err(SparseError("nrows and ncols must be > 0".to_string()));
        }
        let mut arena = slotmap::SlotMap::new();
        let mut baserows = Vec::with_capacity(nrows);
        let mut basecols = Vec::with_capacity(ncols);

        for r in 0..nrows {
            let mk_baserow_node = |k| Node {
                row: Some(r),
                col: None,
                value: V::zero(),
                left: k,
                up: k,
            };
            // initially every left/up pointer of the baserow nodes points to itself
            let k = arena.insert_with_key(mk_baserow_node);
            baserows.push(k);
        }

        // form a circularly linked list with the baserow nodes
        let last_baserow_node_k = *baserows.last().unwrap(); // safe b/c nrows > 0 from early return above
        let first_baserow_node_k = *baserows.first().unwrap();
        let first_baserow_node = arena.get_mut(first_baserow_node_k).unwrap();
        first_baserow_node.up = last_baserow_node_k;
        let mut k = first_baserow_node_k; // key to the previous baserow node
        for r in baserows[1..].iter() {
            let node = arena.get_mut(*r).unwrap();
            node.up = k;
            k = *r;
        }

        for c in 0..ncols {
            let mk_basecol_node = |k| Node {
                row: None,
                col: Some(c),
                value: V::zero(),
                left: k,
                up: k,
            };
            // initially every left/up pointer of the basecol nodes points to itself
            let k = arena.insert_with_key(mk_basecol_node);
            basecols.push(k);
        }

        // form a circularly linked list with the basecol nodes
        let last_basecol_node_k = *basecols.last().unwrap(); // safe b/c nrows > 0 from early return above
        let first_basecol_node_k = *basecols.first().unwrap();
        let first_basecol_node = arena.get_mut(first_basecol_node_k).unwrap();
        first_basecol_node.left = last_basecol_node_k;
        let mut k = first_basecol_node_k; // key to the previous basecol node
        for c in basecols[1..].iter() {
            let node = arena.get_mut(*c).unwrap();
            node.left = k;
            k = *c;
        }

        Ok(Self {
            arena,
            baserows,
            basecols,
            zero: V::zero(),
        })
    }

    /// Get the value of an element in the matrix
    ///
    /// Returns Some(&Zero) if the element coordinates are in-bounds but the node
    /// doesn't exist in the sparse matrix representation. Return None if the indices
    /// are out of bounds.
    pub fn get(&self, row: usize, col: usize) -> Option<&V> {
        if row >= self.baserows.len() || col >= self.basecols.len() {
            return None;
        }
        // traverse left from the baserow[row] to find the right column to get
        let baserow_n = self.arena.get(self.baserows[row]).unwrap();
        let mut p = baserow_n.left; // pointer to the current node in left traversal
        let mut p_n = self.arena.get(p).unwrap();
        while let Some(pcol) = p_n.col
            && pcol > col
        {
            p = p_n.left;
            p_n = self.arena.get(p).unwrap();
        }
        if let Some(pcol) = p_n.col
            && pcol == col
        {
            // we arrived at a non baserow node whose row and col match the input; return the value
            // stored here
            debug_assert!(p_n.row.is_some() && p_n.row.unwrap() == row);
            let p_n = self.arena.get(p).unwrap();
            return Some(&p_n.value);
        }
        // we arrived at a baserow node; meaning the node doesn't exist in the sparse
        // representation
        Some(&self.zero)
    }

    /// Insert or update an entry in the matrix
    ///
    /// Returns `true` if a node was inserted. Otherwise the existing value
    /// is updated and `false` is returned.
    ///
    /// Panics if `row` or `col` is out of bounds
    pub fn update_or_insert(&mut self, row: usize, col: usize, val: V) -> Option<bool> {
        if row >= self.baserows.len() || col >= self.basecols.len() {
            return None;
        }
        // traverse left from the baserow[row] to find the right column to insert or
        // update at
        let mut q = self.baserows[row]; // previous node in left traversal
        let baserow_n = self.arena.get_mut(q).unwrap();
        let mut p = baserow_n.left;
        let p_n = self.arena.get(p).unwrap();
        while let Some(pcol) = p_n.col
            && pcol > col
        {
            q = p;
            let p_n = self.arena.get(p).unwrap();
            p = p_n.left;
        }
        if let Some(pcol) = p_n.col
            && pcol == col
        {
            // update value
            debug_assert!(p_n.row.is_some() && p_n.row.unwrap() == row);
            let p_n = self.arena.get_mut(p).unwrap();
            p_n.value = val;
            Some(false)
        } else {
            // insert node p <- new_node <- q
            let mk_node = |k| Node {
                row: Some(row),
                col: Some(col),
                value: val,
                left: p,
                up: k, // up will be updated later in the column traversal
            };
            let k = self.arena.insert_with_key(mk_node);
            let q_n = self.arena.get_mut(q).unwrap();
            q_n.left = k;

            // column traverse to fix links in col `col` and update `k`'s up pointer
            let mut q = self.basecols[col]; // previous node in left traversal
            let basecol_n = self.arena.get_mut(q).unwrap();
            let mut p = basecol_n.up;
            let p_n = self.arena.get(p).unwrap();
            while let Some(prow) = p_n.row
                && prow > row
            {
                q = p;
                let p_n = self.arena.get(p).unwrap();
                p = p_n.up;
            }
            if let Some(prow) = p_n.row
                && prow == row
            {
                // there is no node linked yet in the column with row `row` since
                // we're in the branch creating that now and column links have not
                // been setup yet
                unreachable!("programming error in sparse matrix column traversal");
            } else {
                // update links in the column
                //   p
                //   ^
                // new_node
                //   ^
                //   q
                debug_assert!(p_n.col.is_some() && p_n.col.unwrap() == col);
                let k_n = self.arena.get_mut(k).unwrap();
                k_n.up = p;
                let q_n = self.arena.get_mut(q).unwrap();
                q_n.up = k;

                Some(true)
            }
        }
    }

    /// Delete a node at the specified row and column from the sparse matrix.
    ///
    /// Updates the linked list pointers to maintain matrix integrity.
    /// Returns Ok(true) if an in-bounds node was found and deleted, or Ok(false)
    /// if no node was present to delete. Return Err if the row, col are out of bounds.
    /// (row, col) is out of bounds.
    fn delete_node(&mut self, row: usize, col: usize) -> SparseResult<bool> {
        if row >= self.baserows.len() || col >= self.basecols.len() {
            return Err(SparseError(format!(
                "({row}, {col}) are out of bounds for matrix of size {}x{}",
                self.baserows.len(),
                self.basecols.len(),
            )));
        }

        // Traverse left from baserow to find the node and its predecessor
        let mut q = self.baserows[row]; // predecessor in row traversal
        let baserow_n = self.arena.get(q).unwrap();
        let mut p = baserow_n.left; // current pointer in row traversal

        loop {
            let p_n = self.arena.get(p).unwrap();
            if let Some(pcol) = p_n.col {
                if pcol == col {
                    // Found the node to delete
                    let node_to_delete = p;
                    let left_ptr = p_n.left;
                    let up_ptr = p_n.up;

                    // Update row links: q.left = p.left
                    let q_n = self.arena.get_mut(q).unwrap();
                    q_n.left = left_ptr;

                    // Traverse up from basecol to find predecessor in column
                    let mut q_col = self.basecols[col];
                    let basecol_n = self.arena.get(q_col).unwrap();
                    let mut p_col = basecol_n.up;

                    loop {
                        let p_col_n = self.arena.get(p_col).unwrap();
                        if let Some(prow) = p_col_n.row {
                            if prow == row {
                                // Found the node in column traversal
                                // Update column links: q_col.up = p.up
                                let q_col_n = self.arena.get_mut(q_col).unwrap();
                                q_col_n.up = up_ptr;
                                break;
                            }
                            q_col = p_col;
                            let p_col_n = self.arena.get(p_col).unwrap();
                            p_col = p_col_n.up;
                        } else {
                            // Reached basecol without finding node - cannot happen since we've
                            // already found the node
                            unreachable!()
                        }
                    }

                    // Remove from arena
                    self.arena.remove(node_to_delete);
                    // TODO: sparse::delete: doesn't make sense to return the key if we delete from the arena
                    return Ok(true);
                } else if pcol < col {
                    // Passed where the node would be, it doesn't exist
                    return Ok(false);
                }
                q = p;
                let p_n = self.arena.get(p).unwrap();
                p = p_n.left;
            } else {
                // Reached baserow without finding node
                return Ok(false);
            }
        }
    }

    /// Perform a pivot operation on the matrix at the specified row and column.
    ///
    /// The pivot transforms matrix elements according to:
    ///
    /// - Pivot element: a → 1/a
    /// - Pivot row (non-pivot): b → b/a
    /// - Pivot column (non-pivot): c → -c/a
    /// - Other elements: d → d - b*c/a (where b is pivot row element, c is pivot column element)
    ///
    /// Nodes that become zero are deleted from the sparse representation.
    ///
    /// TODO: sparse::pivot: the current implementation uses `get` and `delete_node` as helper
    /// functions in a few places. This introduces some extra row/col traversals which can be
    /// eliminated by combining with traversals in the pivot.
    pub fn pivot(&mut self, row: usize, col: usize) -> SparseResult<()>
    where
        V: Clone
            + std::ops::Div<Output = V>
            + std::ops::Mul<Output = V>
            + std::ops::Sub<Output = V>
            + std::ops::Neg<Output = V>
            + From<i32>,
    {
        // Validate bounds
        if row >= self.baserows.len() || col >= self.basecols.len() {
            return Err(SparseError(format!(
                "pivot position ({}, {}) is out of bounds for matrix with dimensions {} x {}",
                row,
                col,
                self.baserows.len(),
                self.basecols.len()
            )));
        }

        // Get pivot element and check it's non-zero
        let pivot_value = match self.get(row, col) {
            Some(v) if !v.is_zero() => v.clone(),
            Some(_) => return Err(SparseError("pivot element is zero".to_string())),
            None => return Err(SparseError("pivot position is out of bounds".to_string())),
        };

        // Calculate inverse of pivot
        let inv_pivot = V::from(1) / pivot_value.clone();

        // Cache pivot row values in a HashMap for efficient lookup in later passes
        let mut pivot_row_map = HashMap::new(); // HashMap<col, value>
        // Update pivot row: a -> 1/a for pivot elt., b → b/a for non-pivot elements
        let baserow_k = self.baserows[row];
        let baserow_n = self.arena.get(baserow_k).unwrap();
        let mut p = baserow_n.left;
        loop {
            let p_n = self.arena.get_mut(p).unwrap();
            if let Some(pcol) = p_n.col {
                pivot_row_map.insert(pcol, p_n.value.clone());
                if pcol == col {
                    // a -> 1/a
                    p_n.value = inv_pivot.clone();
                } else {
                    // b -> b/a
                    p_n.value = p_n.value.clone() * inv_pivot.clone();
                }
                p = p_n.left;
            } else {
                // Reached baserow node, stop
                break;
            }
        }

        // Update pivot column: c → -c/a for non-pivot rows
        // Cache the pivot column values 'c' for later use in the general d -> d - b*c/a case
        let mut pivot_col_values = HashMap::new();
        let basecol_k = self.basecols[col];
        let basecol_n = self.arena.get(basecol_k).unwrap();
        let mut p = basecol_n.up;
        loop {
            let p_n = self.arena.get_mut(p).unwrap();
            if let Some(prow) = p_n.row {
                if prow != row {
                    let old_value = &p_n.value;
                    pivot_col_values.insert(prow, old_value.clone());
                    p_n.value = -(old_value.clone() / pivot_value.clone());
                }
                p = p_n.up;
            } else {
                // Reached basecol node, stop
                break;
            }
        }

        // TODO: sparse::pivot: in the for { ... loop { ... } } code blocks below, efficiency can be improved by
        // maintaining an array of column pointers as in Knuth 2.2.6 Algorithm S

        // Update non-pivot rows: d → d - b*c/a
        for r in 0..self.baserows.len() {
            if r == row {
                continue; // Skip pivot row
            }

            // Get pivot column value for this row (c) from cached values
            let c_val = match pivot_col_values.get(&r).cloned() {
                Some(v) if !v.is_zero() => v, // Note: guard is true by construction, but we're being defensive
                _ => continue, // If c is zero (implicit or explicit), no updates needed for this row: d -> d - b*c/a = d
            };

            // Track which columns we've already seen/updated in this row
            let mut updated_cols = HashSet::new();

            // Collect nodes to update/delete in this row
            let mut updates = Vec::new(); // Vec<(col, new_value)>
            let baserow_k = self.baserows[r];
            let baserow_n = self.arena.get(baserow_k).unwrap();
            let mut p = baserow_n.left;

            loop {
                let p_n = self.arena.get(p).unwrap();
                if let Some(pcol) = p_n.col {
                    updated_cols.insert(pcol); // Mark this column as seen
                    if pcol != col {
                        // Get pivot row value b at (row, pcol) from the cached HashMap
                        let b_val = pivot_row_map
                            .get(&pcol)
                            .cloned()
                            .unwrap_or_else(|| V::zero());

                        // Calculate new value: d - b*c/a
                        let d_val = p_n.value.clone();
                        let new_val = d_val - b_val * c_val.clone() * inv_pivot.clone();

                        updates.push((pcol, new_val));
                    }
                    p = p_n.left;
                } else {
                    break;
                }
            }

            // Apply updates to existing nodes
            for (pcol, new_val) in updates {
                if new_val.is_zero() {
                    self.delete_node(r, pcol)?;
                } else {
                    let baserow_k = self.baserows[r];
                    let baserow_n = self.arena.get(baserow_k).unwrap();
                    let mut p = baserow_n.left;
                    loop {
                        let p_n = self.arena.get_mut(p).unwrap();
                        if let Some(c) = p_n.col {
                            if c == pcol {
                                p_n.value = new_val;
                                break;
                            }
                            p = p_n.left;
                        } else {
                            break;
                        }
                    }
                }
            }

            // Handle column positions that were zero initially, but for which the corresponding
            // pivot row and column values are non-zero, i.e. d=0, but b, c != 0.
            for (pcol, b_val) in pivot_row_map.iter() {
                if *pcol != col && !updated_cols.contains(pcol) {
                    // d=0, calculate 0 - b*c/a = -b*c/a
                    let new_val = -b_val.clone() * c_val.clone() * inv_pivot.clone();
                    if !new_val.is_zero() {
                        self.update_or_insert(r, *pcol, new_val);
                    }
                }
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arithmetic::lia::types::{Rational, rbig};

    #[test]
    ///
    /// Matrix:
    ///   baserows: [DefaultKey(1v1), DefaultKey(2v1)]
    ///   basecols: [DefaultKey(3v1), DefaultKey(4v1)]
    ///     Node { row: Some(0), col: None, value: 0, left: DefaultKey(1v1), up: DefaultKey(2v1) }
    ///     Node { row: Some(1), col: None, value: 0, left: DefaultKey(2v1), up: DefaultKey(1v1) }
    ///     Node { row: None, col: Some(0), value: 0, left: DefaultKey(4v1), up: DefaultKey(3v1) }
    ///     Node { row: None, col: Some(1), value: 0, left: DefaultKey(3v1), up: DefaultKey(4v1) }
    ///
    fn new_sparse_matrix() {
        let sp = Matrix::<i32>::new(2, 2);
        assert!(sp.is_ok());
    }

    ///
    /// Matrix:
    ///   baserows: [DefaultKey(1v1), DefaultKey(2v1)]
    ///   basecols: [DefaultKey(3v1), DefaultKey(4v1)]
    ///     Node { row: Some(0), col: None, value: 0, left: DefaultKey(5v1), up: DefaultKey(2v1) }
    ///     Node { row: Some(1), col: None, value: 0, left: DefaultKey(2v1), up: DefaultKey(1v1) }
    ///     Node { row: None, col: Some(0), value: 0, left: DefaultKey(4v1), up: DefaultKey(3v1) }
    ///     Node { row: None, col: Some(1), va lue: 0, left: DefaultKey(3v1), up: DefaultKey(4v1) }
    ///     Node { row: Some(0), col: Some(0), value: 1, left: DefaultKey(1v1), up: Defau ltKey(5v1) }
    #[test]
    fn test_update_or_insert() {
        let mut sp = Matrix::<i32>::new(2, 2).expect("failed to create new sparse matrix");
        assert_eq!(sp.update_or_insert(0, 0, 1), Some(true)); // element did not exist previously
        assert_eq!(sp.update_or_insert(0, 0, 2), Some(false)); // element **did** exist previously
        assert_eq!(sp.update_or_insert(2, 0, 3), None); // element **did** exist previously
    }

    #[test]
    fn test_multiple_update_or_insert() {
        let mut sp = Matrix::<i32>::new(2, 2).expect("failed to create new sparse matrix");
        assert_eq!(sp.update_or_insert(0, 0, 1), Some(true));
        assert_eq!(sp.update_or_insert(1, 1, 2), Some(true));
    }

    #[test]
    fn test_2x2_single_insert_get() {
        let mut sp = Matrix::<i32>::new(2, 2).expect("failed to create new sparse matrix");
        assert!(sp.update_or_insert(0, 0, 1).is_some());
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

        // Delete existing node
        assert_eq!(m.delete_node(0, 1), Ok(true));
        assert_eq!(m.get(0, 1), Some(&rbig!(0)));

        // Delete non-existent node
        assert_eq!(m.delete_node(2, 2), Ok(false));

        // Verify other nodes still exist
        assert_eq!(m.get(0, 0), Some(&rbig!(1)));
        assert_eq!(m.get(1, 1), Some(&rbig!(3)));
    }

    #[test]
    fn test_delete_node_skipping() {
        // [ 1   2   0 ]  deletion traversal must skip values 2 and 4 to fix up links
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
        assert_eq!(m.delete_node(0, 0), Ok(true));
        assert_eq!(m.get(0, 0), Some(&rbig!(0)));
        // Verify nodes that were skipped over still exist
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
        // [ 2   4   6 ]    [ 0.5   2    3 ]
        // [ 1   3   5 ] -> [-0.5   1    2 ]
        // [ 3   6   9 ]    [-1.5   0    0 ]

        // Check pivot element: 2 → 1/2
        assert_eq!(m.get(0, 0), Some(&rbig!(1 / 2)));

        // Check rest of the pivot row: b -> b/a
        assert_eq!(m.get(0, 1), Some(&rbig!(2)));
        assert_eq!(m.get(0, 2), Some(&rbig!(3)));

        // Check pivot column: c → -c/2
        assert_eq!(m.get(1, 0), Some(&rbig!(-1 / 2)));
        assert_eq!(m.get(2, 0), Some(&rbig!(-3 / 2)));

        // Check other elements: d - b*c/2
        // (1,1): 3 - 4*1/2 = 3 - 2 = 1
        assert_eq!(m.get(1, 1), Some(&rbig!(1)));
        // (1,2): 5 - 6*1/2 = 5 - 3 = 2
        assert_eq!(m.get(1, 2), Some(&rbig!(2)));
        // (2,1): 6 - 4*3/2 = 6 - 6 = 0 (should be deleted)
        assert_eq!(m.get(2, 1), Some(&rbig!(0)));
        // (2,2): 9 - 6*3/2 = 9 - 9 = 0 (should be deleted)
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
        // [ 1/2   2 ]  (0,1) = 4/2 = 2
        // [-1/2   0 ]  (1,1) = 2 - 4*1/2 = 2 - 2 = 0
        assert_eq!(m.get(0, 0), Some(&rbig!(1 / 2)));
        assert_eq!(m.get(0, 1), Some(&rbig!(2)));
        assert_eq!(m.get(1, 0), Some(&rbig!(-1 / 2)));
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
        // [ 1/3   2 ]  (0,1) = 6/3 = 2
        // [-2/3   1 ]  (1,1) = 5 - 2*2/3 = 5 - 4 = 1
        assert_eq!(m.get(0, 0), Some(&rbig!(1 / 3)));
        assert_eq!(m.get(0, 1), Some(&rbig!(2)));
        assert_eq!(m.get(1, 0), Some(&rbig!(-2 / 3)));
        assert_eq!(m.get(1, 1), Some(&rbig!(1)));

        // Second pivot on (1, 1)
        assert!(m.pivot(1, 1).is_ok());

        // After second pivot:
        // [ 5/3  -2 ]  (0,0) -> 1/3 - (-2/3)*2/1 = 1/3 + 4/3 = 5/3
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
        // [ 1/2   1/2 ]
        // [-1/2  -1/2 ] (1,1) entry goes from zero to non-zero --> 0 - 1*1/2 = -1/2
        assert_eq!(m.get(0, 0), Some(&rbig!(1 / 2)));
        assert_eq!(m.get(0, 1), Some(&rbig!(1 / 2)));
        assert_eq!(m.get(1, 0), Some(&rbig!(-1 / 2)));
        assert_eq!(m.get(1, 1), Some(&rbig!(-1 / 2)));
    }
}
