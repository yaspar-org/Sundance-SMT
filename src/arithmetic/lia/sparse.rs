// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! todo:

use num_traits::Zero;
use slotmap;
use std::error;
/// Sparse matrix implementation
///
/// Matrix representation:
///
///                        basecol
///                           |
///                          ...
///                           ^
///                           |
/// baserow  <    [ r | c |  up  ] <-- ...
///           \   [ value | left ]
///            \______________/
///
///                      ^
///                      |
///                     ...
use std::fmt;

/// Generic error type for spare matrix operations
#[derive(Debug)]
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

impl<V: Zero + Default + fmt::Debug> Matrix<V> {
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

        // Insert each tuple into the matrix, validating bounds
        for (row, col, value) in t {
            if matrix.update_or_insert(row, col, value).is_none() {
                return Err(SparseError(format!(
                    "tuple ({}, {}) is out of bounds for matrix with dimensions {} x {}",
                    row, col, nrows, ncols
                )));
            }
        }

        Ok(matrix)
    }

    /// Create a new sparse matrix of nrows x ncols where all entries are Zero, i.e.
    /// there are no nodes in the matrix representation except for the base rows and columns.
    pub fn new(nrows: usize, ncols: usize) -> SparseResult<Self> {
        let mut arena = slotmap::SlotMap::new();
        let mut baserows = Vec::with_capacity(nrows);
        let mut basecols = Vec::with_capacity(ncols);
        if nrows == 0 || ncols == 0 {
            return Err(SparseError("nrows and ncols must be > 0".to_string()));
        }

        for r in 0..nrows {
            let mk_baserow_node = |k| Node {
                row: Some(r),
                col: None,
                value: V::default(),
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
                value: V::default(),
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
    /// Returns Zero if the element coordinates are in-bounds but the node
    /// doesn't exist in the sparse matrix representation.
    pub fn get(&self, row: usize, col: usize) -> Option<&V> {
        if row >= self.baserows.len() || col >= self.basecols.len() {
            return None;
        }
        // traverse left from the baserow[row] to find the right column to get
        let baserow_n = self.arena.get(self.baserows[row]).unwrap();
        let mut p = baserow_n.left; // current node in left traversal
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

            // DEBUG: println!("{:?}", self);

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
}

#[cfg(test)]
mod tests {
    use super::*;

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
        println!("DEBUG:");
        println!("{m:?}");
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
}
