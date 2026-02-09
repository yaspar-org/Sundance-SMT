// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Implementation of tableau based on dense a matrix

use crate::arithmetic::lia::tableau::{Tableau, TableauError, TableauResult};
use crate::arithmetic::lia::types::Rational;

use array2d::{self, Array2D};

/// Tableau implementation based on a dense matrix
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TableauDense {
    nrows: usize,
    ncols: usize,
    data: Box<Array2D<Rational>>,
}

impl TableauDense {
    /// Make a new Tableau from row data.
    ///
    /// Pre-conditions:
    /// - forall v1, v2 in `data`, `v1.len() == v2.len()`
    ///
    pub fn from_rows(data: &[Vec<Rational>]) -> TableauResult<Self> {
        let nrows = data.len();
        if nrows == 0 {
            return Err(TableauError("tableau data is empty".to_string()));
        }
        let ncols = data[0].len();
        Ok(TableauDense {
            nrows,
            ncols,
            data: Box::new(Array2D::from_rows(data)?),
        })
    }

    /// Return the number of rows in the tableau (= number of basic variables)
    pub fn nrows(&self) -> usize {
        self.data.num_rows()
    }
    /// Return the number of columns in the tableau (= number of basic + non-basic variables)
    pub fn ncols(&self) -> usize {
        self.data.num_columns()
    }
}

impl Tableau for TableauDense {
    fn pivot(&mut self, row: usize, col: usize) -> TableauResult<()> {
        let a_row_col = &self.data[(row, col)];
        if a_row_col.is_zero() {
            return Err(TableauError("pivot coeff is zero".to_string()));
        }
        let inv_a_row_col = Rational::from(1) / a_row_col;

        #[allow(clippy::needless_range_loop)] // lint suggestion forces violation of borrow rules
        for r in 0..self.nrows {
            if r == row {
                // updated last
                continue;
            } else {
                // update the non-pivot rows
                // copy the pivot column, unmodified first case; all the rest of the updates depend on this
                let a_r_col = self.data[(r, col)].clone(); // clone here to avoid breaking borrow rules with self.data.set() below
                for j in 0..self.ncols {
                    if j == col {
                        // update modifies the current row and current column and does not depend on data updated in later
                        // iterations
                        let orig = &self.data[(r, col)];
                        // a frequent case in large SMT queries, but doesn't seem to help in cases where the dense impl performs well
                        // if orig.is_zero() { continue }
                        self.data[(r, j)] = orig * &inv_a_row_col;
                    } else {
                        // update depends on original data in the pivot row and column
                        self.data[(r, j)] = &self.data[(r, j)]
                            - &self.data[(row, j)] // pivot row is updated last so this is original data
                                    * a_r_col.clone()  // current row & pivot column has been copied from original
                                    * &inv_a_row_col;
                    }
                }
            }
        }

        // update the pivot row
        #[allow(clippy::needless_range_loop)] // lint suggestion forces violation of borrow rules
        for j in 0..self.ncols {
            // both updates do not depend on data in the tableau which will be updated in later iterations
            if j == col {
                self.data[(row, j)] = inv_a_row_col.clone();
            } else {
                let orig = &self.data[(row, j)];
                // if orig.is_zero() { continue }
                self.data[(row, j)] = -orig * &inv_a_row_col;
            }
        }
        Ok(())
    }

    fn get(&self, row: usize, col: usize) -> TableauResult<&Rational> {
        self.data
            .get(row, col)
            .ok_or(TableauError("dense tableau get out of bounds".to_string()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arithmetic::lia::types::rbig;

    #[test]
    fn pivot_2x3() {
        // general form tableau for (x0 + 6 x2 = 0) //\ (x1 + (-1/2) x2 = 0)
        //
        //       x2
        //    /----
        // x0 |  -6
        // x1 | 1/2
        let data = [vec![rbig!(-6)], vec![rbig!(1 / 2)]];
        let mut tab = TableauDense::from_rows(&data).unwrap();

        // Note: col = 0 here because x2 owns column zero in the reduced table representation
        tab.pivot(0, 0).unwrap();

        // Result after pivot(x0, x2): (x2 + 1/2 6 x0 = 0) //\ (x1 + (1/12) x2 = 0)
        //
        //         x0
        //    /------
        // x2 |  -1/6
        // x1 | -1/12
        let expected_data = [vec![rbig!(-1 / 6)], vec![rbig!(-1 / 12)]];
        let expected_tab = TableauDense::from_rows(&expected_data).unwrap();
        assert_eq!(tab, expected_tab);
    }

    // 3x2 tableau example from [DP]
    #[test]
    fn pivot_example_5_6() {
        let data = [
            vec![rbig!(1), rbig!(1)],
            vec![rbig!(2), rbig!(-1)],
            vec![rbig!(-1), rbig!(2)],
        ];
        let mut tab = TableauDense::from_rows(&data).unwrap();

        tab.pivot(0, 0).unwrap();

        // originally a bug here with pivot row, non-pivot column element
        let expected_data = [
            vec![rbig!(1), rbig!(-1)],
            vec![rbig!(2), rbig!(-3)], //  2 1
            vec![rbig!(-1), rbig!(3)], // -1 1
        ];
        let expected_tab = TableauDense::from_rows(&expected_data).unwrap();
        assert_eq!(tab, expected_tab);
    }

    // 3x2 tableau example from an infeasible system
    #[test]
    fn pivot_example_from_infeasible_system() {
        let data = [
            vec![rbig!(1), rbig!(0)],
            vec![rbig!(0), rbig!(1)],
            vec![rbig!(-1), rbig!(-1)],
        ];
        let mut tab = TableauDense::from_rows(&data).unwrap();

        tab.pivot(2, 0).unwrap();

        let expected_data = [
            vec![rbig!(-1), rbig!(-1)],
            vec![rbig!(0), rbig!(1)],
            vec![rbig!(-1), rbig!(-1)],
        ];
        let expected_tab = TableauDense::from_rows(&expected_data).unwrap();
        assert_eq!(tab, expected_tab);
    }
}
