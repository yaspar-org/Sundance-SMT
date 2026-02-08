#![allow(dead_code)]

use crate::arithmetic::lia::sparse;
use crate::arithmetic::lia::types::Rational;

pub struct TableauSparse {
    matrix: sparse::Matrix<Rational>,
}
