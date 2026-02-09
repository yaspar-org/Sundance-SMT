// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! todo:

use crate::arithmetic::lia::sparse;
use crate::arithmetic::lia::types::Rational;

/// todo:
#[allow(dead_code)]
#[derive(Debug)]
pub struct TableauSparse {
    matrix: sparse::Matrix<Rational>,
}
