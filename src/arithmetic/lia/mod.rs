// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! LIA Arithmetic Solver
//!
//! TODO: more detailed Markdown documentation of the crate
#![warn(missing_docs, missing_debug_implementations, rust_2018_idioms)]

pub mod bounds;
pub mod context;
pub mod frontend;
pub mod linear_system;
pub mod lira_solver;
pub mod lra_solver;
pub mod preprocess;
pub mod qdelta;
pub mod solver_result;
pub mod solver_result_api;
pub mod sparse;
pub mod tableau;
pub mod tableau_dense;
pub mod tableau_sparse;
pub mod types;
pub mod utils;
pub mod variables;
