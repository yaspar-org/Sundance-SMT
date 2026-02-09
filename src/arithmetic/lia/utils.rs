// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Utility functions
use dashu::Integer;
use dashu::base::Gcd;

/// Compute the least common multiple of two integers.
pub fn lcm(x: &Integer, y: &Integer) -> Integer {
    x * y / x.gcd(y)
}
