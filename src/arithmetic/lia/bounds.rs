// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Bounds for rational and integer variables over a generic num type (usually QDelta in
//! practice).

use std::fmt::Display;

/// Bounds Interpreted as an inclusive interval with endpoints in a numerical type union
/// {+inf, -inf}
#[derive(Clone, Debug)]
pub struct Bounds<T> {
    /// lower bound; none means no bound
    pub lower: Option<T>,
    /// upper bound; none means no bound
    pub upper: Option<T>,
}

impl<T> Bounds<T> {
    /// Construct new bounds from optional lower and upper values
    pub fn new(lower: Option<T>, upper: Option<T>) -> Self {
        Self { lower, upper }
    }

    /// Construct a simple lower bound
    pub fn above_of(val: impl Into<T>) -> Self {
        Self {
            lower: Some(val.into()),
            upper: None,
        }
    }

    /// Construct an simple upper bound
    pub fn below_of(val: impl Into<T>) -> Self {
        Self {
            lower: None,
            upper: Some(val.into()),
        }
    }

    /// Construct a Bounds that is unbounded both above and below
    pub fn unbounded() -> Self {
        Self {
            lower: None,
            upper: None,
        }
    }
}

impl<T: Ord> Bounds<T> {
    /// Determine if `val` is (inclusively) inside the bounds
    pub fn in_bounds(&self, val: &T) -> bool {
        if let Some(lower) = self.lower.as_ref()
            && *val < *lower
        {
            // short circuit if the lower bound is violated
            return false;
        }
        if let Some(upper) = self.upper.as_ref()
            && *val > *upper
        {
            return false;
        }
        true
    }

    /// Determine if `val` is strictly above the upper bound
    ///
    /// ```
    /// use sundance_smt::arithmetic::lia::bounds::Bounds;
    /// use dashu::rbig;
    /// let b = Bounds::new(Some(rbig!(0)), Some(rbig!(5)));
    /// assert!(!b.above_upper(&rbig!(-10_000)));
    /// assert!(b.above_upper(&rbig!(10)));
    /// assert!(!b.above_upper(&rbig!(5)));
    /// let ub = Bounds::unbounded();
    /// assert!(!ub.above_upper(&rbig!(10_000))); // any value makes this assertion true
    /// ```
    pub fn above_upper(&self, val: &T) -> bool {
        self.upper.as_ref().is_some_and(|u| u < val)
    }

    /// Determine if `val` is strictly below the upper bound
    ///
    /// ```
    /// use sundance_smt::arithmetic::lia::bounds::Bounds;
    /// use dashu::rbig;
    /// let b = Bounds::new(Some(rbig!(0)), Some(rbig!(5)));
    /// assert!(b.below_upper(&rbig!(-10_000)));
    /// assert!(!b.below_upper(&rbig!(10)));
    /// assert!(b.below_upper(&rbig!(4)));
    /// assert!(!b.below_upper(&rbig!(5)));
    /// let ub = Bounds::unbounded();
    /// assert!(ub.below_upper(&rbig!(10_000))); // any value makes this assertion true
    /// ```
    pub fn below_upper(&self, val: &T) -> bool {
        self.upper.as_ref().is_none_or(|u| val < u)
    }

    /// Determine if `val` is strictly below the lower bound
    ///
    /// ```
    /// use sundance_smt::arithmetic::lia::bounds::Bounds;
    /// use dashu::rbig;
    /// let b = Bounds::new(Some(rbig!(0)), Some(rbig!(5)));
    /// assert!(b.below_lower(&rbig!(-10_000)));
    /// assert!(!b.below_lower(&rbig!(10)));
    /// assert!(!b.below_lower(&rbig!(0)));
    /// let ub = Bounds::unbounded();
    /// assert!(!ub.below_lower(&rbig!(-10_000))); // any value makes this assertion true
    /// ```
    pub fn below_lower(&self, val: &T) -> bool {
        self.lower.as_ref().is_some_and(|l| val < l)
    }

    /// Determine if `val` is strictly above the lower bound
    ///
    /// ```
    /// use sundance_smt::arithmetic::lia::bounds::Bounds;
    /// use dashu::rbig;
    /// let b = Bounds::new(Some(rbig!(0)), Some(rbig!(5)));
    /// assert!(b.above_lower(&rbig!(10_000)));
    /// assert!(!b.above_lower(&rbig!(-10)));
    /// assert!(b.above_lower(&rbig!(1)));
    /// assert!(!b.above_lower(&rbig!(0)));
    /// let ub = Bounds::unbounded();
    /// assert!(ub.above_lower(&rbig!(-10_000))); // any value makes this assertion true
    /// ```
    pub fn above_lower(&self, val: &T) -> bool {
        self.lower.as_ref().is_none_or(|l| l < val)
    }
}

impl<T> Default for Bounds<T> {
    fn default() -> Self {
        Bounds::<T>::unbounded()
    }
}

impl<T: Display> Display for Bounds<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match (&self.lower, &self.upper) {
            (Some(l), Some(u)) => write!(f, "{l} <= · <= {u}"),
            (Some(l), None) => write!(f, "{l} <= ·"),
            (None, Some(u)) => write!(f, "· <= {u}"),
            (None, None) => write!(f, "-inf < · < inf"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arithmetic::lia::types::rbig;

    #[test]
    fn check_bounds_finite() {
        let b = Bounds::new(Some(rbig!(0)), Some(rbig!(5)));
        // in bounds
        assert!(b.in_bounds(&rbig!(0)));
        assert!(b.in_bounds(&rbig!(1 / 3)));
        assert!(b.in_bounds(&rbig!(5)));
        // not in bounds
        assert!(!b.in_bounds(&rbig!(-1)));
        assert!(!b.in_bounds(&rbig!(35 / 4)));
    }

    #[test]
    fn check_bounds_infinite() {
        let b = Bounds::new(None, Some(rbig!(0)));
        // in bounds
        assert!(b.in_bounds(&rbig!(-1 / 5)));
        assert!(b.in_bounds(&rbig!(0)));
        // not in bounds
        assert!(!b.in_bounds(&rbig!(5)));
        assert!(!b.in_bounds(&rbig!(1 / 3)));
    }
}
