// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Implementation of rationals with symbolic infinitesimal parameter
//!
//! Q_δ is the set of elements a + b δ where a, b are rational and δ is
//! a symbolic parameter. δ should be thought of as an arbitrarily small rational
//! value.
//!
//! Operations:
//!
//! (a + b δ) + (c + d δ) = (a + c) + (b + d) δ
//! For k in Q, k * (a + b δ) = ka + kb δ
//! a + b δ = c + d δ <==> (a = c) and (b = d)
//! a + b δ <= c + d δ <==> (a < c) or (a == c and b <= d)
//!

use dashu::{Integer, Rational};
use std::cmp;
use std::fmt;
use std::ops;

use num_traits::Zero;

use crate::arithmetic::lia::bounds::Bounds;

/// Q_δ is the set of elements `rat + inf δ` where rat, inf are rational and δ is
/// a symbolic parameter
#[derive(fmt::Debug, Clone)]
pub struct QDelta {
    rat: Rational,
    inf: Rational,
}

impl QDelta {
    /// [QDelta] with value zero
    pub const ZERO: Self = QDelta {
        rat: Rational::ZERO,
        inf: Rational::ZERO,
    };

    /// [QDelta] with rational value 1
    pub const ONE: Self = QDelta {
        rat: Rational::ONE,
        inf: Rational::ZERO,
    };

    /// [QDelta] with delta value 1
    pub const DELTA: Self = QDelta {
        rat: Rational::ZERO,
        inf: Rational::ONE,
    };

    /// Build a new Q_δ with given rational and infinitesimal parts
    pub fn new(rat: impl Into<Rational>, inf: impl Into<Rational>) -> Self {
        Self {
            rat: rat.into(),
            inf: inf.into(),
        }
    }

    /// Get the rational part of `self`
    pub fn rat(&self) -> &Rational {
        &self.rat
    }

    /// Get the infinitesimal part of `self`
    pub fn inf(&self) -> &Rational {
        &self.inf
    }

    /// Instantiate at a concrete value of delta
    pub fn instantiate(&self, delta: &Rational) -> Rational {
        self.rat.clone() + self.inf.clone() * delta
    }

    /// Value has zero infinitesimal part and rational part zero
    pub fn is_int(&self) -> bool {
        self.rat.is_int() && self.inf.is_zero()
    }

    /// Return the integer floor of self
    ///
    /// floor(a + b δ) = { floor(a) if a not in Z, a if a in Z and b >= 0, a-1 if a in Z and b < 0 }
    ///
    /// This is equivalent to floor(a + b δ) := the largest integer less or equal to a + b δ.
    ///
    /// Examples:
    ///
    /// ```rust
    /// use dashu::{rbig, ibig};
    /// use sundance_smt::arithmetic::lia::qdelta::*;
    ///
    /// let x = QDelta::new(1,1);
    /// let y = QDelta::new(1,-1);
    /// let z = QDelta::new(rbig!(1/3),1);
    /// let w = QDelta::new(rbig!(10/3),-1);
    ///
    /// assert_eq!(x.floor(), ibig!(1));  // 1 == self.rat
    /// assert_eq!(y.floor(), ibig!(0));  // 0 == self.rat - 1
    /// assert_eq!(z.floor(), ibig!(0));  // 0 == floor(1/3)
    /// assert_eq!(w.floor(), ibig!(3));  // 3 == floor(10/3)
    /// ```
    ///
    pub fn floor(&self) -> Integer {
        if self.rat.is_int() {
            if self.inf >= Rational::ZERO {
                self.rat.numerator().clone()
            } else {
                self.rat.numerator() - Integer::ONE
            }
        } else {
            self.rat.floor()
        }
    }
}

impl Zero for QDelta {
    fn zero() -> Self {
        Self::ZERO
    }

    fn is_zero(&self) -> bool {
        self.rat.is_zero() && self.inf.is_zero()
    }
}

impl Default for QDelta {
    fn default() -> Self {
        Self::ZERO
    }
}

impl PartialEq for QDelta {
    fn eq(&self, other: &QDelta) -> bool {
        self.rat == other.rat && self.inf == other.inf
    }
}

impl Eq for QDelta {}

/// A less than or equal relation is defined as:
///
/// a + b δ <= c + d δ <==> (a < c) or (a == c and b <= d)
///
/// This defines a partial order on Q_δ
///
/// This relation is:
/// * reflexive: forall a,b: (a < a) or (a == a and b <= b). The rhs is always true.
/// * anti-symmetric, for example:
///
///   (a + b δ) <= (c + d δ) and (c + d δ) <= (a + b δ)
///   ((a < c) or (a == c and b <= d)) and ((c < a) or (c == a and d <= b))
///   one disjunct in each conjunct must be true
///   cases:
///   - a < c, c > a: absurd
///   - a < c, c == a and d <= b: absurd
///   - (a == c and b <= d), c < a: absurd
///   - (a = c and b <= d), (c = a and d <= b): deduce a = c and b = d
///
/// * transitive: proof left to the reader
///
/// Note, Equality is derived: `a + b δ = c + d δ <==> (a = c) and (b = d)`
impl Ord for QDelta {
    /// ```rust
    /// use sundance_smt::arithmetic::lia::qdelta::*;
    ///
    /// let x = QDelta::new(1, 1);
    /// let y = QDelta::new(1, 2);
    /// assert_eq!(x, x); // derived equality is reflexive
    /// assert_ne!(x, y);
    /// assert!(x <= x); // `le` is reflexive
    /// assert!(x <= y);
    /// assert!(!(y <= x));
    /// ```
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.rat.cmp(&other.rat).then(self.inf.cmp(&other.inf))
    }
}

impl PartialOrd for QDelta {
    fn partial_cmp(&self, other: &QDelta) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Display for QDelta {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} + {} δ", self.rat, self.inf)
    }
}

impl From<Rational> for QDelta {
    fn from(value: Rational) -> Self {
        QDelta {
            rat: value,
            inf: Rational::ZERO,
        }
    }
}

impl From<Integer> for QDelta {
    fn from(value: Integer) -> Self {
        QDelta {
            rat: value.into(),
            inf: Rational::ZERO,
        }
    }
}

impl From<i32> for QDelta {
    fn from(value: i32) -> Self {
        QDelta {
            rat: value.into(),
            inf: Rational::ZERO,
        }
    }
}

impl ops::Add for &QDelta {
    type Output = QDelta;

    fn add(self, rhs: Self) -> Self::Output {
        QDelta {
            rat: self.rat.clone() + rhs.rat.clone(),
            inf: self.inf.clone() + rhs.inf.clone(),
        }
    }
}

/// TODO: dry
impl ops::Add for QDelta {
    type Output = QDelta;

    fn add(self, rhs: Self) -> Self::Output {
        QDelta {
            rat: self.rat + rhs.rat,
            inf: self.inf + rhs.inf,
        }
    }
}

impl ops::Sub for &QDelta {
    type Output = QDelta;

    fn sub(self, rhs: Self) -> Self::Output {
        QDelta {
            rat: self.rat.clone() - rhs.rat.clone(),
            inf: self.inf.clone() - rhs.inf.clone(),
        }
    }
}

/// TODO: dry
impl ops::Sub for QDelta {
    type Output = QDelta;

    fn sub(self, rhs: Self) -> Self::Output {
        QDelta {
            rat: self.rat - rhs.rat,
            inf: self.inf - rhs.inf,
        }
    }
}

/// Multiply a Q_δ on the left by a rational: a * d for a in Q, d in Q_δ
///
/// ```rust
/// use dashu::rbig;
/// use sundance_smt::arithmetic::lia::qdelta::*;
///
/// let x = QDelta::new(1, rbig!(1/2));
/// assert_eq!(x * &rbig!(2), QDelta::new(2, 1));
/// ```
impl ops::Mul<&Rational> for QDelta {
    type Output = Self;

    fn mul(self, rhs: &Rational) -> Self::Output {
        QDelta {
            rat: self.rat * rhs,
            inf: self.inf * rhs,
        }
    }
}

/// TODO: dry
impl ops::Mul<&Rational> for &QDelta {
    type Output = QDelta;

    fn mul(self, rhs: &Rational) -> Self::Output {
        QDelta {
            rat: self.rat.clone() * rhs,
            inf: self.inf.clone() * rhs,
        }
    }
}

impl Bounds<Rational> {
    /// Inject bounds over Q into bounds over Q_δ. Unfortunately implementing
    /// `From<Bounds<Rational>>` for `Bounds<QDelta>` isn't possible b/c of conflict
    /// with blanket impl from core.
    #[inline]
    pub fn inject_bounds(&self) -> Bounds<QDelta> {
        Bounds {
            lower: self.lower.clone().map(|l| l.into()),
            upper: self.upper.clone().map(|u| u.into()),
        }
    }
}

impl Bounds<QDelta> {
    /// Project bounds over Q_δ onto the line `δ = delta` =~ Q
    #[inline]
    pub fn project_bounds(&self, delta: &Rational) -> Bounds<Rational> {
        Bounds {
            lower: self.lower.clone().map(|l| l.instantiate(delta)),
            upper: self.upper.clone().map(|u| u.instantiate(delta)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arithmetic::lia::bounds::Bounds;
    use dashu::rbig;

    #[test]
    fn qdelta_arith() {
        let x = QDelta::new(1, 1);
        let y = QDelta::new(1, 2);
        let z = QDelta::new(0, 1);

        assert_eq!(&x + &y, QDelta::new(2, 3));
        assert_eq!(&x - &y, QDelta::new(0, -1));
        assert_eq!(&x + &z, y);

        assert_eq!(x * &rbig!(2), QDelta::new(2, 2));
        assert_eq!(y * &rbig!(1 / 2), QDelta::new(rbig!(1 / 2), 1));
        assert_eq!(z * &rbig!(1 / 2), QDelta::new(0, rbig!(1 / 2)));
    }

    #[test]
    fn qdelta_instantiate() {
        let x = QDelta::new(1, 1);
        assert_eq!(x.instantiate(&rbig!(1 / 100)), rbig!(101 / 100));
        assert_eq!(x.instantiate(&rbig!(0)), rbig!(1));
    }

    #[test]
    fn qdelta_bounds() {
        // full integer + δ above the lower bound
        let x = QDelta::new(1, 1);
        let bds = Bounds::above_of(QDelta::new(0, 0));
        assert!(bds.in_bounds(&x));
        assert!(!bds.above_upper(&x));
        assert!(!bds.below_lower(&x));

        // x is in bounds infinitesimally
        let x = QDelta::new(1, rbig!(1 / 2));
        let bds = Bounds::new(
            Some(QDelta::new(1, rbig!(1 / 3))),
            Some(QDelta::new(1, rbig!(2 / 3))),
        );
        assert!(bds.in_bounds(&x));
        assert!(!bds.above_upper(&x));
        assert!(!bds.below_lower(&x));
    }
}
