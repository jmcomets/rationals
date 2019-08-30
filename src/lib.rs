use std::mem;
use std::cmp::Ordering;
use std::ops::{Add, Sub, Mul, Div, Neg, AddAssign, SubAssign, MulAssign, DivAssign, BitXor};

#[cfg(feature = "use_bigint")]
type Integer = num_bigint::BigInt;

#[cfg(feature = "use_bigint")]
use num_traits::pow::Pow;

#[cfg(not(feature = "use_bigint"))]
type Integer = i64;

#[cfg(not(feature = "use_bigint"))]
pub const MAX: Integer = std::i64::MAX;

macro_rules! ensure_non_zero_division {
    ($x:expr) => {
        debug_assert!($x != 0.into(), "cannot divide by zero!");
    }
}

#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(not(feature = "use_bigint"), derive(Copy))]
pub struct Rational {
    numerator: Integer,
    denominator: Integer,
}

impl Rational {
    pub fn new<T, U>(numerator: T, denominator: U) -> Self
        where T: Into<Integer>,
              U: Into<Integer>,
    {
        let numerator = numerator.into();
        let denominator = denominator.into();

        ensure_non_zero_division!(denominator);

        let (numerator, denominator) = simplify_fraction(numerator, denominator);

        Rational { numerator, denominator }
    }

    pub fn with_numerator<T>(numerator: T) -> Self
        where T: Into<Integer>,
    {
        let numerator = numerator.into();
        let denominator = 1.into();

        Rational { numerator, denominator }
    }

    #[inline]
    pub fn zero() -> Self {
        0.into()
    }

    #[inline]
    pub fn one() -> Self {
        1.into()
    }

    #[inline]
    pub fn invert(mut self) -> Self {
        ensure_non_zero_division!(self.numerator);
        mem::swap(&mut self.numerator, &mut self.denominator);
        self
    }

    pub fn pow(mut self, exponent: i32) -> Self {
        if exponent >= 0 {
            let exponent = exponent as u32;
            self.numerator = self.numerator.pow(exponent);
            self.denominator = self.denominator.pow(exponent);
            self
        } else {
            self.invert() ^ -exponent
        }
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let n1 = self.numerator.clone() * other.denominator.clone();
        let n2 = other.numerator.clone() * self.denominator.clone();

        n1.partial_cmp(&n2)
    }
}

impl Neg for Rational {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Rational {
            numerator: -self.numerator,
            denominator: self.denominator,
        }
    }
}

impl Add for Rational {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        let n1 = self.numerator * other.denominator.clone();
        let n2 = other.numerator * self.denominator.clone();

        let d = self.denominator * other.denominator;

        Rational::new(n1 + n2, d)
    }
}

impl AddAssign for Rational {
    fn add_assign(&mut self, other: Self) {
        *self = self.clone() + other;
    }
}

impl Sub for Rational {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        self + other.neg()
    }
}

impl SubAssign for Rational {
    fn sub_assign(&mut self, other: Self) {
        *self = self.clone() - other;
    }
}

impl Mul for Rational {
    type Output = Self;

    fn mul(self, other: Self) -> Self::Output {
        let n = self.numerator * other.numerator;
        let d = self.denominator * other.denominator;

        Rational::new(n, d)
    }
}

impl MulAssign for Rational {
    fn mul_assign(&mut self, other: Self) {
        *self = self.clone() * other;
    }
}

impl Div for Rational {
    type Output = Self;

    fn div(self, other: Self) -> Self::Output {
        self * other.invert()
    }
}

impl DivAssign for Rational {
    fn div_assign(&mut self, other: Self) {
        *self = self.clone() / other;
    }
}

pub trait IntoRational {
    fn into_rational(self) -> Rational;
}

macro_rules! impls_for_integers {
    ($($t:ty),*) => {
        $(
            impl IntoRational for $t {
                fn into_rational(self) -> Rational {
                    Rational::with_numerator(self)
                }
            }

            impl From<$t> for Rational {
                fn from(n: $t) -> Self {
                    n.into_rational()
                }
            }

            impl BitXor<$t> for Rational {
                type Output = Self;

                fn bitxor(self, exponent: $t) -> Self::Output {
                    self.pow(exponent as i32)
                }
            }

            impl Add<$t> for Rational {
                type Output = Self;

                fn add(self, other: $t) -> Self::Output {
                    self.add(other.into_rational())
                }
            }

            impl AddAssign<$t> for Rational {
                fn add_assign(&mut self, other: $t) {
                    self.add_assign(other.into_rational())
                }
            }

            impl Sub<$t> for Rational {
                type Output = Self;

                fn sub(self, other: $t) -> Self::Output {
                    self.sub(other.into_rational())
                }
            }

            impl SubAssign<$t> for Rational {
                fn sub_assign(&mut self, other: $t) {
                    self.sub_assign(other.into_rational())
                }
            }

            impl Mul<$t> for Rational {
                type Output = Self;

                fn mul(self, other: $t) -> Self::Output {
                    self.mul(other.into_rational())
                }
            }

            impl MulAssign<$t> for Rational {
                fn mul_assign(&mut self, other: $t) {
                    self.mul_assign(other.into_rational())
                }
            }

            impl Div<$t> for Rational {
                type Output = Self;

                fn div(self, other: $t) -> Self::Output {
                    self.div(other.into_rational())
                }
            }

            impl DivAssign<$t> for Rational {
                fn div_assign(&mut self, other: $t) {
                    self.div_assign(other.into_rational())
                }
            }
        )*
    }
}

impls_for_integers!(i8, i16, i32, i64);

fn gcd(a: Integer, b: Integer) -> Integer {
    let (mut a, mut b) = if a > b {
        (a, b)
    } else {
        (b, a)
    };

    while b != 0.into() {
        let r = a % &b;
        a = b;
        b = r;
    }

    a
}

fn simplify_fraction(numerator: Integer, denominator: Integer) -> (Integer, Integer) {
    let d = gcd(numerator.clone(), denominator.clone());

    let mut numerator = numerator / &d;
    let mut denominator = denominator / &d;

    // ensure that the numerator is always holding the fraction's sign
    if denominator < 0.into() {
        denominator = -denominator;
        numerator = -numerator;
    }

    (numerator, denominator)
}

#[cfg(test)]
mod tests {
    use more_asserts::*;
    use super::*;

    #[test]
    fn operators() {
        assert_eq!(2.into_rational() + 2.into_rational(), 4.into_rational());
        assert_eq!(2.into_rational() - 2.into_rational(), 0.into_rational());
        assert_eq!(2.into_rational() * 2.into_rational(), 4.into_rational());
        assert_eq!(2.into_rational() / 2.into_rational(), 1.into_rational());

        assert_eq!(2.into_rational() + 2, 4.into_rational());
        assert_eq!(2.into_rational() - 2, 0.into_rational());
        assert_eq!(2.into_rational() * 2, 4.into_rational());
        assert_eq!(2.into_rational() / 2, 1.into_rational());

        // only RHS version is available
        //
        // assert_eq!(2 + 2.into_rational(), 4.into_rational());
        // assert_eq!(2 - 2.into_rational(), 0.into_rational());
        // assert_eq!(2 * 2.into_rational(), 4.into_rational());
        // assert_eq!(2 / 2.into_rational(), 1.into_rational());
    }

    #[test]
    fn division_by_integer() {
        assert_eq!(2.into_rational() / 3, Rational::new(2, 3));
    }

    #[test]
    fn sign() {
        assert_eq!(Rational::new(1, 1), Rational::new(-1, -1));
        assert_eq!(Rational::new(-1, 1), Rational::new(1, -1));
    }

    #[test]
    fn equality() {
        assert_eq!(1.into_rational(), 1.into_rational());
        assert_ne!(2.into_rational(), 3.into_rational());
        assert_eq!(0.into_rational() / 3, 0.into_rational() / 4);
        assert_eq!(0.into_rational(), -0.into_rational());
    }

    #[test]
    fn comparison() {
        assert_lt!(2.into_rational(), 3.into_rational());
        assert_lt!(2.into_rational() / 3, 3.into_rational() / 4);
        assert_le!(1.into_rational(), 1.into_rational());
    }

    #[test]
    #[should_panic]
    fn cannot_have_zero_denominator() {
        let _ = Rational::new(1, 0);
    }

    #[test]
    #[should_panic]
    fn zero_cannot_be_inverted() {
        let _ = Rational::new(0, 1).invert();
    }

    #[test]
    #[should_panic]
    fn cannot_divide_by_zero() {
        let _ = Rational::one() / Rational::zero();
    }

    #[test]
    fn simplification() {
        let a = Rational::new(2, 3);
        let b = Rational::new(4, 6);
        assert_eq!(a, b);
    }

    #[test]
    fn negation() {
        assert_eq!(-(2.into_rational()), -2.into_rational());
    }

    #[test]
    fn exponents() {
        assert_eq!(2.into_rational() ^ 2, Rational::new(4, 1));
        assert_eq!(2.into_rational() ^ -2, Rational::new(1, 4));
        assert_eq!(42.into_rational() ^ 0, Rational::one());
    }

    #[test]
    fn integer_conversions_are_lossless() {
        assert_eq!(std::i8::MAX as u32,  (std::u8::MAX  >> 1) as u32);
        assert_eq!(std::i16::MAX as u32, (std::u16::MAX >> 1) as u32);
        assert_eq!(std::i32::MAX as u32, (std::u32::MAX >> 1) as u32);
        assert_eq!(std::i64::MAX as u32, (std::u64::MAX >> 1) as u32);
    }

    fn fact<T: Into<Rational>>(n: T) -> Rational {
        let n: Rational = n.into();
        //println!("factorial({:?})", &n);
        let one = Rational::one();
        if n <= one {
            return one;
        }
        n.clone() * fact(n - 1)
    }

    #[test]
    fn factorial() {
        assert_eq!(fact(0), 1.into());
        assert_eq!(fact(1), 1.into());
        assert_eq!(fact(2), 2.into());
        assert_eq!(fact(3), 6.into());
        assert_eq!(fact(4), 24.into());
    }
}
