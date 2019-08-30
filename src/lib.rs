use std::mem;
use std::ops::{Add, Sub, Mul, Div, Neg, AddAssign, SubAssign, MulAssign, DivAssign, BitXor};

#[cfg(feature = "use_bigint")]
type Integer = num_bigint::BigInt;

#[cfg(feature = "use_bigint")]
use num_traits::pow::Pow;

#[cfg(not(feature = "use_bigint"))]
type Integer = i64;

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
        Rational::with_numerator(0)
    }

    #[inline]
    pub fn one() -> Self {
        Rational::with_numerator(1)
    }

    #[inline]
    pub fn inverted(mut self) -> Self {
        ensure_non_zero_division!(self.numerator);
        mem::swap(&mut self.numerator, &mut self.denominator);
        self
    }
}

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

    let numerator = numerator / &d;
    let denominator = denominator / &d;

    (numerator, denominator)
}

trait IntoRational {
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

                fn bitxor(mut self, exponent: $t) -> Self::Output {
                    if exponent >= 0 {
                        let exponent = exponent as u32;
                        self.numerator = self.numerator.pow(exponent);
                        self.denominator = self.denominator.pow(exponent);
                        self
                    } else {
                        self.inverted() ^ -exponent
                    }
                }
            }
        )*
    }
}

impls_for_integers!(i8, i16, i32, i64);

impl Neg for Rational {
    type Output = Self;

    fn neg(self) -> Self::Output {
        let Rational { numerator, denominator } = self;
        let numerator = -numerator;
        Rational { numerator, denominator }
    }
}

macro_rules! add_with {
    ($a:expr, $b:expr, $op:tt) => {
        {
            let Rational { numerator: n1, denominator: d1 } = $a;
            let Rational { numerator: n2, denominator: d2 } = $b;

            let numerator = n1 * &d2 $op n2 * &d1;
            let denominator = d1 * d2;

            Rational::new(numerator, denominator)
        }
    }
}

impl Add for Rational {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        add_with!(self, other, +)
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
        add_with!(self, other, -)
    }
}

impl SubAssign for Rational {
    fn sub_assign(&mut self, other: Self) {
        *self = self.clone() - other;
    }
}

macro_rules! mul_with {
    ($a:expr, $b:expr, $op:tt) => {
        {
            let Rational { numerator: n1, denominator: d1 } = $a;
            let Rational { numerator: n2, denominator: d2 } = $b;

            let numerator = n1 $op n2;
            let denominator = d1 $op d2;

            Rational::new(numerator, denominator)
        }
    }
}

impl Mul for Rational {
    type Output = Self;

    fn mul(self, other: Self) -> Self::Output {
        mul_with!(self, other, *)
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
        ensure_non_zero_division!(other.denominator);
        mul_with!(self, other, /)
    }
}

impl DivAssign for Rational {
    fn div_assign(&mut self, other: Self) {
        *self = self.clone() / other;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn operators() {
        assert_eq!(2.into_rational() + 2.into_rational(), 4.into_rational());
        assert_eq!(2.into_rational() - 2.into_rational(), 0.into_rational());
        assert_eq!(2.into_rational() * 2.into_rational(), 4.into_rational());
        assert_eq!(2.into_rational() / 2.into_rational(), 1.into_rational());
    }

    #[test]
    fn equality() {
        assert_ne!(2.into_rational(), 3.into_rational());
    }

    #[test]
    #[should_panic]
    fn cannot_have_zero_denominator() {
        let _ = Rational::new(1, 0);
    }

    #[test]
    #[should_panic]
    fn zero_cannot_be_inverted() {
        let _ = Rational::new(0, 1).inverted();
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
}
