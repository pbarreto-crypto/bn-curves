#[cfg(not(any(target_pointer_width = "64")))]
compile_error!("this crate requires 64-bit limbs");

use crate::bnfp::BNFp;
use crate::bnfp2::BNFp2;
use crate::bnparam::BNParam;
use crate::traits::{BNField, One};
use crypto_bigint::{Random, Uint, Word, Zero};
use crypto_bigint::rand_core::{RngCore, TryRngCore};
use crypto_bigint::subtle::{Choice, ConditionallySelectable, ConstantTimeEq};
use std::fmt::{Debug, Display, Formatter};
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

/// The <b>F</b><sub><i>p&#x2076;</i></sub> = <b>F</b><sub><i>p&sup2;</i></sub>&lbrack;<i>w</i>&rbrack;/&lt;<i>w&sup3; - &xi;</i>&gt;
/// extension field, with <i>&xi;</i> = <i>1 + i</i>.
/// NB: <i>w&sup3;</i> = <i>&xi;</i>.
pub struct BNFp6<BN: BNParam, const LIMBS: usize> {
    pub(crate) v0: BNFp2<BN, LIMBS>,
    pub(crate) v1: BNFp2<BN, LIMBS>,
    pub(crate) v2: BNFp2<BN, LIMBS>,
}

/*
// the Litany of All Saints:
pub type BN062Fp6 = BNFp6<BN062Param, 1>;
pub type BN126Fp6 = BNFp6<BN126Param, 2>;
pub type BN190Fp6 = BNFp6<BN190Param, 3>;
pub type BN254Fp6 = BNFp6<BN254Param, 4>;
pub type BN318Fp6 = BNFp6<BN318Param, 5>;
pub type BN382Fp6 = BNFp6<BN382Param, 6>;
pub type BN446Fp6 = BNFp6<BN446Param, 7>;
pub type BN510Fp6 = BNFp6<BN510Param, 8>;
pub type BN574Fp6 = BNFp6<BN574Param, 9>;
pub type BN638Fp6 = BNFp6<BN638Param, 10>;
pub type BN702Fp6 = BNFp6<BN702Param, 11>;
pub type BN766Fp6 = BNFp6<BN766Param, 12>;
// */


impl<BN: BNParam, const LIMBS: usize> BNFp6<BN, LIMBS> {
    /// Map an <b>F</b><sub><i>p&sup2;</i></sub> element to its <b>F</b><sub><i>p&#x2076;</i></sub> counterpart.
    #[inline]
    pub(crate) fn from_base(v0: BNFp2<BN, LIMBS>) -> Self {
        Self {
            v0, v1: BNFp2::zero(), v2: BNFp2::zero()
        }
    }

    /// Assemble an <b>F</b><sub><i>p&#x2076;</i></sub> element from its components.
    #[inline]
    pub(crate) fn from(v0: BNFp2<BN, LIMBS>, v1: BNFp2<BN, LIMBS>, v2: BNFp2<BN, LIMBS>) -> Self {
        Self {
            v0, v1, v2
        }
    }

    /// Compute <i>`self`</i><sup>(<i>p&sup2;</i>)<i>&#x1D50;</i></sup>,
    /// the <i>m</i>-th conjugate in <b>F</b><sub><i>p&#x2076;</i></sub> of `self`
    /// over <i><b>F</b><sub>p&sup2;</sub></i>, for <i>0 &leq; m &lt; 3</i>.
    #[inline]
    pub(crate) fn conj(&self, m: usize) -> Self {
        /*
         * w^(p^2)  = zeta0*w
         * w^(p^4)  = zeta1*w
         * w^(p^6)  = w
         *
         * v        = v_0 + v_1 w       + v_2 w^2 =>
         * v^(p^2)  = v_0 + v_1*zeta0 w + v_2*zeta1 w^2
         * v^(p^4)  = v_0 + v_1*zeta1 w + v_2*zeta0 w^2
         */
        assert!(m < 6);
        let zeta0 = BNFp::from_words(<[Word; LIMBS]>::try_from(BN::ZETA).unwrap());
        let zeta1 = -(zeta0 + BNFp::one());
        let (v0, v1, v2) = match m {
            0 => (self.v0, self.v1, self.v2),
            1 => (self.v0, zeta0*self.v1, zeta1*self.v2),
            2 => (self.v0, zeta1*self.v1, zeta0*self.v2),
            _ => (self.v0, self.v1, self.v2)  // just to make the compiler happy
        };
        Self {
            v0, v1, v2
        }
    }

    /// Compute the <b>F</b><sub><i>p&sup2;</i></sub>-norm of this <b>F</b><sub><i>p&#x2076;</i></sub> element.
    #[inline]
    pub(crate) fn norm(&self) -> BNFp2<BN, LIMBS> {
        // |v| = v*v.conj(1)*v.conj(2)
        //
        // v.conj(1)*v.conj(2) = (v_0 + v_1*zeta0 w + v_2*zeta1 w^2)*(v_0 + v_1*zeta1 w + v_2*zeta0 w^2) =
        // v_0^2            + v_0*v_1*zeta1 w + v_0*v_2*zeta0 w^2 +
        // v_1*v_2*zeta1*xi + v_0*v_1*zeta0 w + v_1^2         w^2 +
        // v_1*v_2*zeta0*xi + v_2^2*xi      w + v_0*v_2*zeta1 w^2 =
        // (v_0^2 - v_1*v_2*xi) + (v_2^2*xi - v_0*v_1) w + (v_1^2 - v_0*v_2) w^2
        //
        // v*v.conj(1)*v.conj(2) =
        // (v_0 + v_1 w + v_2 w^2)*((v_0^2 - v_1*v_2*xi) + (v_2^2*xi - v_0*v_1) w + (v_1^2 - v_0*v_2) w^2) =
        // (v_0^3 - v_0*v_1*v_2*xi)    + (v_0*v_2^2*xi - v_0^2*v_1) w + (v_0*v_1^2 - v_0^2*v_2)    w^2 +
        // (v_1^3 - v_0*v_1*v_2)*xi    + (v_1*v_0^2 - v_1^2*v_2*xi) w + (v_1*v_2^2*xi - v_0*v_1^2) w^2 +
        // (v_2^3*xi - v_0*v_1*v_2)*xi + (v_2*v_1^2 - v_0*v_2^2)*xi w + (v_2*v_0^2 - v_1*v_2^2*xi) w^2 =
        // v_0^3 + v_1^3*xi + v_2^3*xi*xi - 3*v_0*v_1*v_2*xi
        self.v0.cb() + (self.v1.cb() + (self.v2.sq().mul_xi() - 3*self.v0*self.v1)*self.v2).mul_xi()
    }

    /// Compute the product of this element and `rhs` using 3-way Karatsuba over <b>F</b><sub><i>p&sup2;</i></sub>.
    #[inline]
    fn kara3mul(&mut self, rhs: Self) {
        let t0 = self.v0*rhs.v0;
        let t1 = self.v1*rhs.v1;
        let t2 = self.v2*rhs.v2;
        let t3 = (self.v0 + self.v1)*(rhs.v0 + rhs.v1) - t0 - t1;
        let t4 = (self.v0 + self.v2)*(rhs.v0 + rhs.v2) - t0 - t2;
        let t5 = (self.v1 + self.v2)*(rhs.v1 + rhs.v2) - t1 - t2;
        self.v0 = t0 + t5.mul_xi();
        self.v1 = t3 + t2.mul_xi();
        self.v2 = t4 + t1;
    }

    /// Compute the square of this element using 3-way Karatsuba over <b>F</b><sub><i>p&sup2;</i></sub>.
    #[inline]
    fn kara3sqr(&self) -> Self {
        let t0 = self.v0.sq();
        let t1 = self.v1.sq();
        let t2 = self.v2.sq();
        let t3 = (self.v0 + self.v1).sq() - t0 - t1;
        let t4 = (self.v0 + self.v2).sq() - t0 - t2;
        let t5 = (self.v1 + self.v2).sq() - t1 - t2;
        Self {
            v0: t0 + t5.mul_xi(), v1: t3 + t2.mul_xi(), v2: t4 + t1
        }
    }

    /// Compute the product of this element and `rhs` using Toom-3 over <b>F</b><sub><i>p&sup2;</i></sub>.
    /// Notice: this tends to be slower than 3-way Karatsuba.
    #[inline]
    fn toom3mul(&mut self, fact: Self) {
        // evaluate the factors at 0, 1, -1, i, and ∞:
        let s = self.v0 + self.v2;
        let a = [self.v0, s + self.v1, s - self.v1, self.v0 - self.v2 + self.v1.mul_i(), self.v2];
        let s = fact.v0 + fact.v2;
        let b = [fact.v0, s + fact.v1, s - fact.v1, fact.v0 - fact.v2 + fact.v1.mul_i(), fact.v2];

        // interpolate:
        let c_0 = a[0]*b[0];
        let mut c_1 = (a[1]*b[1]).half();
        let mut c_2 = (a[2]*b[2]).half();
        let mut c_3 = (a[3]*b[3]).half();
        let c_4 = a[4]*b[4];

        let e_5 = c_0 + c_4;
        let (e_6, e_7) = c_1.jmul();
        let (e_8, e_9) = c_2.jmul();
        let e_10 = e_5.isub(c_3);
        c_2 += c_1 - e_5;
        c_1 = e_7 - e_8 + e_10;
        c_3 = e_6 - e_9 - e_10;

        // reduce:
        // c_0 + c_1 w + c_2 w^2 + c_3 w^3 + c_4 w^4 = (c_0 + c_3.xi) + (c_1 + c_4.xi) w + c_2 w^2
        self.v0 = c_0 + c_3.mul_xi();
        self.v1 = c_1 + c_4.mul_xi();
        self.v2 = c_2;
    }

    /// Compute the square of this element using Toom-3 over <b>F</b><sub><i>p&sup2;</i></sub>.
    /// Notice: this tends to be slower than 3-way Karatsuba.
    #[inline]
    fn toom3sqr(&self) -> Self  {
        // evaluate the factors at 0, 1, -1, i, and ∞:
        let s = self.v0 + self.v2;
        let a = [self.v0, s + self.v1, s - self.v1, self.v0 - self.v2 + self.v1.mul_i(), self.v2];

        // interpolate:
        let e = [a[0].sq(), a[1].sq().half(), a[2].sq().half(), a[3].sq().half(), a[4].sq()];
        let e_5 = e[0] + e[4];
        let (e_6, e_7) = e[1].jmul();
        let (e_8, e_9) = e[2].jmul();
        let e_10 = e_5.isub(e[3]);
        let c = [e[0], e_7 - e_8 + e_10, e[1] + e[2] - e_5, e_6 - e_9 - e_10, e[4]];

        // reduce:
        // c_0 + c_1 w + c_2 w^2 + c_3 w^3 + c_4 w^4 = (c_0 + c_3.xi) + (c_1 + c_4.xi) w + c_2 w^2
        Self {
            v0: e[0] + c[3].mul_xi(), v1: c[1] + c[4].mul_xi(), v2: c[2]
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> Add for BNFp6<BN, LIMBS> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let mut val = self;
        val += rhs;
        val
    }
}

impl<BN: BNParam, const LIMBS: usize> AddAssign for BNFp6<BN, LIMBS> {
    fn add_assign(&mut self, rhs: Self) {
        self.v0 += rhs.v0;
        self.v1 += rhs.v1;
        self.v2 += rhs.v2;
    }
}

impl<BN: BNParam, const LIMBS: usize> BNField for BNFp6<BN, LIMBS> {
    /// Convert `self` to serialized (byte array) representation.
    #[inline]
    fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = self.v0.to_bytes();
        let mut next = self.v1.to_bytes(); bytes.append(&mut next);
        let mut next = self.v2.to_bytes(); bytes.append(&mut next);
        bytes
    }

    /// Compute the value of twice this element.
    #[inline]
    fn double(&self) -> Self {
        Self {
            v0: self.v0.double(), v1: self.v1.double(), v2: self.v2.double()
        }
    }

    /// Compute the value of half this element.
    #[inline]
    fn half(&self) -> Self {
        Self {
            v0: self.v0.half(), v1: self.v1.half(), v2: self.v2.half()
        }
    }

    /// Compute the square of this <b>F</b><sub><i>p&#x2076;</i></sub> element.
    #[inline]
    fn sq(&self) -> Self {
        //*
        self.kara3sqr()
        // */
        /*
        self.toom3sqr()  // slower than 3-way Karatsuba
        // */
    }

    /// Compute the cube of this <b>F</b><sub><i>p&#x2076;</i></sub> element.
    #[inline]
    fn cb(&self) -> Self {
        self.sq()*(*self)
    }

    /// Compute the inverse of this <b>F</b><sub><i>p&#x2076;</i></sub> element
    /// (or 0, if this element is itself 0).
    #[inline]
    fn inv(&self) -> Self {
        // |v| = v*v.conj(1)*v.conj(2)
        // :: v^-1 = |v|^-1*v.conj(1)*v.conj(2)
        //
        // v.conj(1)*v.conj(2) = (v_0^2 - v_1*v_2*xi) + (v_2^2*xi - v_0*v_1) w + (v_1^2 - v_0*v_2) w^2
        // |v| = v_0*(v_0^2 - v_1*v_2*xi) + v_1*(v_1^2 - v_0*v_2)*xi + v_2*(v_2^2*xi - v_0*v_1)*xi

        // compute the components of the product of proper conjugates:
        let c0 = self.v0.sq() - self.v1*self.v2.mul_xi();  // v_0^2 - v_1*v_2*xi
        let c1 = self.v2.sq().mul_xi() - self.v0*self.v1;  // v_2^2*xi - v_0*v_1
        let c2 = self.v1.sq() - self.v0*self.v2;  // v_1^2 - v_0*v_2

        // compute the inverse of the Fp2-norm:
        let norm_inv = (self.v0*c0 + (self.v1*c2 + self.v2*c1).mul_xi()).inv();

        // complete the inversion in Fp6:
        norm_inv*Self::from(c0, c1, c2)
    }
}

impl<BN: BNParam, const LIMBS: usize> Clone for BNFp6<BN, LIMBS> {
    fn clone(&self) -> Self {
        Self {
            v0: self.v0.clone(), v1: self.v1.clone(), v2: self.v2.clone()
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> ConditionallySelectable for BNFp6<BN, LIMBS> {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        let v0 = BNFp2::conditional_select(&a.v0, &b.v0, choice);
        let v1 = BNFp2::conditional_select(&a.v1, &b.v1, choice);
        let v2 = BNFp2::conditional_select(&a.v2, &b.v2, choice);
        Self { v0, v1, v2 }
    }
}

impl<BN: BNParam, const LIMBS: usize> ConstantTimeEq for BNFp6<BN, LIMBS> {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.v0.ct_eq(&other.v0) & self.v1.ct_eq(&other.v1) & self.v2.ct_eq(&other.v2)
    }

    fn ct_ne(&self, other: &Self) -> Choice {
        self.v0.ct_ne(&other.v0) | self.v1.ct_ne(&other.v1) | self.v2.ct_ne(&other.v2)
    }
}

impl<BN: BNParam, const LIMBS: usize> Copy for BNFp6<BN, LIMBS> {}

impl<BN: BNParam, const LIMBS: usize> Debug for BNFp6<BN, LIMBS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self, f)
    }
}

impl<BN: BNParam, const LIMBS: usize> Display for BNFp6<BN, LIMBS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if bool::from(self.v1.is_zero() & self.v2.is_zero()) {
            // element in F_{p^2}:
            write!(f, "{}", self.v0)
        } else {
            write!(f, "({}) + ({})*w + ({})*w^2", self.v0, self.v1, self.v2)
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> Mul for BNFp6<BN, LIMBS> {
    type Output = Self;

    /// Compute a product in <b>F</b><sub><i>p&#x2076;</i></sub>.
    fn mul(self, rhs: Self) -> Self::Output {
        let mut val = self;
        val *= rhs;
        val
    }
}

impl<BN: BNParam, const LIMBS: usize> Mul<BNFp6<BN, LIMBS>> for Word {
    type Output = BNFp6<BN, LIMBS>;

    /// Compute the product of an integer left factor
    /// by a right factor from <b>F</b><sub><i>p&#x2076;</i></sub>.
    fn mul(self, rhs: BNFp6<BN, LIMBS>) -> Self::Output {
        Self::Output {
            v0: self*rhs.v0, v1: self*rhs.v1, v2: self*rhs.v2
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> Mul<BNFp6<BN, LIMBS>> for Uint<LIMBS> {
    type Output = BNFp6<BN, LIMBS>;

    /// Compute the product of an integer left factor
    /// by a right factor from <b>F</b><sub><i>p&#x2076;</i></sub>.
    fn mul(self, rhs: BNFp6<BN, LIMBS>) -> Self::Output {
        Self::Output {
            v0: self*rhs.v0, v1: self*rhs.v1, v2: self*rhs.v2
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> Mul<BNFp6<BN, LIMBS>> for BNFp<BN, LIMBS> {
    type Output = BNFp6<BN, LIMBS>;

    /// Compute the product of a left factor from <b>F</b><sub><i>p</i></sub>
    /// by a right factor from <b>F</b><sub><i>p&#x2076;</i></sub>.
    fn mul(self, rhs: BNFp6<BN, LIMBS>) -> Self::Output {
        Self::Output {
            v0: self*rhs.v0, v1: self*rhs.v1, v2: self*rhs.v2
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> Mul<BNFp6<BN, LIMBS>> for BNFp2<BN, LIMBS> {
    type Output = BNFp6<BN, LIMBS>;

    /// Compute the product of a left factor from <i><b>F</b><sub>p&sup2;</sub></i>
    /// by a right factor from <b>F</b><sub><i>p&#x2076;</i></sub>.
    fn mul(self, rhs: BNFp6<BN, LIMBS>) -> Self::Output {
        Self::Output {
            v0: self*rhs.v0, v1: self*rhs.v1, v2: self*rhs.v2
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> MulAssign for BNFp6<BN, LIMBS> {
    fn mul_assign(&mut self, rhs: Self) {
        //*
        self.kara3mul(rhs);
        // */
        /*
        self.toom3mul(rhs);  // slower than 3-way Karatsuba
        // */
    }
}

impl<BN: BNParam, const LIMBS: usize> Neg for BNFp6<BN, LIMBS> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::Output {
            v0: -self.v0, v1: -self.v1, v2: -self.v2
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> One for BNFp6<BN, LIMBS> {
    #[inline]
    fn one() -> Self {
        Self {
            v0: BNFp2::one(), v1: BNFp2::zero(), v2: BNFp2::zero()
        }
    }

    fn is_one(&self) -> Choice {
        self.v0.is_one() & self.v1.is_zero() & self.v2.is_zero()
    }
}

impl<BN: BNParam, const LIMBS: usize> PartialEq for BNFp6<BN, LIMBS> {
    fn eq(&self, other: &Self) -> bool { self.ct_eq(&other).into() }

    fn ne(&self, other: &Self) -> bool { self.ct_ne(&other).into() }
}

impl<BN: BNParam, const LIMBS: usize> Random for BNFp6<BN, LIMBS> {
    /// Pick a uniform element from <b>F</b><sub><i>p&#x2076;</i></sub> by rejection sampling.
    fn random<R: RngCore + ?Sized>(rng: &mut R) -> Self {
        Self {
            v0: BNFp2::random(rng), v1: BNFp2::random(rng), v2: BNFp2::random(rng),
        }
    }

    /// Try to pick a uniform element from <b>F</b><sub><i>p&#x2076;</i></sub> by rejection sampling.
    fn try_random<R: TryRngCore + ?Sized>(rng: &mut R) -> Result<Self, <R as TryRngCore>::Error> where R: TryRngCore {
        let try_v0 = match BNFp2::try_random(rng) {
            Ok(val) => Ok(val),
            Err(e) => Err(e),
        }?;

        let try_v1 = match BNFp2::try_random(rng) {
            Ok(val) => Ok(val),
            Err(e) => Err(e),
        }?;

        let try_v2 = match BNFp2::try_random(rng) {
            Ok(val) => Ok(val),
            Err(e) => Err(e),
        }?;

        Ok(Self { v0: try_v0, v1: try_v1, v2: try_v2 })
    }
}

impl<BN: BNParam, const LIMBS: usize> Sub for BNFp6<BN, LIMBS> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        let mut val = self;
        val -= rhs;
        val
    }
}

impl<BN: BNParam, const LIMBS: usize> SubAssign for BNFp6<BN, LIMBS> {
    fn sub_assign(&mut self, rhs: Self) {
        self.v0 -= rhs.v0;
        self.v1 -= rhs.v1;
        self.v2 -= rhs.v2;
    }
}

impl<BN: BNParam, const LIMBS: usize> Zero for BNFp6<BN, LIMBS> {
    fn zero() -> Self {
        Self {
            v0: BNFp2::zero(), v1: BNFp2::zero(), v2: BNFp2::zero()
        }
    }

    fn is_zero(&self) -> Choice {
        self.v0.is_zero() & self.v1.is_zero() & self.v2.is_zero()
    }

    fn set_zero(&mut self) {
        self.v0.set_zero();
        self.v1.set_zero();
        self.v2.set_zero();
    }
}


#[cfg(test)]
mod tests {
    use crate::bnparam::{BN062Param, BN126Param, BN190Param, BN254Param, BN318Param, BN382Param, BN446Param, BN510Param, BN574Param, BN638Param, BN702Param, BN766Param};
    use crypto_bigint::{NonZero, RandomMod};
    use crypto_bigint::rand_core::RngCore;
    use std::time::SystemTime;
    use super::*;

    const TESTS: usize = 100;

    /// General BNFp6 test template.
    #[allow(non_snake_case)]
    fn BNFp6_test<BN: BNParam, const LIMBS: usize>() {
        //let mut rng: SmallRng = SmallRng::from_seed([0; 32]);
        let mut rng = rand::rng();

        println!();
        println!("Performing {} BN{:03}Fp6 test(s)...", TESTS, 64*LIMBS - 2);
        let now = SystemTime::now();

        // neutral elements:
        //println!("0 = {}", BNFp6::zero());
        assert!(bool::from(BNFp6::<BN, LIMBS>::zero().is_zero()));
        //println!("1 = {}", BNFp6::one());
        assert!(bool::from(BNFp6::<BN, LIMBS>::one().is_one()));

        for _t in 0..TESTS {
            //println!("======== {}", _t);

            let e6: BNFp6<BN, LIMBS> = BNFp6::random(&mut rng);
            //println!("e6 = {}", e6);
            //println!("e6 + 0 = {}", e6 + BNFp6::zero());
            assert_eq!(e6 + BNFp6::zero(), e6);
            //println!("e6*1 = {}", e6*BNFp6::one());
            assert_eq!(e6*BNFp6::one(), e6);
            let e2: BNFp2<BN, LIMBS> = BNFp2::random(&mut rng);
            assert_eq!(BNFp6::from_base(e2), BNFp6::from(e2, BNFp2::zero(), BNFp2::zero()));

            // addition vs subtraction:
            //println!("-e6      = {}", -e6);
            //println!("e6 - e6  = {}", e6 - e6);
            //println!("e6+(-e6) = {}", e6 + (-e6));
            assert!(bool::from((e6 - e6).is_zero()));
            assert!(bool::from((e6 + (-e6)).is_zero()));

            // double and half:
            //println!("2*e6   = {}", e6.double());
            //println!("e6/2   = {}", e6.half());
            assert_eq!(e6.double().half(), e6);
            assert_eq!(e6.half().double(), e6);
            //assert_eq!(e6.double()*e6.half(), e6.sq());

            // square and cube:
            //println!("e6^2  == {}", e6.sq());
            //println!("e6*e6 == {}", e6*e6);
            //println!("e6^2 = e6*e6 ? {}", e6.sq() == e6*e6);
            assert_eq!(e6.sq(), e6*e6);
            //println!("e6^3       = {}", e6.cb());
            //println!("e6^3 = e6*e6*e6 ? {}", e6.cb() == e6*e6*e6);
            assert_eq!(e6.cb(), e6*e6*e6);

            // norm:
            //println!("|e6| = {}", e6.norm());
            //println!("|e6| ? {}", e6*e6.conj(1)*e6.conj(2));
            let e6_conj_prod = e6*e6.conj(1)*e6.conj(2);
            //println!("|e6| = e6*e6.conj(1)*e6.conj(2) ? {}", bool::from(e6_conj_prod.v0.ct_eq(&e6.norm()) & e6_conj_prod.v1.is_zero() & e6_conj_prod.v2.is_zero()));
            assert!(bool::from(e6_conj_prod.v0.ct_eq(&e6.norm()) & e6_conj_prod.v1.is_zero() & e6_conj_prod.v2.is_zero()));

            // field inversion:
            //println!("e6^-1 = {};", e6.inv());
            //println!("e6*e6^-1 = {}", e6*e6.inv());
            assert!(bool::from((e6*e6.inv()).is_one()));

            // subring multiplication (Word*BNFp6, Uint*BNFp6, BNFp*BNFp6, BNFp2*BNFp6, BNFp2*BNFp6):
            let p: Uint<LIMBS> = Uint::from_words(BN::MODULUS.try_into().unwrap());
            let k6: Word = rng.next_u64() & 0xF;
            //println!("k6*e6 = {}", k6*e6);
            //println!("k6*e6 ? {}", BNFp::from_word(k6)*e6);
            assert_eq!(k6*e6, BNFp::from_word(k6)*e6);
            let u6 = Uint::random_mod(&mut rng, &NonZero::new(p).unwrap());
            //println!("u6 = {}", u6.to_string_radix_vartime(20));
            //println!("u6*e6 = {}", u6*e6);
            assert_eq!(u6*e6, BNFp::from_uint(u6)*e6);
            assert_eq!(u6*e6, BNFp2::from_base(BNFp::from_uint(u6))*e6);

            // norm homomorphism:
            let e7 = BNFp6::random(&mut rng);
            //println!("e7 = {}", e7);
            //println!("|e7| = {}", e7.norm());
            //println!("|e6*e7| = |e6|*|e7| ? {}", (e6*e7).norm() == e6.norm()*e7.norm());
            assert_eq!((e6*e7).norm(), e6.norm()*e7.norm());

            let f6 = BNFp6::random(&mut rng);
            //println!("f6     = {}", f6);
            let g6 = BNFp6::random(&mut rng);
            //println!("g6     = {}", g6);

            // commutativity of addition and multiplication:
            //println!("e6 + f6 = {}", e6 + f6);
            //println!("f6 + e6 = {}", f6 + e6);
            assert_eq!(e6 + f6, f6 + e6);
            assert_eq!(e6*f6, f6*e6);

            // associativity:
            //println!("(e6 + f6) + g6 = {}", (e6 + f6) + g6);
            //println!("e6 + (f6 + g6) = {}", e6 + (f6 + g6));
            assert_eq!((e6 + f6) + g6, e6 + (f6 + g6));
            //println!("(e6*f6)*g6 = {}", (e6*f6)*g6);
            //println!("e6*(f6*g6) = {}", e6*(f6*g6));
            assert_eq!((e6*f6)*g6, e6*(f6*g6));
        }
        match now.elapsed() {
            Ok(elapsed) => {
                println!("Elapsed time: {} ms.", (elapsed.as_micros() as f64)/1000.0);
            }
            Err(e) => {
                println!("Error: {e:?}");
            }
        }
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN062Fp6_test() {
        const LIMBS: usize = BN062Param::LIMBS;
        BNFp6_test::<BN062Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN126Fp6_test() {
        const LIMBS: usize = BN126Param::LIMBS;
        BNFp6_test::<BN126Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN190Fp6_test() {
        const LIMBS: usize = BN190Param::LIMBS;
        BNFp6_test::<BN190Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN254Fp6_test() {
        const LIMBS: usize = BN254Param::LIMBS;
        BNFp6_test::<BN254Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN318Fp6_test() {
        const LIMBS: usize = BN318Param::LIMBS;
        BNFp6_test::<BN318Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN382Fp6_test() {
        const LIMBS: usize = BN382Param::LIMBS;
        BNFp6_test::<BN382Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN446Fp6_test() {
        const LIMBS: usize = BN446Param::LIMBS;
        BNFp6_test::<BN446Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN510Fp6_test() {
        const LIMBS: usize = BN510Param::LIMBS;
        BNFp6_test::<BN510Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN574Fp6_test() {
        const LIMBS: usize = BN574Param::LIMBS;
        BNFp6_test::<BN574Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN638Fp6_test() {
        const LIMBS: usize = BN638Param::LIMBS;
        BNFp6_test::<BN638Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN702Fp6_test() {
        const LIMBS: usize = BN702Param::LIMBS;
        BNFp6_test::<BN702Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN766Fp6_test() {
        const LIMBS: usize = BN766Param::LIMBS;
        BNFp6_test::<BN766Param, LIMBS>();
    }

}
