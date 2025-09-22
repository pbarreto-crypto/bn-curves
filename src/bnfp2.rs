#[cfg(not(any(target_pointer_width = "64")))]
compile_error!("this crate requires 64-bit limbs");

use crate::bnfp::BNFp;
use crate::bnparam::BNParam;
use crate::traits::{BNField, One};
use crypto_bigint::{Random, Uint, Word, Zero};
use crypto_bigint::rand_core::{RngCore, TryRngCore};
use crypto_bigint::subtle::{Choice, ConditionallySelectable, ConstantTimeEq};
use std::fmt::{Debug, Display, Formatter};
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

/// The <b>F</b><sub><i>p&sup2;</i></sub> &simeq; <b>F</b><sub><i>p</i></sub>&lbrack;<i>i</i>&rbrack;/&lt;<i>i&sup2;</i> + 1&gt;
/// extension field.  NB: <i>i&sup2;</i> = -1.
pub struct BNFp2<BN: BNParam, const LIMBS: usize> {
    pub(crate) re: BNFp<BN, LIMBS>,
    pub(crate) im: BNFp<BN, LIMBS>,
}

/*
// the Litany of All Saints:
pub type BN062Fp2 = BNFp2<BN062Param, 1>;
pub type BN126Fp2 = BNFp2<BN126Param, 2>;
pub type BN190Fp2 = BNFp2<BN190Param, 3>;
pub type BN254Fp2 = BNFp2<BN254Param, 4>;
pub type BN318Fp2 = BNFp2<BN318Param, 5>;
pub type BN382Fp2 = BNFp2<BN382Param, 6>;
pub type BN446Fp2 = BNFp2<BN446Param, 7>;
pub type BN510Fp2 = BNFp2<BN510Param, 8>;
pub type BN574Fp2 = BNFp2<BN574Param, 9>;
pub type BN638Fp2 = BNFp2<BN638Param, 10>;
pub type BN702Fp2 = BNFp2<BN702Param, 11>;
pub type BN766Fp2 = BNFp2<BN766Param, 12>;
// */


impl<BN: BNParam, const LIMBS: usize> BNFp2<BN, LIMBS> {
    /// Convert an <b>F</b><sub><i>p</i></sub> element to its <b>F</b><sub><i>p&sup2;</i></sub> counterpart.
    #[inline]
    pub(crate) fn from_base(re: BNFp<BN, LIMBS>) -> Self {
        Self {
            re,
            im: BNFp::zero(),
        }
    }

    /// Convert a word-sized integer <i>w</i> to its <b>F</b><sub><i>p&sup2;</i></sub> counterpart.
    #[inline]
    pub fn from_word(w: Word) -> Self {
        Self {
            re: BNFp::from_word(w),
            im: BNFp::zero(),
        }
    }

    /// Assemble an <b>F</b><sub><i>p&sup2;</i></sub> element
    /// from its <b>F</b><sub><i>p</i></sub> components.
    #[inline]
    pub(crate) fn from(re: BNFp<BN, LIMBS>, im: BNFp<BN, LIMBS>) -> Self {
        Self {
            re,
            im,
        }
    }

    /// Hash input data into a field element with SHAKE-128.
    #[inline]
    pub fn shake128(data: &[u8]) -> Self {
        let (re, im) = BNFp::shake128pair(data);
        Self {
            re,
            im,
        }
    }

    /// Hash input data into a field element with SHAKE-256.
    #[inline]
    pub fn shake256(data: &[u8]) -> Self {
        let (re, im) = BNFp::shake256pair(data);
        Self {
            re,
            im,
        }
    }

    /// Create an instance of the element <i>i &in; <b>F</b><sub>p&sup2;</sub></i>.
    #[inline]
    pub(crate) fn i() -> Self {
        Self {
            re: BNFp::zero(),
            im: BNFp::one(),
        }
    }

    #[inline]
    pub(crate) fn is_odd(&self) -> Choice {
        self.re.is_odd()
    }

    /// Complex conjugate of this <b>F</b><sub><i>p&sup2;</i></sub> element,
    /// namely, if this element is <i>u + vi</i>, return <i>u - vi</i>.
    #[inline]
    pub(crate) fn conj(&self) -> Self {
        Self { re: self.re, im: -self.im, }
    }

    /// <b>F</b><sub><i>p</i></sub>-norm of this <b>F</b><sub><i>p&sup2;</i></sub> element,
    /// namely, if this element is <i>u + vi</i>, return <i>u&sup2; + v&sup2;</i>.
    #[inline]
    pub(crate) fn norm(&self) -> BNFp<BN, LIMBS> {
        self.re.sq() + self.im.sq()
    }

    /// Compute the product of a field element <i>x + yi</i> by <i>i</i>.
    #[inline]
    pub(crate) fn mul_i(&self) -> Self {
        // (x + yi)i = (-y + xi)
        Self { re: -self.im, im: self.re, }
    }

    /// Compute the product of a field element <i>x + yi</i> by <i>&xi; := 1 + i</i>.
    #[inline]
    pub(crate) fn mul_xi(&self) -> Self {
        // (x + yi)*(1 + i) = (x - y) + (x + y)i
        Self {
            re: self.re - self.im,
            im: self.re + self.im,
        }
    }

    /// Compute the quotient of a field element <i>x + yi</i> by <i>&xi; := 1 + i</i>.
    #[inline]
    pub(crate) fn div_xi(&self) -> Self {
        // (x + yi)/(1 + i) = (x + yi)(1 - i)/((1 + i)*(1 - i)) = (x + yi)(1 - i)/2
        // = (x + yi)/2 - (xi - y)/2 = (x + y)/2 + (y - x)i/2
        Self {
            re: (self.re + self.im).half(),
            im: (self.im - self.re).half(),
        }
    }

    /// Compute the products of a field element <i>x + yi</i> by both <i>(1 &pm; i)/2</i>.
    #[inline]
    pub(crate) fn jmul(&self) -> (Self, Self) {
        // (x + yi)*(1 + i)/2 = (x - y)/2 + i(x + y)/2 = d + si
        // (x + yi)*(1 - i)/2 = (x + y)/2 - i(x - y)/2 = s - di
        let s = (self.re + self.im).half();
        let d = (self.re - self.im).half();
        (Self { re: d, im: s }, Self { re: s, im: -d })
    }

    /// Compute i*(self - other).
    pub(crate) fn isub(&self, other: BNFp2<BN, LIMBS>) -> Self {
        Self {
            re: other.im - self.im,
            im: self.re - other.re
        }
    }

    /// Compute the square root of this element <i>u + vi &in; <b>F</b><sub>p&sup2;</sub></i> if such a root exists.
    /// If a root does exist with a nonzero "real" part,
    /// pick the root where that part has the specified least-significant bit (`lsb`).
    /// If a root does exist with a zero "real" part but a nonzero "imaginary" part,
    /// pick the root where this part has the specified least-significant bit (`lsb`).
    /// If `self` is zero or if a root does not exist, return zero.
    ///
    /// Reference:
    ///
    /// *; M. Scott, ``Implementing cryptographic pairings'' (invited talk),
    /// International Conference on Pairing-Based Cryptography -- Pairing 2007,
    /// Lecture Notes in Computer Science, vol. 4575, pp. 177--196, Springer, 2007.
    /// https://link.springer.com/book/10.1007/978-3-540-73489-5
    #[inline]
    pub(crate) fn sqrt(&self, lsb: Choice) -> Self {
        let n = self.norm();  // n = (u^2 + v^2) mod p
        let m = n.sqrt();
        let ex = m.sq().ct_eq(&n);  // root existence flag
        let z: BNFp<BN, LIMBS> = BNFp::conditional_select(&(self.re + m).half(), &self.re, self.im.is_zero());  // (u + m)/2 mod p, or just u when v = 0
        let t = z.inv_sqrt();  // 1/sqrt(z) = z^((p + 1)/4 - 1) mod p
        let r = z*t;  // sqrt(z) = z*t mod p
        let s = self.im*t.half(); // v*t/2 mod p = ±v*(r*t)*t/2 mod p (NB: r*t is just a ± sign)
        let ch = r.sq().ct_eq(&z);  // sign flip and swap flag
        assert!(bool::from((r*t).is_one().ct_eq(&ch) | self.im.is_zero()));  // r*t == 1 <=> ch = true, except if self in Fp
        let mut mu = BNFp::conditional_select(&s, &r, ch);
        let mut nu = BNFp::conditional_select(&(-r), &s, ch);
        let mu0 = mu.is_zero();
        let parity = (!mu0 & (mu.is_odd() ^ lsb)) | (mu0 & !nu.is_zero() & (nu.is_odd() ^ lsb));
        mu = BNFp::conditional_select(&mu, &(-mu), parity);
        nu = BNFp::conditional_select(&nu, &(-nu), parity);
        assert!(bool::from(!ex | !((!mu0 & (mu.is_odd() ^ lsb)) | (mu0 & !nu.is_zero() & (nu.is_odd() ^ lsb)))));
        BNFp2::conditional_select(&BNFp2::zero(), &BNFp2::from(mu, nu), ex)
    }

    /// Compute the generalized Legendre symbol <i>(u/<b>F</b><sub>p&sup2;</sub>)</i>:<br>
    /// &nbsp;   +1      if <i>u</i> is a nonzero quadratic residue in <b>F</b><sub><i>p&sup2;</i></sub>,<br>
    /// &nbsp;   &nbsp;0 if <i>u</i> = <i>0</i><br>
    /// &nbsp;   -1      if <i>u</i> is a nonzero quadratic non-residue in <b>F</b><sub><i>p&sup2;</i></sub>.
    #[inline]
    pub(crate) fn legendre(&self) -> isize {
        self.norm().legendre()
    }
}

impl<BN: BNParam, const LIMBS: usize> Add for BNFp2<BN, LIMBS> {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        Self {
            re: self.re + rhs.re,
            im: self.im + rhs.im,
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> AddAssign for BNFp2<BN, LIMBS> {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.re += rhs.re;
        self.im += rhs.im;
    }
}

impl<BN: BNParam, const LIMBS: usize> BNField for BNFp2<BN, LIMBS> {
    /// Convert `self` to byte array representation.
    #[inline]
    fn to_bytes(&self) -> Vec<u8> {
        let mut rev = self.re.to_bytes();
        let mut imv = self.im.to_bytes();
        rev.append(&mut imv);
        rev
    }

    /// Compute the value of twice this element.
    #[inline]
    fn double(&self) -> Self {
        Self {
            re: self.re.double(),
            im: self.im.double(),
        }
    }

    /// Compute the value of half this element.
    #[inline]
    fn half(&self) -> Self {
        Self {
            re: self.re.half(),
            im: self.im.half(),
        }
    }

    /// Compute the square of this <b>F</b><sub><i>p&sup2;</i></sub> element.
    #[inline]
    fn sq(&self) -> Self {
        // (u + vi)^2 = u^2 - v^2 + 2uvi = (u + v)*(u - v) + 2uvi
        let repim = self.re + self.im;
        let remim = self.re - self.im;
        let retim = self.re*self.im;
        Self {
            re: repim*remim,
            im: retim + retim
        }
    }

    /// Compute the cube of this <b>F</b><sub><i>p&sup2;</i></sub> element.
    #[inline]
    fn cb(&self) -> Self {
        // (u + vi)^3 = u*(u^2 - 3*v^2) + v*(3*u^2 - v^2) i
        let re2 = self.re.sq();
        let im2 = self.im.sq();
        let d = re2 - im2;
        Self {
            re: self.re*(d - im2 - im2),
            im: self.im*(re2 + re2 + d)
        }
    }

    /// Compute the inverse of `self` in <b>F</b><sub><i>p&sup2;</i></sub>
    /// (or 0, if `self` is itself 0).
    #[inline]
    fn inv(&self) -> Self {
        // (u + vi)^-1 = (u^2 + v^2)^-1*(u - vi) = norm^-1*conj.
        self.norm().inv()*self.conj()
    }
}

impl<BN: BNParam, const LIMBS: usize> Clone for BNFp2<BN, LIMBS> {
    #[inline]
    fn clone(&self) -> Self {
        Self { re: self.re.clone(), im: self.im.clone() }
    }
}

impl<BN: BNParam, const LIMBS: usize> ConditionallySelectable for BNFp2<BN, LIMBS> {
    #[inline]
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self {
            re: BNFp::conditional_select(&a.re, &b.re, choice),
            im: BNFp::conditional_select(&a.im, &b.im, choice),
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> ConstantTimeEq for BNFp2<BN, LIMBS> {
    #[inline]
    fn ct_eq(&self, other: &Self) -> Choice {
        self.re.ct_eq(&other.re) & self.im.ct_eq(&other.im)
    }

    #[inline]
    fn ct_ne(&self, other: &Self) -> Choice {
        self.re.ct_ne(&other.re) | self.im.ct_ne(&other.im)
    }
}

impl<BN: BNParam, const LIMBS: usize> Copy for BNFp2<BN, LIMBS> {}

impl<BN: BNParam, const LIMBS: usize> Debug for BNFp2<BN, LIMBS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self, f)
    }
}

impl<BN: BNParam, const LIMBS: usize> Display for BNFp2<BN, LIMBS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if bool::from(self.im.is_zero()) {
            write!(f, "{}",
                self.re.to_string()
            )
        } else if bool::from(self.re.is_zero()) {
            if bool::from(self.im.is_one()) {
                write!(f, "i")
            } else if bool::from((-self.im).is_one()) {
                write!(f, "-i")
            } else {
                write!(f, "{}*i",
                    self.im.to_string()
                )
            }
        } else {
            if bool::from(self.im.is_one()) {
                write!(f, "{} + i", self.re.to_string())
            } else if bool::from((-self.im).is_one()) {
                write!(f, "{} - i", self.re.to_string())
            } else {
                let strim = self.im.to_string();
                if strim.chars().next() != Some('-') {
                    write!(f, "{} + {}*i",
                        self.re.to_string(),
                        strim
                    )
                } else {
                    write!(f, "{} - {}*i",
                        self.re.to_string(),
                        &strim[1..].to_string()
                    )
                }
            }
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> Mul for BNFp2<BN, LIMBS> {
    type Output = Self;

    /// Compute a product in <b>F</b><sub><i>p&sup2;</i></sub>.
    #[inline]
    fn mul(self, rhs: Self) -> Self::Output {
        let mut val = self;
        val *= rhs;
        val
    }
}

impl<BN: BNParam, const LIMBS: usize> Mul<BNFp2<BN, LIMBS>> for Word {
    type Output = BNFp2<BN, LIMBS>;

    /// Compute the product of an integer left factor
    /// by a right factor from <b>F</b><sub><i>p&sup2;</i></sub>.
    #[inline]
    fn mul(self, rhs: BNFp2<BN, LIMBS>) -> Self::Output {
        Self::Output {
            re: self*rhs.re,
            im: self*rhs.im
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> Mul<BNFp2<BN, LIMBS>> for Uint<LIMBS> {
    type Output = BNFp2<BN, LIMBS>;

    /// Compute the product of an integer left factor
    /// by a right factor from <b>F</b><sub><i>p&sup2;</i></sub>.
    #[inline]
    fn mul(self, rhs: BNFp2<BN, LIMBS>) -> Self::Output {
        Self::Output {
            re: self*rhs.re,
            im: self*rhs.im
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> Mul<BNFp2<BN, LIMBS>> for BNFp<BN, LIMBS> {
    type Output = BNFp2<BN, LIMBS>;

    /// Compute the product of a left factor from <b>F</b><sub><i>p</i></sub>
    /// by a right factor from <b>F</b><sub><i>p&sup2;</i></sub>.
    #[inline]
    fn mul(self, rhs: BNFp2<BN, LIMBS>) -> Self::Output {
        Self::Output {
            re: self*rhs.re,
            im: self*rhs.im
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> MulAssign for BNFp2<BN, LIMBS> {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        // (a + bi)*(u + vi) = au - bv + (av + bu)i
        // (a + b)*(u + v) - au - bv = av + bu
        let re2 = self.re*rhs.re;
        let im2 = self.im*rhs.im;
        let mix = (self.re + self.im)*(rhs.re + rhs.im);
        self.re = re2 - im2;
        self.im = mix - re2 - im2;
    }
}

impl<BN: BNParam, const LIMBS: usize> Neg for BNFp2<BN, LIMBS> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self::Output {
        Self::Output {
            re: -self.re,
            im: -self.im,
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> One for BNFp2<BN, LIMBS> {
    #[inline]
    fn one() -> Self {
        Self {
            re: BNFp::one(),
            im: BNFp::zero(),
        }
    }

    #[inline]
    fn is_one(&self) -> Choice {
        self.re.is_one() & self.im.is_zero()
    }
}

impl<BN: BNParam, const LIMBS: usize> PartialEq for BNFp2<BN, LIMBS> {
    #[inline]
    fn eq(&self, other: &Self) -> bool { self.ct_eq(&other).into() }

    #[inline]
    fn ne(&self, other: &Self) -> bool { self.ct_ne(&other).into() }
}

impl<BN: BNParam, const LIMBS: usize> Random for BNFp2<BN, LIMBS> {
    /// Pick a uniform element from <b>F</b><sub><i>p&sup2;</i></sub> by rejection sampling.
    #[inline]
    fn random<R: RngCore + ?Sized>(rng: &mut R) -> Self {
        Self {
            re: BNFp::random(rng),
            im: BNFp::random(rng),
        }
    }

    /// Try to pick a uniform element from <b>F</b><sub><i>p&sup2;</i></sub> by rejection sampling.
    fn try_random<R: TryRngCore + ?Sized>(rng: &mut R) -> Result<Self, <R as TryRngCore>::Error> where R: TryRngCore {
        let try_re = match BNFp::try_random(rng) {
            Ok(val) => Ok(val),
            Err(e) => Err(e),
        }?;

        let try_im = match BNFp::try_random(rng) {
            Ok(val) => Ok(val),
            Err(e) => Err(e),
        }?;

        Ok(Self { re: try_re, im: try_im })
    }
}

impl<BN: BNParam, const LIMBS: usize> Sub for BNFp2<BN, LIMBS> {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        Self {
            re: self.re - rhs.re,
            im: self.im - rhs.im,
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> SubAssign for BNFp2<BN, LIMBS> {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        self.re -= rhs.re;
        self.im -= rhs.im;
    }
}

impl<BN: BNParam, const LIMBS: usize> Zero for BNFp2<BN, LIMBS> {
    #[inline]
    fn zero() -> Self {
        Self {
            re: BNFp::zero(),
            im: BNFp::zero(),
        }
    }

    #[inline]
    fn is_zero(&self) -> Choice {
        self.re.is_zero() & self.im.is_zero()
    }

    #[inline]
    fn set_zero(&mut self) {
        self.re.set_zero();
        self.im.set_zero()
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

    /// General BNFp2 test template.
    #[allow(non_snake_case)]
    fn BNFp2_test<BN: BNParam, const LIMBS: usize>() {
        let mut rng = rand::rng();

        println!();
        println!("Performing {} BN{:03}Fp2 test(s)...", TESTS, 64*LIMBS - 2);
        let now = SystemTime::now();

        // neutral elements:
        //println!("0 = {}", BNFp2::zero());
        assert!(bool::from(BNFp2::<BN, LIMBS>::zero().is_zero()));
        //println!("1 = {}", BNFp2::one());
        assert!(bool::from(BNFp2::<BN, LIMBS>::one().is_one()));

        for _t in 0..TESTS {
            //println!("======== {}", _t);

            let e2: BNFp2<BN, LIMBS> = BNFp2::random(&mut rng);
            //println!("e2 = {}", e2);
            //println!("e2 + 0 = {}", e2 + BNFp2::zero());
            assert_eq!(e2 + BNFp2::zero(), e2);
            //println!("e2*1 = {}", e2*BNFp2::one());
            assert_eq!(e2*BNFp2::one(), e2);

            // addition vs subtraction:
            //println!("-e1      = {}", -e1);
            //println!("e1 - e1  = {}", e1 - e1);
            //println!("e1+(-e1) = {}", e1 + (-e1));
            assert!(bool::from((e2 - e2).is_zero()));
            assert!(bool::from((e2 + (-e2)).is_zero()));

            // double and half:
            //println!("2*e1   = {}", e1.double());
            //println!("e1/2   = {}", e1.half());
            assert_eq!(e2.double().half(), e2);
            assert_eq!(e2.half().double(), e2);
            assert_eq!(e2.double()*e2.half(), e2.sq());

            // square and cube:
            //println!("e2^2       = {}", e2.sq());
            //println!("e2^2 = e2*e2 ? {}", e2.sq() == e2*e2);
            assert_eq!(e2.sq(), e2*e2);
            //println!("e2^3       = {}", e2.cb());
            //println!("e2^3 = e2*e2*e2 ? {}", e2.cb() == e2*e2*e2);
            assert_eq!(e2.cb(), e2*e2*e2);

            // norm:
            //println!("|e2| = {}", e2.norm());
            //println!("|e2| = e2*e2.conj() ? {}", bool::from((e2*e2.conj()).re.ct_eq(&e2.norm()) & (e2*e2.conj()).im.is_zero()));
            assert!(bool::from((e2*e2.conj()).re.ct_eq(&e2.norm()) & (e2*e2.conj()).im.is_zero()));

            // field inversion:
            //println!("e2^-1 = {}", e2.inv());
            //println!("e2*e2^-1 = {}", e2*e2.inv());
            assert!(bool::from((e2*e2.inv()).is_one()));

            // square roots:
            let sr = e2.sqrt(e2.re.is_odd());
            if bool::from(!sr.is_zero() | e2.is_zero()) {
                //println!("sqrt(e2) = {}", sr);
                //println!("sqrt(e2)^2 = e2 ? {}", bool::from(sr.sq().ct_eq(&e2)));
                assert_eq!(sr.sq(), e2);
            } else {
                //println!("no sqrt");
                assert!(e2.legendre() < 0);
            }
            let e1: BNFp2<BN, LIMBS> = BNFp2::from_base(BNFp::random(&mut rng));
            let sr = e1.sqrt(BNFp::<BN, LIMBS>::random(&mut rng).is_odd());
            assert!(e1.legendre() >= 0);
            assert!(bool::from(!sr.is_zero() | e1.is_zero()));  // square root of Fp value always exists in Fp2
            assert_eq!(sr.sq(), e1);

            // subgroup multiplication (Word*BNFp2, Uint*BNFp2, and BNFp*BNFp2):
            let p: Uint<LIMBS> = Uint::from_words(BN::MODULUS.try_into().unwrap());
            let k2: Word = rng.next_u64() & 0xF;
            //println!("k2*e2 = {}", k2*e2);
            //println!("k2*e2 ? {}", BNFp::from_word(k2)*e2);
            assert_eq!(k2*e2, BNFp::from_word(k2)*e2);
            let u2 = Uint::random_mod(&mut rng, &NonZero::new(p).unwrap());
            //println!("u2 = {}", u2.to_string_radix_vartime(20));
            //println!("u2*e2 = {}", u2*e2);
            assert_eq!(u2*e2, BNFp::from_uint(u2)*e2);
            assert_eq!(u2*e2, BNFp2::from(BNFp::from_uint(u2), BNFp::zero())*e2);

            let e3 = BNFp2::random(&mut rng);
            //println!("e3 = {}", e3);

            // norm homomorphism:
            //println!("|e3| = {}", e3.norm());
            //println!("|e2*e3| = |e2|*|e3| ? {}", (e2*e3).norm() == e2.norm()*e3.norm());
            assert_eq!((e2*e3).norm(), e2.norm()*e3.norm());

            let f2 = BNFp2::random(&mut rng);
            //println!("f2     = {}", f2);
            let g2 = BNFp2::random(&mut rng);
            //println!("g2     = {}", g2);

            // commutativity of addition and multiplication:
            //println!("e2 + f2 = {}", e2 + f2);
            //println!("f2 + e2 = {}", f2 + e2);
            assert_eq!(e2 + f2, f2 + e2);
            assert_eq!(e2*f2, f2*e2);

            // associativity:
            //println!("(e2 + f2) + g2 = {}", (e2 + f2) + g2);
            //println!("e2 + (f2 + g2) = {}", e2 + (f2 + g2));
            assert_eq!((e2 + f2) + g2, e2 + (f2 + g2));
            //println!("(e2*f2)*g2 = {}", (e2*f2)*g2);
            //println!("e2*(f2*g2) = {}", e2*(f2*g2));
            assert_eq!((e2*f2)*g2, e2*(f2*g2));
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
    fn BN062Fp2_test() {
        const LIMBS: usize = BN062Param::LIMBS;
        BNFp2_test::<BN062Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN126Fp2_test() {
        const LIMBS: usize = BN126Param::LIMBS;
        BNFp2_test::<BN126Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN190Fp2_test() {
        const LIMBS: usize = BN190Param::LIMBS;
        BNFp2_test::<BN190Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN254Fp2_test() {
        const LIMBS: usize = BN254Param::LIMBS;
        BNFp2_test::<BN254Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN318Fp2_test() {
        const LIMBS: usize = BN318Param::LIMBS;
        BNFp2_test::<BN318Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN382Fp2_test() {
        const LIMBS: usize = BN382Param::LIMBS;
        BNFp2_test::<BN382Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN446Fp2_test() {
        const LIMBS: usize = BN446Param::LIMBS;
        BNFp2_test::<BN446Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN510Fp2_test() {
        const LIMBS: usize = BN510Param::LIMBS;
        BNFp2_test::<BN510Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN574Fp2_test() {
        const LIMBS: usize = BN574Param::LIMBS;
        BNFp2_test::<BN574Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN638Fp2_test() {
        const LIMBS: usize = BN638Param::LIMBS;
        BNFp2_test::<BN638Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN702Fp2_test() {
        const LIMBS: usize = BN702Param::LIMBS;
        BNFp2_test::<BN702Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN766Fp2_test() {
        const LIMBS: usize = BN766Param::LIMBS;
        BNFp2_test::<BN766Param, LIMBS>();
    }

}
