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

/// The <b>F</b><sub><i>p&#x2074;</i></sub> = <b>F</b><sub><i>p&sup2;</i></sub>&lbrack;<i>w</i>&rbrack;/&lt;<i>w&sup2; - &xi;</i>&gt;
/// extension field, with <i>&xi;</i> = <i>1 + i</i>.
/// NB: <i>w&sup2;</i> = <i>&xi;</i>.
pub struct BNFp4<BN: BNParam, const LIMBS: usize> {
    pub(crate) re: BNFp2<BN, LIMBS>,
    pub(crate) im: BNFp2<BN, LIMBS>,
}

/*
// the Litany of All Saints:
pub type BN062Fp4 = BNFp4<BN062Param, 1>;
pub type BN126Fp4 = BNFp4<BN126Param, 2>;
pub type BN190Fp4 = BNFp4<BN190Param, 3>;
pub type BN254Fp4 = BNFp4<BN254Param, 4>;
pub type BN318Fp4 = BNFp4<BN318Param, 5>;
pub type BN382Fp4 = BNFp4<BN382Param, 6>;
pub type BN446Fp4 = BNFp4<BN446Param, 7>;
pub type BN510Fp4 = BNFp4<BN510Param, 8>;
pub type BN574Fp4 = BNFp4<BN574Param, 9>;
pub type BN638Fp4 = BNFp4<BN638Param, 10>;
pub type BN702Fp4 = BNFp4<BN702Param, 11>;
pub type BN766Fp4 = BNFp4<BN766Param, 12>;
// */


impl<BN: BNParam, const LIMBS: usize> BNFp4<BN, LIMBS> {
    /// Convert an <b>F</b><sub><i>p&sup2;</i></sub> element to its <b>F</b><sub><i>p&#x2074;</i></sub> counterpart.
    #[inline]
    pub(crate) fn from_base(re: BNFp2<BN, LIMBS>) -> Self {
        Self {
            re,
            im: BNFp2::zero(),
        }
    }

    /// Assemble an <b>F</b><sub><i>p&#x2074;</i></sub> element
    /// from its <b>F</b><sub><i>p&sup2;</i></sub> components.
    #[inline]
    pub(crate) fn from(re: BNFp2<BN, LIMBS>, im: BNFp2<BN, LIMBS>) -> Self {
        Self {
            re,
            im,
        }
    }

    /// Complex conjugate of this <b>F</b><sub><i>p&#x2074;</i></sub> element,
    /// namely, if this element is <i>u + vw</i>, return <i>u - vw</i>.
    #[inline]
    pub(crate) fn conj(&self) -> Self {
        Self {
            re: self.re, im: -self.im,
        }
    }

    /// Compute the product of this element <i>u + vw &in; <b>F</b><sub>p&#x2074;</sub> = <b>F</b><sub>p&sup2;</sub>&lbrack;w&rbrack;/&lt;w&sup2; - &xi;&gt;</i>
    /// by <i>w</i>.
    #[inline]
    pub(crate) fn mul_tau(&self) -> Self {
        // (u, v)*w = (u + v*w)*w = v*xi + u*w = (v*xi, u)
        Self {
            re: self.im.mul_xi(),
            im: self.re,
        }
    }

    /// Compute <i>`u`&times;`self` - `v`&times;conj(`self`)</i>.
    #[inline]
    fn ch(&self, u: &BNFp4<BN, LIMBS>, v: &BNFp4<BN, LIMBS>) -> BNFp4<BN, LIMBS> {
        // (x.re + x.im*w)*(s.re + s.im*w) - (y.re + y.im*w)*(s.re - s.im*w) =
        // (x.re - y.re)*s.re + (x.im + y.im)*s.im*xi + ((x.im - y.im)*s.re + (x.re + y.re)*s.im)*w
        let re = (u.re - v.re)*self.re + (u.im + v.im)*self.im.mul_xi();
        let im = (u.im - v.im)*self.re + (u.re + v.re)*self.im;
        Self {
            re,
            im,
        }
    }

    /// Interpreting this element as the <b>F</b><sub><i>p&#x2074;</i></sub>-trace of some
    /// <i><b>F</b><sub>p&sup1;&#xFEFF;&sup2;</sub></i> value, namely <i>`self` = tr(g)</i>,
    /// implicitly exponentiate the trace, yielding <i>tr(g&#x1D50;)</i>.
    ///
    /// This is useful for further processing compressed pairing values,
    /// i.e. after compressing <i>e(P, Q)</i> to <i>tr(e(P, Q))</i>.
    #[inline]
    pub(crate) fn trexp(&self, m: &Uint<LIMBS>) -> BNFp4<BN, LIMBS> {
        let w = m.as_words();
        // S_w(c) = c_w
        let r = 64*LIMBS;  // this ensures 2^r > m
        let mut k= Uint::ZERO;
        // [c_{0}, c_{1}, c_{2}]:
        let mut c_k0: BNFp4<BN, LIMBS> = 3*BNFp4::one();
        let mut c_k1: BNFp4<BN, LIMBS> = self.clone();
        let mut c_k2: BNFp4<BN, LIMBS> = self.sq() - self.conj().double();  // c^2 - 2*conj(c)
        let c_conj = self.conj();
        for j in (1..r).rev() {
            let mj = (w[j >> 6] >> (j & 63)) & 1;
            k = (k << 1) + Uint::from_word(mj);
            /*
                if mj == 1 {
                  compute [c_{2k+2}, c_{2k+3}, c_{2k+4}] from [c_{k}, c_{k+1}, c_{k+2}]:
                      c_{2m} = c_m^2 - 2*conj(c_m) =>
                          c_{2k+2} = c_{k+1}^2 - 2*conj(c_{k+1}),
                          c_{2k+4} = c_{k+2}^2 - 2*conj(c_{k+2}),
                      c_{2m+1} = c_{m+1}*c_m - c*conj(c_m) + conj(c_{m-1}) =>
                          c_{2k+3} = c_{k+2}*c_{k+1} - c*conj(c_{k+1}) + conj(c_{k})
                } else {
                      compute [c_{2k}, c_{2k+1}, c_{2k+2}] from [c_{k}, c_{k+1}, c_{k+2}]:
                      c_{2m} = c_m^2 - 2*conj(c_m) =>
                          c_{2k} = c_{k}^2 - 2*conj(c_{k}),
                          c_{2k+2} = c_{k+1}^2 - 2*conj(c_{k+1}),
                      c_{2m-1} = c_{m-1}*c_m - conj(c)*conj(c_m) + conj(c_{m+1}) =>
                          c_{2k+1} = c_{k}*c_{k+1} - conj(c)*conj(c_{k+1}) + conj(c_{k+2})
                }
             */
            let cond = mj.ct_eq(&1);
            BNFp4::conditional_swap(&mut c_k0, &mut c_k2, cond);
            let mut c_t0 = c_k0.sq() - c_k0.conj().double();
            let mut c_t1 = c_k1.sq() - c_k1.conj().double();
            c_k1 = c_k1.ch(&c_k0, &BNFp4::conditional_select(&c_conj, &self, cond)) + c_k2.conj();
            BNFp4::conditional_swap(&mut c_t0, &mut c_t1, cond);
            c_k0 = c_t0;
            c_k2 = c_t1;
        }
        assert_eq!((k << 1) + Uint::from_word(w[0] & 1), *m);
        let cond = (w[0] & 1).ct_eq(&1);
        BNFp4::conditional_select(&c_k0, &c_k1, cond)
    }

    /// <b>F</b><sub><i>p&sup2;</i></sub>-norm of this <b>F</b><sub><i>p&#x2074;</i></sub> element,
    /// namely, if this element is <i>u + vw</i>, return <i>u&sup2; - v&sup2;&xi;</i>.
    #[inline]
    pub(crate) fn norm(&self) -> BNFp2<BN, LIMBS> {
        // (u + v*w)*(u - v*w) = u^2 - v^2*w^2 = u^2 - v^2*xi
        self.re.sq() - self.im.sq().mul_xi()
    }
}

impl<BN: BNParam, const LIMBS: usize> Add for BNFp4<BN, LIMBS> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self {
            re: self.re + rhs.re,
            im: self.im + rhs.im,
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> AddAssign for BNFp4<BN, LIMBS> {
    fn add_assign(&mut self, rhs: Self) {
        self.re += rhs.re;
        self.im += rhs.im;
    }
}

impl<BN: BNParam, const LIMBS: usize> BNField for BNFp4<BN, LIMBS> {
    /// Convert `self` to serialized (byte array) representation.
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

    /// Compute the square of this <b>F</b><sub><i>p&#x2074;</i></sub> element.
    #[inline]
    fn sq(&self) -> Self {
        // (u + v*w)^2 = u^2 + v^2*w^2 + 2*u*v*w = (u^2 + v^2*xi) + ((u + v)^2 - u^2 - v^2)*w
        let u2 = self.re.sq();
        let v2 = self.im.sq();
        let uv = (self.re + self.im).sq();
        Self {
            re: u2 + v2.mul_xi(),
            im: uv - u2 - v2
        }
    }

    /// Compute the cube of this <b>F</b><sub><i>p&sup2;</i></sub> element.
    #[inline]
    fn cb(&self) -> Self {
        // (u + v*w)^3 = u*((u^2 + v^2*xi) + 2*v^2*xi) + v*(2*u^2 + (u^2 + v^2*xi))*w
        let re2 = self.re.sq();
        let im2 = self.im.sq().mul_xi();
        let s = re2 + im2;
        Self {
            re: self.re*(s + im2 + im2),
            im: self.im*(re2 + re2 + s)
        }
    }

    /// Compute the inverse of this <b>F</b><sub><i>p&#x2074;</i></sub> element
    /// (or 0, if this element is itself 0).
    #[inline]
    fn inv(&self) -> Self {
        // (u + v*w)^-1 = (u - v*w)/((u + v*w)((u - v*w))
        // = (u - v*w)/(u^2 - v^2*xi) = norm^-1*conj.
        self.norm().inv()*self.conj()
    }
}

impl<BN: BNParam, const LIMBS: usize> Clone for BNFp4<BN, LIMBS> {
    fn clone(&self) -> Self {
        Self { re: self.re.clone(), im: self.im.clone() }
    }
}

impl<BN: BNParam, const LIMBS: usize> ConditionallySelectable for BNFp4<BN, LIMBS> {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self {
            re: BNFp2::conditional_select(&a.re, &b.re, choice),
            im: BNFp2::conditional_select(&a.im, &b.im, choice),
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> ConstantTimeEq for BNFp4<BN, LIMBS> {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.re.ct_eq(&other.re) & self.im.ct_eq(&other.im)
    }

    fn ct_ne(&self, other: &Self) -> Choice {
        self.re.ct_ne(&other.re) | self.im.ct_ne(&other.im)
    }
}

impl<BN: BNParam, const LIMBS: usize> Copy for BNFp4<BN, LIMBS> {}

impl<BN: BNParam, const LIMBS: usize> Debug for BNFp4<BN, LIMBS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self, f)
    }
}

impl<BN: BNParam, const LIMBS: usize> Display for BNFp4<BN, LIMBS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if bool::from(self.im.is_zero()) {
            write!(f, "{}", self.re)
        } else if bool::from(self.re.is_zero()) {
            write!(f, "({})*w", self.im)
        } else {
            write!(f, "({}) + ({})*w", self.re, self.im)
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> Mul for BNFp4<BN, LIMBS> {
    type Output = Self;

    /// Compute a product in <b>F</b><sub><i>p&#x2074;</i></sub>.
    fn mul(self, rhs: Self) -> Self::Output {
        let mut val = self;
        val *= rhs;
        val
    }
}

impl<BN: BNParam, const LIMBS: usize> Mul<BNFp4<BN, LIMBS>> for Word {
    type Output = BNFp4<BN, LIMBS>;

    /// Compute the product of an integer left factor
    /// by a right factor from <b>F</b><sub><i>p&#x2074;</i></sub>.
    fn mul(self, rhs: BNFp4<BN, LIMBS>) -> Self::Output {
        Self::Output {
            re: self*rhs.re,
            im: self*rhs.im
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> Mul<BNFp4<BN, LIMBS>> for Uint<LIMBS> {
    type Output = BNFp4<BN, LIMBS>;

    /// Compute the product of an integer left factor
    /// by a right factor from <b>F</b><sub><i>p&#x2074;</i></sub>.
    fn mul(self, rhs: BNFp4<BN, LIMBS>) -> Self::Output {
        Self::Output {
            re: self*rhs.re,
            im: self*rhs.im
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> Mul<BNFp4<BN, LIMBS>> for BNFp<BN, LIMBS> {
    type Output = BNFp4<BN, LIMBS>;

    /// Compute the product of a left factor from <i><b>F</b><sub>p</sub></i>
    /// by a right factor from <b>F</b><sub><i>p&#x2074;</i></sub>.
    fn mul(self, rhs: BNFp4<BN, LIMBS>) -> Self::Output {
        Self::Output {
            re: self*rhs.re,
            im: self*rhs.im
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> Mul<BNFp4<BN, LIMBS>> for BNFp2<BN, LIMBS> {
    type Output = BNFp4<BN, LIMBS>;

    /// Compute the product of a left factor from <b>F</b><sub><i>p&sup2;</i></sub>
    /// by a right factor from <b>F</b><sub><i>p&#x2074;</i></sub>.
    fn mul(self, rhs: BNFp4<BN, LIMBS>) -> Self::Output {
        Self::Output {
            re: self*rhs.re,
            im: self*rhs.im
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> MulAssign for BNFp4<BN, LIMBS> {
    fn mul_assign(&mut self, rhs: Self) {
        // (a + b*w)*(u + v*w) = a*u + b*v*xi + (a*v + b*u)*w
        // (a + b)*(u + v) - a*u - b*v = a*v + b*u
        let re2 = self.re*rhs.re;
        let im2 = self.im*rhs.im;
        let mix = (self.re + self.im)*(rhs.re + rhs.im);
        self.re = re2 + im2.mul_xi();
        self.im = mix - re2 - im2;
    }
}

impl<BN: BNParam, const LIMBS: usize> Neg for BNFp4<BN, LIMBS> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::Output {
            re: -self.re,
            im: -self.im,
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> One for BNFp4<BN, LIMBS> {
    #[inline]
    fn one() -> Self {
        Self {
            re: BNFp2::one(),
            im: BNFp2::zero(),
        }
    }

    fn is_one(&self) -> Choice {
        self.re.is_one() & self.im.is_zero()
    }
}

impl<BN: BNParam, const LIMBS: usize> PartialEq for BNFp4<BN, LIMBS> {
    fn eq(&self, other: &Self) -> bool { self.ct_eq(&other).into() }

    fn ne(&self, other: &Self) -> bool { self.ct_ne(&other).into() }
}

impl<BN: BNParam, const LIMBS: usize> Random for BNFp4<BN, LIMBS> {
    /// Pick a uniform element from <b>F</b><sub><i>p&#x2074;</i></sub> by rejection sampling.
    fn random<R: RngCore + ?Sized>(rng: &mut R) -> Self {
        Self {
            re: BNFp2::random(rng),
            im: BNFp2::random(rng),
        }
    }

    /// Try to pick a uniform element from <b>F</b><sub><i>p&#x2074;</i></sub> by rejection sampling.
    fn try_random<R: TryRngCore + ?Sized>(rng: &mut R) -> Result<Self, <R as TryRngCore>::Error> where R: TryRngCore {
        let try_re = match BNFp2::try_random(rng) {
            Ok(val) => Ok(val),
            Err(e) => Err(e),
        }?;

        let try_im = match BNFp2::try_random(rng) {
            Ok(val) => Ok(val),
            Err(e) => Err(e),
        }?;

        Ok(Self { re: try_re, im: try_im })
    }
}

impl<BN: BNParam, const LIMBS: usize> Sub for BNFp4<BN, LIMBS> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self {
            re: self.re - rhs.re,
            im: self.im - rhs.im,
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> SubAssign for BNFp4<BN, LIMBS> {
    fn sub_assign(&mut self, rhs: Self) {
        self.re -= rhs.re;
        self.im -= rhs.im;
    }
}

impl<BN: BNParam, const LIMBS: usize> Zero for BNFp4<BN, LIMBS> {
    fn zero() -> Self {
        Self {
            re: BNFp2::zero(),
            im: BNFp2::zero(),
        }
    }

    fn is_zero(&self) -> Choice {
        self.re.is_zero() & self.im.is_zero()
    }

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

    /// General BNFp4 test template.
    #[allow(non_snake_case)]
    fn BNFp4_test<BN: BNParam, const LIMBS: usize>() {
        //let mut rng: SmallRng = SmallRng::from_seed([0; 32]);
        let mut rng = rand::rng();

        println!();
        println!("Performing {} BN{:03}Fp4 test(s)...", TESTS, 64*LIMBS - 2);
        let now = SystemTime::now();

        // neutral elements:
        //println!("0 = {}", BNFp4::zero());
        assert!(bool::from(BNFp4::<BN, LIMBS>::zero().is_zero()));
        //println!("1 = {}", BNFp4::one());
        assert!(bool::from(BNFp4::<BN, LIMBS>::one().is_one()));

        for _t in 0..TESTS {
            //println!("======== {}", _t);

            let e4: BNFp4<BN, LIMBS> = BNFp4::random(&mut rng);
            //println!("e4 = {}", e4);
            //println!("e4 + 0 = {}", e4 + BNFp4::zero());
            assert_eq!(e4 + BNFp4::zero(), e4);
            //println!("e4*1 = {}", e4*BNFp4::one());
            assert_eq!(e4*BNFp4::one(), e4);
            let e2: BNFp2<BN, LIMBS> = BNFp2::random(&mut rng);
            assert_eq!(BNFp4::from_base(e2), BNFp4::from(e2, BNFp2::zero()));

            // addition vs subtraction:
            //println!("-e4      = {}", -e4);
            //println!("e4 - e4  = {}", e4 - e4);
            //println!("e4+(-e4) = {}", e4 + (-e4));
            assert!(bool::from((e4 - e4).is_zero()));
            assert!(bool::from((e4 + (-e4)).is_zero()));

            // double and half:
            //println!("2*e4   = {}", e4.double());
            //println!("e4/2   = {}", e4.half());
            assert_eq!(e4.double().half(), e4);
            assert_eq!(e4.half().double(), e4);
            assert_eq!(e4.double()*e4.half(), e4.sq());

            // square and cube:
            //println!("e4^2       = {}", e4.sq());
            //println!("e4^2 = e4*e4 ? {}", e4.sq() == e4*e4);
            assert_eq!(e4.sq(), e4*e4);
            //println!("e4^3       = {}", e4.cb());
            //println!("e4^3 = e4*e4*e4 ? {}", e4.cb() == e4*e4*e4);
            assert_eq!(e4.cb(), e4*e4*e4);

            // norm:
            //println!("|e4| = {}", e4.norm());
            //println!("|e4| = e4*e4.conj() ? {}", bool::from((e4*e4.conj()).re.ct_eq(&e4.norm()) & (e4*e4.conj()).im.is_zero()));
            assert!(bool::from((e4*e4.conj()).re.ct_eq(&e4.norm()) & (e4*e4.conj()).im.is_zero()));

            // field inversion:
            //println!("e4^-1 = {}", e4.inv());
            //println!("e4*e4^-1 = {}", e4*e4.inv());
            assert!(bool::from((e4*e4.inv()).is_one()));

            // subgroup multiplication (Word*BNFp4, Uint*BNFp4, BNFp*BNFp4, and BNFp2*BNFp4):
            let p: Uint<LIMBS> = Uint::from_words(BN::MODULUS.try_into().unwrap());
            let k4: Word = rng.next_u64() & 0xF;
            //println!("k4*e4 = {}", k4*e4);
            //println!("k4*e4 ? {}", BNFp::from_word(k4)*e4);
            assert_eq!(k4*e4, BNFp::from_word(k4)*e4);
            let u4 = Uint::random_mod(&mut rng, &NonZero::new(p).unwrap());
            //println!("u4 = {}", u4.to_string_radix_vartime(20));
            //println!("u4*e4 = {}", u4*e4);
            assert_eq!(u4*e4, BNFp::from_uint(u4)*e4);
            assert_eq!(u4*e4, BNFp2::from_base(BNFp::from_uint(u4))*e4);

            // norm homomorphism:
            let e5 = BNFp4::random(&mut rng);
            //println!("e5 = {}", e5);
            //println!("|e5| = {}", e5.norm());
            //println!("|e4*e5| = |e4|*|e5| ? {}", (e4*e5).norm() == e4.norm()*e5.norm());
            assert_eq!((e4*e5).norm(), e4.norm()*e5.norm());

            let f4 = BNFp4::random(&mut rng);
            //println!("f4     = {}", f4);
            let g4 = BNFp4::random(&mut rng);
            //println!("g4     = {}", g4);

            // commutativity of addition and multiplication:
            //println!("e4 + f4 = {}", e4 + f4);
            //println!("f4 + e4 = {}", f4 + e4);
            assert_eq!(e4 + f4, f4 + e4);
            assert_eq!(e4*f4, f4*e4);

            // associativity:
            //println!("(e4 + f4) + g4 = {}", (e4 + f4) + g4);
            //println!("e4 + (f4 + g4) = {}", e4 + (f4 + g4));
            assert_eq!((e4 + f4) + g4, e4 + (f4 + g4));
            //println!("(e4*f4)*g4 = {}", (e4*f4)*g4);
            //println!("e4*(f4*g4) = {}", e4*(f4*g4));
            assert_eq!((e4*f4)*g4, e4*(f4*g4));
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
    fn BN062Fp4_test() {
        const LIMBS: usize = BN062Param::LIMBS;
        BNFp4_test::<BN062Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN126Fp4_test() {
        const LIMBS: usize = BN126Param::LIMBS;
        BNFp4_test::<BN126Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN190Fp4_test() {
        const LIMBS: usize = BN190Param::LIMBS;
        BNFp4_test::<BN190Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN254Fp4_test() {
        const LIMBS: usize = BN254Param::LIMBS;
        BNFp4_test::<BN254Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN318Fp4_test() {
        const LIMBS: usize = BN318Param::LIMBS;
        BNFp4_test::<BN318Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN382Fp4_test() {
        const LIMBS: usize = BN382Param::LIMBS;
        BNFp4_test::<BN382Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN446Fp4_test() {
        const LIMBS: usize = BN446Param::LIMBS;
        BNFp4_test::<BN446Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN510Fp4_test() {
        const LIMBS: usize = BN510Param::LIMBS;
        BNFp4_test::<BN510Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN574Fp4_test() {
        const LIMBS: usize = BN574Param::LIMBS;
        BNFp4_test::<BN574Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN638Fp4_test() {
        const LIMBS: usize = BN638Param::LIMBS;
        BNFp4_test::<BN638Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN702Fp4_test() {
        const LIMBS: usize = BN702Param::LIMBS;
        BNFp4_test::<BN702Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN766Fp4_test() {
        const LIMBS: usize = BN766Param::LIMBS;
        BNFp4_test::<BN766Param, LIMBS>();
    }

}
