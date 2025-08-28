#[cfg(not(any(target_pointer_width = "64")))]
compile_error!("this crate requires 64-bit limbs");

use crate::bnparam::BNParam;
use crate::traits::{BNField, One};
use crypto_bigint::{Integer, Limb, NonZero, Random, Uint, Word, Zero};
use crypto_bigint::rand_core::{RngCore, TryRngCore};
use crypto_bigint::subtle::{Choice, ConditionallySelectable, ConstantTimeEq, ConstantTimeLess};
use rand::Rng;
use sha3::{Shake128, Shake256};
use sha3::digest::ExtendableOutput;
use std::fmt::{Debug, Display, Formatter};
use std::marker::PhantomData;
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

pub struct BNFp<BN: BNParam, const LIMBS: usize>(
    #[doc(hidden)]
    pub Uint<LIMBS>,
    #[doc(hidden)]
    pub PhantomData<BN>,
);

/*
// the Litany of All Saints:
pub type BN062Fp = BNFp<BN062Param, 1>;
pub type BN126Fp = BNFp<BN126Param, 2>;
pub type BN190Fp = BNFp<BN190Param, 3>;
pub type BN254Fp = BNFp<BN254Param, 4>;
pub type BN318Fp = BNFp<BN318Param, 5>;
pub type BN382Fp = BNFp<BN382Param, 6>;
pub type BN446Fp = BNFp<BN446Param, 7>;
pub type BN510Fp = BNFp<BN510Param, 8>;
pub type BN574Fp = BNFp<BN574Param, 9>;
pub type BN638Fp = BNFp<BN638Param, 10>;
pub type BN702Fp = BNFp<BN702Param, 11>;
pub type BN766Fp = BNFp<BN766Param, 12>;
// */


impl<BN: BNParam, const LIMBS: usize> BNFp<BN, LIMBS> {
    /// Montgomery reduction of <i>t</i> = (<i>t_lo</i>, <i>t_hi</i>) in range 0..&lt;<i>p&times;2&#x02B7;</i>,
    /// where <i>p &lt; 2&#x02B7;</i> is the BN modulus and <i>w</i> &#x2254; <i>64&times;LIMBS</i>.
    ///
    /// Return <i>t&times;2&#8315;&#x02B7;</i> in range 0..&lt;<i>p</i>.
    #[inline]
    fn redc(t_lo: Uint<LIMBS>, t_hi: Uint<LIMBS>) -> Uint<LIMBS> {
        let p: Uint<LIMBS> = Uint::from_words(BN::MODULUS.try_into().unwrap());  // p < 2^w
        let q: Uint<LIMBS> = Uint::from_words(BN::NEG_INV_MOD.try_into().unwrap());  // q := -1/p mod 2^w
        // m ← ((t mod s)*q) mod s = (t_lo*q) mod s:
        let (m, _) = t_lo.widening_mul(&q);
        // t ← (t + m*p) / s:
        let (mp_lo, mp_hi) = m.widening_mul(&p);
        let (_, carry) = t_lo.carrying_add(&mp_lo, Limb::ZERO);
        let (t, _) = t_hi.carrying_add(&mp_hi, carry);
        // return if t < p { t } else { t - p }
        t - Uint::conditional_select(&p, &Uint::ZERO, t.ct_lt(&p))
    }

    /// Convert an unsigned integer (Uint) value <i>w</i> to Montgomery form,
    /// namely, the value <i>w&middot;s</i> mod <i>p</i> =
    /// redc((<i>w</i> mod <i>p</i>)&middot;(<i>s&sup2;</i> mod <i>p</i>)),
    /// where <i>s > p</i> is a power of 2.
    #[inline]
    pub fn from_uint(w: Uint<LIMBS>) -> Self {
        let s2: Uint<LIMBS> = Uint::from_words(BN::MONTY_P.try_into().unwrap());
        let (lo, hi) = w.widening_mul(&s2);
        Self {
            0: Self::redc(lo, hi),
            1: Default::default(),
        }
    }

    /// Convert a word-sized integer <i>w</i> to Montgomery form,
    /// namely, the value <i>w&middot;s</i> mod <i>p</i> =
    /// redc((<i>w</i> mod <i>p</i>)&middot;(<i>s&sup2;</i> mod <i>p</i>)),
    /// where <i>s > p</i> is a power of 2.
    #[inline]
    pub fn from_word(w: Word) -> Self {
        let s2: Uint<LIMBS> = Uint::from_words(BN::MONTY_P.try_into().unwrap());
        let (lo, hi) = Uint::from_word(w).widening_mul(&s2);
        Self {
            0: Self::redc(lo, hi),
            1: Default::default(),
        }
    }

    /// Convert an integer <i>w</i> represented by a sequence of words to Montgomery form,
    /// namely, the value <i>w&middot;s</i> mod <i>p</i> =
    /// redc((<i>w</i> mod <i>p</i>)&middot;(<i>s&sup2;</i> mod <i>p</i>)),
    /// where <i>s > p</i> is a power of 2.
    #[inline]
    pub(crate) fn from_words(v: [Word; LIMBS]) -> Self {
        let s2: Uint<LIMBS> = Uint::from_words(BN::MONTY_P.try_into().unwrap());
        let (lo, hi) = Uint::from_words(v).widening_mul(&s2);
        Self {
            0: Self::redc(lo, hi),
            1: Default::default(),
        }
    }

    /// Hash input data into a field element with SHAKE-128.
    ///
    /// Twice as much hash output is converted to the field element via Montgomery reduction.
    /// This ensures the deviation from uniform sampling over <b>F</b><sub><i>p</i></sub>
    /// is upper-bounded by <i>p&#8315;&sup1;</i>, well below the target
    /// adversary advantage <i>O</i>(<i>p<sup>-&frac12;</sup></i>).
    #[inline]
    pub fn shake128(data: &[u8]) -> Self {
        let mut out = vec![0u8; 2*LIMBS*8];  // twice the space taken by a base field element
        Shake128::digest_xof(data, &mut out);
        out[2*LIMBS*8 - 1] = 0;  // make sure the lift to Z does not exceed the squared BN modulus p^2
        let lo = Uint::from_le_slice(&out[0..LIMBS*8]);
        let hi = Uint::from_le_slice(&out[LIMBS*8..]);
        Self {
            0: Self::redc(lo, hi),
            1: Default::default(),
        }
    }

    /// Hash input data into a field element with SHAKE-256.
    ///
    /// Twice as much hash output is converted to the field element via Montgomery reduction.
    /// This ensures the deviation from uniform sampling over <b>F</b><sub><i>p</i></sub>
    /// is upper-bounded by <i>p&#8315;&sup1;</i>, well below the target
    /// adversary advantage <i>O</i>(<i>p<sup>-&frac12;</sup></i>).
    #[inline]
    pub fn shake256(data: &[u8]) -> Self {
        let mut out = vec![0u8; 2*LIMBS*8];  // twice the space taken by a base field element
        Shake256::digest_xof(data, &mut out);
        out[2*LIMBS*8 - 1] = 0;  // make sure the lift to Z does not exceed the squared BN modulus p^2
        let lo = Uint::from_le_slice(&out[0..LIMBS*8]);
        let hi = Uint::from_le_slice(&out[LIMBS*8..]);
        Self {
            0: Self::redc(lo, hi),
            1: Default::default(),
        }
    }

    /// Hash input data into a pair of base field elements with SHAKE-128.
    ///
    /// Mainly for use by the quadratic extension field.
    #[inline]
    pub(crate) fn shake128pair(data: &[u8]) -> (Self, Self) {
        let mut out = vec![0u8; 4*LIMBS*8];  // twice the space taken by two base field elements
        Shake128::digest_xof(data, &mut out);
        out[2*LIMBS*8 - 1] = 0;  // make sure the lift of re to Z does not exceed the squared BN modulus p^2
        out[4*LIMBS*8 - 1] = 0;  // make sure the lift of im to Z does not exceed the squared BN modulus p^2
        let re_lo = Uint::from_le_slice(&out[0..LIMBS*8]);
        let re_hi = Uint::from_le_slice(&out[LIMBS*8..2*LIMBS*8]);
        let im_lo = Uint::from_le_slice(&out[2*LIMBS*8..3*LIMBS*8]);
        let im_hi = Uint::from_le_slice(&out[3*LIMBS*8..]);
        (
            Self { 0: Self::redc(re_lo, re_hi), 1: Default::default(), },
            Self { 0: Self::redc(im_lo, im_hi), 1: Default::default(), },
        )
    }

    /// Hash input data into a pair of base field elements with SHAKE-256.
    ///
    /// Mainly for use by the quadratic extension field.
    #[inline]
    pub(crate) fn shake256pair(data: &[u8]) -> (Self, Self) {
        let mut out = vec![0u8; 4*LIMBS*8];  // twice the space taken by two base field elements
        Shake256::digest_xof(data, &mut out);
        out[2*LIMBS*8 - 1] = 0;  // make sure the lift of re to Z does not exceed the squared BN modulus p^2
        out[4*LIMBS*8 - 1] = 0;  // make sure the lift of im to Z does not exceed the squared BN modulus p^2
        let re_lo = Uint::from_le_slice(&out[0..LIMBS*8]);
        let re_hi = Uint::from_le_slice(&out[LIMBS*8..2*LIMBS*8]);
        let im_lo = Uint::from_le_slice(&out[2*LIMBS*8..3*LIMBS*8]);
        let im_hi = Uint::from_le_slice(&out[3*LIMBS*8..]);
        (
            Self { 0: Self::redc(re_lo, re_hi), 1: Default::default(), },
            Self { 0: Self::redc(im_lo, im_hi), 1: Default::default(), },
        )
    }

    /// Convert an integer in Montgomery form to plain representation.
    ///
    /// NB: the plain representation of <i>m</i> = <i>w&middot;r</i> mod <i>p</i> is
    /// <i>w</i> = redc(<i>m</i>), where <i>r > p</i> is a power of 2.
    #[inline]
    pub(crate) fn to_uint(&self) -> Uint<LIMBS> {
        Self::redc(self.0, Uint::ZERO)
    }

    /// Compute <i>v</i> = `self`<i>&#x02E3;</i> mod <i>p</i>.
    #[inline]
    fn pow(&self, x: Uint<LIMBS>) -> Self {
        // this method is private, and the exponent (restricted to square root and inversion only)
        // is fixed, public, and rather sparse, hence the square-and-multiply method suffices
        // (isochronous for either of these exponents, and more efficient than a fixed-window approach):
        let mut v = Self::one();
        let w = x.as_words();  // presumed NOT to be in Montgomery form
        for i in (0..LIMBS << 6).rev() {
            v = v.sq();
            if ((w[i >> 6] >> (i & 63)) & 1) == 1 {
                v *= *self;
            }
        }
        v
    }

    /// Determine if the plain representation of `self` is odd.
    #[inline]
    pub(crate) fn is_odd(&self) -> Choice {
        Self::redc(self.0, Uint::ZERO).is_odd()
    }

    /// Compute <i>r</i> = <i>&radic;`self`</i> = <i>`self`<sup>(p+1)/4</sup></i> mod <i>p</i>,
    /// which satisfies <i>r&sup2;</i> mod <i>p</i> = <i>`self`</i> if <i>`self`</i> is a quadratic residue mod <i>p</i>.
    #[inline]
    pub(crate) fn sqrt(&self) -> Self {
        let p: Uint<LIMBS> = Uint::from_words(BN::MODULUS.try_into().unwrap());
        self.pow((p + Uint::ONE).shr(2)) // sqrt exponent: (p + 1)/4
    }

    /// Compute <i>r</i> = <i>1/&radic;`self`</i> = <i>`self`<sup>(p+1)/4-1</sup></i> mod <i>p</i>,
    /// which satisfies <i>`self`&times;r&sup2;</i> mod <i>p = 1</i> if <i>`self` &ne; 0</i> and
    /// <i>`self`</i> is a quadratic residue mod <i>p</i>.
    #[inline]
    pub(crate) fn inv_sqrt(&self) -> Self {
        let p: Uint<LIMBS> = Uint::from_words(BN::MODULUS.try_into().unwrap());
        self.pow((p + Uint::ONE).shr(2) - Uint::ONE) // exponent: (p + 1)/4 - 1
    }

    /// Compute the Legendre symbol (<i>`self`/p</i>) in isochronous fashion:<br>
    /// &nbsp;   +1      if <i>`self`</i> is a nonzero quadratic residue mod <i>p</i>,<br>
    /// &nbsp;   &nbsp;0 if <i>`self`</i> = <i>0</i><br>
    /// &nbsp;   -1      if <i>`self`</i> is a nonzero quadratic non-residue mod <i>p</i>.
    ///
    /// NB: The Bernstein-Yang-based <a href="https://ia.cr/2021/1271">algorithm</a> by M. Hamburg
    /// is likely to be more efficient while also being isochronous, but its author claimed
    /// it is covered by a patent.  For that reason, that algorithm is entirely bypassed in this crate.
    #[inline]
    pub(crate) fn legendre(&self) -> isize {
        let p: Uint<LIMBS> = Uint::from_words(BN::MODULUS.try_into().unwrap());
        // (v/p) = v^((p - 1)/2) mod p for prime p
        let m = self.pow((p - Uint::ONE) >> 1).to_uint();
        // take the two least significant bits of m:
        let r = (m.as_words()[0] & 3) as isize;  // (v/p) = p-1, 0, 1
        // NB: since p = 3 (mod 4), it follows that -1 = 2 (mod 4)
        let val = -(r >> 1) + (r & 1);
        val
    }

    /// Compute the Jacobi symbol (<i>`self`/p</i>):<br>
    /// &nbsp;   +1      if <i>`self`</i> is a nonzero quadratic residue mod <i>p</i>,<br>
    /// &nbsp;   &nbsp;0 if <i>`self`</i> = <i>0</i><br>
    /// &nbsp;   -1      if <i>`self`</i> is a nonzero quadratic non-residue mod <i>p</i>.
    ///
    /// This is the same algorithm adopted in IEEE Std 1363:2000.
    /// See also:
    ///
    /// * S. M. Eikenberry, J. P. Sorenson: "Efficient Algorithms for Computing the Jacobi
    /// Symbol." <i>Journal of Symbolic Computation</i> <b>26</b>(4), pp. 509--523, Academic Press, 1998.
    /// https://doi.org/10.1006/jsco.1998.0226
    ///
    /// Warning: This is a <i>variable-time</i> algorithm.
    /// To avert side-channel leakage of information on its input,
    /// the algorithm randomizes it by multiplying it first by a random square mod <i>p</i>.
    /// This makes it slower than the isochronous, exponentiation-based Legendre algorithm.
    ///
    /// NB: The Bernstein-Yang-based <a href="https://ia.cr/2021/1271">algorithm</a> by M. Hamburg
    /// is likely to be more efficient while also being isochronous, but its author claimed
    /// it is covered by a patent.  For that reason, that algorithm is entirely bypassed in this crate.
    pub(crate) fn jacobi_vartime<R: RngCore + ?Sized>(&self, rng: &mut R) -> isize {
        let p: Uint<LIMBS> = Uint::from_words(BN::MODULUS.try_into().unwrap());
        let r = Self::random(rng).sq();  // random square in F_p
        let mut x = (*self*r).to_uint();
        let mut y = p;
        let mut j: isize = 1;
        while y > Uint::ONE {
            x = x.rem(&NonZero::new(y).unwrap());  // x = x mod y
            if x > y >> 1 {  // x > y/2
                x = y - x;
                if (y.as_words()[0] & 3) == 3 {  // y = 3 (mod 4)
                    j = -j;
                }
            }
            if x == Uint::ZERO {
                x = Uint::ONE;  y = Uint::ZERO;  j = 0;
            }
            while (x.as_words()[0] & 3) == 0 {  // x mod 4 = 0
                x = x >> 2;  // x = x/4
            }
            if (x.as_words()[0] & 1) == 0 {  // x mod 2 = 0
                x = x >> 1;  // x = x/2
                if (y.as_words()[0] & 7) == 3 || (y.as_words()[0] & 7) == 5 {  // y = ±3 (mod 8)
                    j = -j;
                }
            }
            if (x.as_words()[0] & 3) == 3 && (y.as_words()[0] & 3) == 3 {  // x = y = 3 (mod 4)
                j = -j;
            }
            let z = x;  x = y;  y = z;  // swap x <-> y
        }
        j
    }

}

impl<BN: BNParam, const LIMBS: usize> Add for BNFp<BN, LIMBS> {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        let p: Uint<LIMBS> = Uint::from_words(BN::MODULUS.try_into().unwrap());
        let nzp: NonZero<Uint<LIMBS>> = NonZero::new(p).unwrap();
        Self::Output {
            0: self.0.add_mod(&rhs.0, &nzp),
            1: Default::default(),
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> AddAssign for BNFp<BN, LIMBS> {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        let p: Uint<LIMBS> = Uint::from_words(BN::MODULUS.try_into().unwrap());
        let nzp: NonZero<Uint<LIMBS>> = NonZero::new(p).unwrap();
        self.0 = self.0.add_mod(&rhs.0, &nzp);
    }
}

impl<BN: BNParam, const LIMBS: usize> BNField for BNFp<BN, LIMBS> {
    /// Convert `self` to byte array representation.
    #[inline]
    fn to_bytes(&self) -> Vec<u8> {
        let binding = self.to_uint();
        let val = binding.as_words();
        assert_eq!(val.len(), LIMBS);
        let mut bytes = Vec::<u8>::with_capacity(LIMBS << 3);
        for j in 0..LIMBS {
            let u = val[j];
            bytes.push(u as u8);
            bytes.push((u >> 8) as u8);
            bytes.push((u >> 16) as u8);
            bytes.push((u >> 24) as u8);
            bytes.push((u >> 32) as u8);
            bytes.push((u >> 40) as u8);
            bytes.push((u >> 48) as u8);
            bytes.push((u >> 56) as u8);
        }
        bytes
    }

    /// Compute the value of twice this element.
    #[inline]
    fn double(&self) -> Self {
        let p: Uint<LIMBS> = Uint::from_words(BN::MODULUS.try_into().unwrap());
        let nzp: NonZero<Uint<LIMBS>> = NonZero::new(p).unwrap();
        Self {
            0: self.0.add_mod(&self.0, &nzp),
            1: Default::default(),
        }
    }

    /// Compute <i>u/2 mod p</i>.
    ///
    /// Technique: if the lift of <i>u</i> (either in plain or in Montgomery form)
    /// to &Zopf; is even, a right-shift does the required division;
    /// if it is odd, then <i>u + p</i> is even, and <i>0 <= (u + p) >> 1 < p</i> is the desired value.
    #[inline]
    fn half(&self) -> Self {
        let p: Uint<LIMBS> = Uint::from_words(BN::MODULUS.try_into().unwrap());
        Self {
            0: Uint::conditional_select(&self.0, &self.0.add(p), self.0.is_odd()) >> 1,
            1: Default::default(),
        }
    }

    /// Compute the square of a field element.
    #[inline]
    fn sq(&self) -> Self {
        let (lo, hi) = self.0.square_wide();
        Self {
            0: Self::redc(lo, hi),
            1: Default::default(),
        }
    }

    /// Compute the cube of a field element.
    #[inline]
    fn cb(&self) -> Self {
        let (lo, hi) = self.0.square_wide();
        let (lo, hi) = self.0.widening_mul(&Self::redc(lo, hi));
        Self {
            0: Self::redc(lo, hi),
            1: Default::default(),
        }
    }

    /// Compute <i>r</i> = <i>u&#8315;&sup1;</i> = <i>u&#x1D56;&#8315;&sup2;</i> mod <i>p</i>
    /// for <i>u</i> &#x2254; `self`, which satisfies
    /// <i>r&times;u</i> mod <i>p</i> = <i>1</i> if <i>u &ne; 0</i>.
    ///
    /// NB: crypto_bigint::Uint seems to offer an inversion functionality, but frankly,
    /// the usage instructions are poorly documented at best, entirely missing at worst.
    #[inline]
    fn inv(&self) -> Self {
        let p: Uint<LIMBS> = Uint::from_words(BN::MODULUS.try_into().unwrap());
        self.pow(p - Uint::from_word(2)) // inv exponent: p - 2
    }
}

impl<BN: BNParam, const LIMBS: usize> Clone for BNFp<BN, LIMBS> {
    fn clone(&self) -> Self {
        Self {
            0: self.0.clone(),
            1: Default::default(),
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> ConditionallySelectable for BNFp<BN, LIMBS> {
    #[inline]
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self {
            0: Uint::conditional_select(&a.0, &b.0, choice),
            1: Default::default(),
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> ConstantTimeEq for BNFp<BN, LIMBS> {
    #[inline]
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0.ct_eq(&other.0)
    }

    #[inline]
    fn ct_ne(&self, other: &Self) -> Choice {
        self.0.ct_ne(&other.0)
    }
}

impl<BN: BNParam, const LIMBS: usize> Copy for BNFp<BN, LIMBS> {}

impl<BN: BNParam, const LIMBS: usize> Debug for BNFp<BN, LIMBS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self, f)
    }
}

impl<BN: BNParam, const LIMBS: usize> Display for BNFp<BN, LIMBS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        /*
        // signed format:
        let p: Uint<LIMBS> = Uint::from_words(BN::MODULUS.try_into().unwrap());
        let half_p= p.shr(1);
        let val = Self::redc(self.0, Uint::ZERO);
        let str = if val <= half_p {
            val.to_string_radix_vartime(10)
        } else {
            "-".to_string() + val.neg_mod(&p).to_string_radix_vartime(10).as_str()
        };
        write!(f, "{}", str)
        // */
        write!(f, "{}", Self::redc(self.0, Uint::ZERO).to_string_radix_vartime(10))
    }
}

impl<BN: BNParam, const LIMBS: usize> Mul for BNFp<BN, LIMBS> {
    type Output = Self;

    /// Compute a product in <b>F</b><sub><i>p</i></sub>.
    #[inline]
    fn mul(self, rhs: Self) -> Self::Output {
        let (lo, hi) = self.0.widening_mul(&rhs.0);
        Self::Output {
            0: Self::redc(lo, hi),
            1: Default::default(),
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> Mul<BNFp<BN, LIMBS>> for Word {
    type Output = BNFp<BN, LIMBS>;

    /// Compute the product of a small integer left factor
    /// by a right factor from <b>F</b><sub><i>p</i></sub>.
    #[inline]
    fn mul(self, rhs: BNFp<BN, LIMBS>) -> Self::Output {
        assert!(self < 1 << 4);  // only meant for very small factors
        let mut val = Self::Output::zero();
        let mut fac = self as u8;
        let mut add = rhs;
        for _ in 0..4 {
            val = BNFp::conditional_select(&val, &(val + add), Choice::from(fac & 1));
            fac >>= 1;
            add += add;
        }
        //assert_eq!(val, BNFp::from_word(self)*rhs);
        val
    }
}

impl<BN: BNParam, const LIMBS: usize> Mul<BNFp<BN, LIMBS>> for i64 {
    type Output = BNFp<BN, LIMBS>;

    /// Compute the product of a single-precision, signed integer left factor
    /// by a right factor from <b>F</b><sub><i>p</i></sub>.
    ///
    /// This is a naïve implementation that treats the word-sized factor as a full-sized value.
    /// It would greatly benefit from dedicated i64&times;Int and/or i64&times;Uint functions.
    #[inline]
    fn mul(self, rhs: BNFp<BN, LIMBS>) -> Self::Output {
        let u = BNFp::from_word(self.unsigned_abs())*rhs;
        Self::Output::conditional_select(&u, &(-u), Choice::from((self < 0) as u8))
    }
}

impl<BN: BNParam, const LIMBS: usize> Mul<BNFp<BN, LIMBS>> for Uint<LIMBS> {
    type Output = BNFp<BN, LIMBS>;

    /// Compute the product of an integer left factor
    /// by a right factor from <b>F</b><sub><i>p</i></sub>.
    #[inline]
    fn mul(self, rhs: BNFp<BN, LIMBS>) -> Self::Output {
        BNFp::from_uint(self)*rhs
    }
}

impl<BN: BNParam, const LIMBS: usize> MulAssign for BNFp<BN, LIMBS> {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        let (lo, hi) = self.0.widening_mul(&rhs.0);
        self.0 = Self::redc(lo, hi);
    }
}

impl<BN: BNParam, const LIMBS: usize> Neg for BNFp<BN, LIMBS> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self::Output {
        let p: Uint<LIMBS> = Uint::from_words(BN::MODULUS.try_into().unwrap());
        let nzp: NonZero<Uint<LIMBS>> = NonZero::new(p).unwrap();
        Self::Output {
            0: self.0.neg_mod(&nzp),
            1: Default::default(),
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> One for BNFp<BN, LIMBS> {
    #[inline]
    fn one() -> Self {
        let r2: Uint<LIMBS> = Uint::from_words(BN::MONTY_P.try_into().unwrap());
        Self {
            0: Self::redc(r2, Uint::ZERO),  // (1*r) mod p
            1: Default::default(),
        }
    }

    fn is_one(&self) -> Choice {
        Self::redc(self.0, Uint::ZERO).ct_eq(&Uint::ONE)
    }
}

impl<BN: BNParam, const LIMBS: usize> PartialEq for BNFp<BN, LIMBS> {
    fn eq(&self, other: &Self) -> bool {
        self.0.ct_eq(&other.0).into()
    }

    fn ne(&self, other: &Self) -> bool {
        self.0.ct_ne(&other.0).into()
    }
}

impl<BN: BNParam, const LIMBS: usize> Random for BNFp<BN, LIMBS> {
    /// Pick a uniform element from <b>F</b><sub><i>p</i></sub> by rejection sampling mod <i>p</i>.
    fn random<R: RngCore + ?Sized>(rng: &mut R) -> Self {
        let p: Uint<LIMBS> = Uint::from_words(BN::MODULUS.try_into().unwrap());
        let top = BN::MODULUS.len() - 1;
        let mask = (1 << 62) - 1; // modulus bitlength is always 64*LIMBS - 2
        let mut w: [Word; LIMBS] = [0; LIMBS];
        loop {
            // uniformly sample the bit capacity of the modulus:
            rng.fill(&mut w);
            w[top] &= mask;
            // rejection sampling for the most significant word:
            while w[top].cmp(&BN::MODULUS[top]).is_gt() {  // this means the whole value exceeds the modulus
                w[top] = rng.next_u64() & mask;
            }
            // rejection sampling for the whole value:
            let r = Uint::from_words(w);
            if r.cmp(&p).is_lt() {
                return Self::from_uint(r);
            }
        }
    }

    /// Try to pick a uniform element from <b>F</b><sub><i>p</i></sub> by rejection sampling mod <i>p</i>.
    fn try_random<R: TryRngCore + ?Sized>(rng: &mut R) -> Result<Self, <R as TryRngCore>::Error> where R: TryRngCore {
        let p: Uint<LIMBS> = Uint::from_words(BN::MODULUS.try_into().unwrap());
        let top = BN::MODULUS.len() - 1;
        let mask = (1 << 62) - 1; // modulus bitlength is always 64*LIMBS - 2
        let mut w: [Word; LIMBS] = [0; LIMBS];
        loop {
            // uniformly sample the bit capacity of the modulus:
            for wi in &mut w {
                *wi = rng.try_next_u64()?
            }
            w[top] &= mask;
            // rejection sampling for the most significant word:
            while w[top].cmp(&BN::MODULUS[top]).is_gt() {  // this means the whole value exceeds the modulus
                w[top] = rng.try_next_u64()? & mask;
            }
            // rejection sampling for the whole value:
            let r = Uint::from_words(w);
            if r.cmp(&p).is_lt() {
                return Ok(Self::from_uint(r));
            }
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> Sub for BNFp<BN, LIMBS> {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        let p: Uint<LIMBS> = Uint::from_words(BN::MODULUS.try_into().unwrap());
        let nzp: NonZero<Uint<LIMBS>> = NonZero::new(p).unwrap();
        Self::Output {
            0: self.0.sub_mod(&rhs.0, &nzp),
            1: Default::default(),
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> SubAssign for BNFp<BN, LIMBS> {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        let p: Uint<LIMBS> = Uint::from_words(BN::MODULUS.try_into().unwrap());
        let nzp: NonZero<Uint<LIMBS>> = NonZero::new(p).unwrap();
        self.0 = self.0.sub_mod(&rhs.0, &nzp);
    }
}

impl<BN: BNParam, const LIMBS: usize> Zero for BNFp<BN, LIMBS> {
    #[inline]
    fn zero() -> Self {
        Self {
            0: Uint::ZERO,  // (0*r) mod p
            1: Default::default(),
        }
    }

    #[inline]
    fn is_zero(&self) -> Choice {
        self.0.is_zero()
    }

    fn set_zero(&mut self) {
        self.0.set_zero()
    }
}


#[cfg(test)]
mod tests {
    use crate::bnparam::{BN062Param, BN126Param, BN190Param, BN254Param, BN318Param, BN382Param, BN446Param, BN510Param, BN574Param, BN638Param, BN702Param, BN766Param};
    use crypto_bigint::NonZero;
    use crypto_bigint::rand_core::RngCore;
    use rand::Rng;
    use std::time::SystemTime;
    use super::*;

    const TESTS: usize = 100;

    /// General BNFp test template.
    #[allow(non_snake_case)]
    fn BNFp_test<BN: BNParam, const LIMBS: usize>() {

        //let mut rng: SmallRng = SmallRng::from_seed([0; 32]);
        let mut rng = rand::rng();
        let p: Uint<LIMBS> = Uint::from_words(BN::MODULUS.try_into().unwrap());
        let nzp = NonZero::new(p).unwrap();

        println!();
        println!("Performing {} BN{:03}Fp test(s)...", TESTS, 64*LIMBS - 2);
        let now = SystemTime::now();

        // neutral elements:
        //println!("0 = {}", BNFp::zero());
        assert!(bool::from(BNFp::<BN, LIMBS>::zero().is_zero()));
        //println!("1 = {}", BNFp::one());
        assert!(bool::from(BNFp::<BN, LIMBS>::one().is_one()));

        for _t in 0..TESTS {
            //println!("======== {}", _t);

            // Montgomery form:
            let v1: Word = rng.next_u64() & 0xF;
            //println!("v1 = {}", v1);
            let m1: BNFp<BN, LIMBS> = BNFp::from_word(v1);
            //println!("m1 ? {}", m1);
            assert_eq!(Uint::from_word(v1), m1.to_uint());

            let e1: BNFp<BN, LIMBS> = BNFp::random(&mut rng);
            //println!("e1     = {}", e1);
            //println!("e1 + 0 = {}", e1 + BNFp::zero());
            assert_eq!(e1 + BNFp::zero(), e1);
            //println!("e1*1   = {}", e1*BNFp::one());
            assert_eq!(e1*BNFp::one(), e1);

            // addition vs subtraction:
            //println!("-e1      = {}", -e1);
            //println!("e1 - e1  = {}", e1 - e1);
            //println!("e1+(-e1) = {}", e1 + (-e1));
            assert!(bool::from((e1 - e1).is_zero()));
            assert!(bool::from((e1 + (-e1)).is_zero()));

            // double and half:
            //println!("2*e1   = {}", e1.double());
            //println!("e1/2   = {}", e1.half());
            assert_eq!(e1.double().half(), e1);
            assert_eq!(e1.half().double(), e1);
            assert_eq!(e1.double()*e1.half(), e1.sq());

            // square and cube:
            //println!("e1^2   = {}", e1.sq());
            //println!("e1^2 = e1*e1 ? {}", e1.sq() == e1*e1);
            assert_eq!(e1.sq(), e1*e1);
            //println!("e1^3   = {}", e1.cb());
            //println!("e1^3 = e1*e1*e1 ? {}", e1.cb() == e1*e1*e1);
            assert_eq!(e1.cb(), e1*e1*e1);

            // field inversion:
            //println!("e1^-1  = {}", e1.inv());
            //println!("e1*e1^-1 = {}", e1*e1.inv());
            assert!(bool::from((e1*e1.inv()).is_one() | e1.is_zero()));

            // Legendre and Jacobi symbols:
            let leg = e1.legendre();
            let jac = e1.jacobi_vartime(&mut rng);
            //println!("leg = {}", leg);
            //println!("jac = {}", jac);
            assert_eq!(leg, jac);

            // square roots:
            let sr1 = e1.sqrt();
            //println!("leg(e1)    = {}", e1.legendre());
            //println!("sqrt(e1)   = {}", sr1);
            //println!("sqrt(e1)^2 = {}", sr1.sq());
            assert!(sr1.sq() == e1 || e1.legendre() < 0 && sr1.sq() == -e1);
            let inv_sr1 = e1.inv_sqrt();
            //println!("1/sqrt(e1) = {}", inv_sr1);
            //println!("e1*(1/sqrt(e1))^2 = {}", e1*inv_sr1.sq());
            assert!(bool::from((e1*inv_sr1.sq()).is_one() | e1.is_zero()) || e1.legendre() < 0);

            // hybrid multiplication (Word*BNFp and Uint*BNFp):
            let k1: Word = rng.next_u64() & 0xF;
            //println!("k1*e1 = {}", k1*e1);
            //println!("k1*e1 ? {}", BNFp::from_word(k1)*e1);
            assert_eq!(k1*e1, BNFp::from_word(k1)*e1);
            let mut w1: [Word; LIMBS] = [0; LIMBS];
            rng.fill(&mut w1);
            let u1 = Uint::from_words(w1).rem(&nzp);
            //println!("u1 = {}", u1.to_string_radix_vartime(10));
            //println!("u1*e1 = {}", u1*e1);
            //println!("u1*e1 ? {}", BNFp::from_words(w1)*e1);
            assert_eq!(u1*e1, BNFp::from_words(w1)*e1);

            let f1 = BNFp::random(&mut rng);
            //println!("f1     = {}", f1);
            let g1 = BNFp::random(&mut rng);
            //println!("g1     = {}", g1);

            // commutativity of addition and multiplication:
            //println!("e1 + f1 = {}", e1 + f1);
            //println!("f1 + e1 = {}", f1 + e1);
            assert_eq!(e1 + f1, f1 + e1);
            assert_eq!(e1*f1, f1*e1);

            // associativity:
            //println!("(e1 + f1) + g1 = {}", (e1 + f1) + g1);
            //println!("e1 + (f1 + g1) = {}", e1 + (f1 + g1));
            assert_eq!((e1 + f1) + g1, e1 + (f1 + g1));
            //println!("(e1*f1)*g1 = {}", (e1*f1)*g1);
            //println!("e1*(f1*g1) = {}", e1*(f1*g1));
            assert_eq!((e1*f1)*g1, e1*(f1*g1));
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
    fn BN062Fp_test() {
        const LIMBS: usize = BN062Param::LIMBS;
        BNFp_test::<BN062Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN126Fp_test() {
        const LIMBS: usize = BN126Param::LIMBS;
        BNFp_test::<BN126Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN190Fp_test() {
        const LIMBS: usize = BN190Param::LIMBS;
        BNFp_test::<BN190Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN254Fp_test() {
        const LIMBS: usize = BN254Param::LIMBS;
        BNFp_test::<BN254Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN318Fp_test() {
        const LIMBS: usize = BN318Param::LIMBS;
        BNFp_test::<BN318Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN382Fp_test() {
        const LIMBS: usize = BN382Param::LIMBS;
        BNFp_test::<BN382Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN446Fp_test() {
        const LIMBS: usize = BN446Param::LIMBS;
        BNFp_test::<BN446Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN510Fp_test() {
        const LIMBS: usize = BN510Param::LIMBS;
        BNFp_test::<BN510Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN574Fp_test() {
        const LIMBS: usize = BN574Param::LIMBS;
        BNFp_test::<BN574Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN638Fp_test() {
        const LIMBS: usize = BN638Param::LIMBS;
        BNFp_test::<BN638Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN702Fp_test() {
        const LIMBS: usize = BN702Param::LIMBS;
        BNFp_test::<BN702Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN766Fp_test() {
        const LIMBS: usize = BN766Param::LIMBS;
        BNFp_test::<BN766Param, LIMBS>();
    }

}
