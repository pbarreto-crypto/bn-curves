#[cfg(not(any(target_pointer_width = "64")))]
compile_error!("this crate requires 64-bit limbs");

use crate::bnfp::BNFp;
use crate::bnfp2::BNFp2;
use crate::bnfp4::BNFp4;
use crate::bnparam::BNParam;
use crate::traits::One;
use crypto_bigint::{Random, Uint, Word, Zero};
use crypto_bigint::rand_core::{RngCore, TryRngCore};
use crypto_bigint::subtle::{Choice, ConditionallySelectable, ConstantTimeEq};
use std::fmt::{Debug, Display, Formatter};
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

/// The <b>F</b><sub><i>p&sup1;&#xFEFF;&sup2;</i></sub> = <b>F</b><sub><i>p&sup2;</i></sub>&lbrack;<i>z</i>&rbrack;/&lt;<i>z&#x2076; - &xi;</i>&gt;
/// extension field, with <i>&xi;</i> = <i>1 + i</i>.
/// NB: <i>z&#x2076;</i> = <i>&xi;</i>.
pub struct BNFp12<BN: BNParam, const LIMBS: usize> {
    pub(crate) v0: BNFp2<BN, LIMBS>,
    pub(crate) v1: BNFp2<BN, LIMBS>,
    pub(crate) v2: BNFp2<BN, LIMBS>,
    pub(crate) v3: BNFp2<BN, LIMBS>,
    pub(crate) v4: BNFp2<BN, LIMBS>,
    pub(crate) v5: BNFp2<BN, LIMBS>,
}

/*
// the Litany of All Saints:
pub type BN062Fp12 = BNFp12<BN062Param, 1>;
pub type BN126Fp12 = BNFp12<BN126Param, 2>;
pub type BN190Fp12 = BNFp12<BN190Param, 3>;
pub type BN254Fp12 = BNFp12<BN254Param, 4>;
pub type BN318Fp12 = BNFp12<BN318Param, 5>;
pub type BN382Fp12 = BNFp12<BN382Param, 6>;
pub type BN446Fp12 = BNFp12<BN446Param, 7>;
pub type BN510Fp12 = BNFp12<BN510Param, 8>;
pub type BN574Fp12 = BNFp12<BN574Param, 9>;
pub type BN638Fp12 = BNFp12<BN638Param, 10>;
pub type BN702Fp12 = BNFp12<BN702Param, 11>;
pub type BN766Fp12 = BNFp12<BN766Param, 12>;
// */


impl<BN: BNParam, const LIMBS: usize> BNFp12<BN, LIMBS> {
    /// Map an <b>F</b><sub><i>p&sup2;</i></sub> element to its <b>F</b><sub><i>p&sup1;&#xFEFF;&sup2;</i></sub> counterpart.
    #[inline]
    pub(crate) fn from_base(v0: BNFp2<BN, LIMBS>) -> Self {
        Self {
            v0, v1: BNFp2::zero(), v2: BNFp2::zero(), v3: BNFp2::zero(), v4: BNFp2::zero(), v5: BNFp2::zero()
        }
    }

    /// Assemble an <b>F</b><sub><i>p&sup1;&#xFEFF;&sup2;</i></sub> element from its components.
    #[inline]
    pub(crate) fn from(v: [BNFp2<BN, LIMBS>; 6]) -> Self {
        Self {
            v0: v[0], v1: v[1], v2: v[2], v3: v[3], v4: v[4], v5: v[5],
        }
    }

    /// Compute the value of twice this element.
    #[inline]
    pub fn double(&self) -> Self {
        Self {
            v0: self.v0.double(), v1: self.v1.double(), v2: self.v2.double(),
            v3: self.v3.double(), v4: self.v4.double(), v5: self.v5.double(),
        }
    }

    /// Compute the value of half this element.
    #[inline]
    pub fn half(&self) -> Self {
        Self {
            v0: self.v0.half(), v1: self.v1.half(), v2: self.v2.half(),
            v3: self.v3.half(), v4: self.v4.half(), v5: self.v5.half(),
        }
    }

    /// Compute <i>`self`&#x1D56;</i> in <b>F</b><sub><i>p&sup1;&#xFEFF;&sup2;</i></sub>.
    #[inline]
    pub fn frob(&self) -> Self {
        let zeta0 = BNFp::from_words(<[Word; LIMBS]>::try_from(BN::ZETA).unwrap());
        let zeta1 = -(zeta0 + BNFp::one());
        let theta = BNFp::from_words(<[Word; LIMBS]>::try_from(BN::THETA).unwrap());
        Self {
            v0: self.v0.conj(),
            v1: -zeta1*theta*self.v1.mul_xi().conj(),
            v2: zeta1*self.v2.conj().mul_i(),
            v3: -zeta0*theta*self.v3.conj().mul_xi(),
            v4: -zeta0*self.v4.conj(),
            v5: theta*self.v5.mul_xi().conj(),
        }
    }

    /// Compute <i>`self`</i><sup>(<i>p&sup2;</i>)<i>&#x1D50;</i></sup>,
    /// the <i>m</i>-th conjugate in <b>F</b><sub><i>p&sup1;&#xFEFF;&sup2;</i></sub> of `self`
    /// over <i><b>F</b><sub>p&sup2;</sub></i>, for <i>0 &leq; m &lt; 6</i>.
    #[inline]
    pub fn conj2(&self, m: usize) -> Self {
        /*
         * z^(p^2)  = -zeta*z
         * z^(p^4)  = -(zeta+1)*z = zeta^2*z
         * z^(p^6)  = -z
         * z^(p^8)  = zeta*z
         * z^(p^10) = (zeta+1)*z = -zeta^2*z
         *
         * v        = v_0 + v_1 z + v_2 z^2 + v_3 z^3 + v_4 z^4 + v_5 z^5 =>
         * v^(p^2)  = v_0 - v_1zeta z - v_2(zeta+1) z^2 - v_3 z^3 + v_4zeta z^4 + v_5(zeta+1) z^5
         * v^(p^4)  = v_0 - v_1(zeta+1) z + v_2zeta z^2 + v_3 z^3 - v_4 z^4(zeta+1) + v_5zeta z^5
         * v^(p^6)  = v_0 - v_1 z + v_2 z^2 - v_3 z^3 + v_4 z^4 - v_5 z^5
         * v^(p^8)  = v_0 + v_1zeta z - v_2(zeta+1) z^2 + v_3 z^3 + v_4zeta z^4 - v_5(zeta+1) z^5
         * v^(p^10) = v_0 + v_1(zeta+1) z + v_2zeta z^2 - v_3 z^3 - v_4 z^4(zeta+1) - v_5zeta z^5
         */
        assert!(m < 6);
        let zeta0 = BNFp::from_words(<[Word; LIMBS]>::try_from(BN::ZETA).unwrap());
        let zeta1 = -(zeta0 + BNFp::one());
        let v = match m {
            0 => [
                self.v0, self.v1, self.v2,
                self.v3, self.v4, self.v5,
            ],
            1 => [
                self.v0, -zeta1*self.v1, zeta0*self.v2,
                -self.v3, zeta1*self.v4, -zeta0*self.v5,
            ],
            2 => [
                self.v0, zeta0*self.v1, zeta1*self.v2,
                self.v3, zeta0*self.v4, zeta1*self.v5,
            ],
            3 => [
                 self.v0, -self.v1,  self.v2,
                -self.v3,  self.v4, -self.v5,
            ],
            4 => [
                self.v0, zeta1*self.v1, zeta0*self.v2,
                self.v3, zeta1*self.v4, zeta0*self.v5,
            ],
            5 => [
                self.v0, -zeta0*self.v1, zeta1*self.v2,
                -self.v3, zeta0*self.v4, -zeta1*self.v5,
            ],
            _ => [
                self.v0, self.v1, self.v2,
                self.v3, self.v4, self.v5,
            ]  // just to make the compiler happy
        };
        Self {
            v0: v[0], v1: v[1], v2: v[2], v3: v[3], v4: v[4], v5: v[5],
        }
    }

    /// Compute the <b>F</b><sub><i>p&#x2074;</i></sub>-norm of this <b>F</b><sub><i>p&sup1;&#xFEFF;&sup2;</i></sub> element.
    #[inline]
    pub fn norm4(&self) -> BNFp4<BN, LIMBS> {
        // w = w0 + w1*z + w2*z^2

        // w         = w0 + w1*z       + w2*z^2
        // w.conj(2) = w0 + w1*zeta0*z + w2*zeta1*z^2
        // w.conj(4) = w0 + w1*zeta1*z + w2*zeta0*z^2

        // w.conj(2)*w.conj(4) =
        // (w0 + w1*zeta0*z + w2*zeta1*z^2)*(w0 + w1*zeta1*z + w2*zeta0*z^2) =

        // w0*w0 + w0*w1*zeta1*z + w0*w2*zeta0*z^2 +
        // w1*zeta0*z*w0 + w1*zeta0*z*w1*zeta1*z + w1*zeta0*z*w2*zeta0*z^2 +
        // w2*zeta1*z^2*w0 + w2*zeta1*z^2*w1*zeta1*z + w2*zeta1*z^2*w2*zeta0*z^2 =

        // (w0^2 - w1*w2*z^3) + (w2^2*z^3 - w0*w1)*z + (w1^2 - w0*w2)*z^2 =
        // (w0^2 - w1*w2*tau) + (w2^2*tau - w0*w1)*z + (w1^2 - w0*w2)*z^2

        // :: w*w.conj(2)*w.conj(4) =
        // (w0 + w1*z + w2*z^2)*((w0^2 - w1*w2*tau) + (w2^2*tau - w0*w1)*z + (w1^2 - w0*w2)*z^2) =

        // w0*((w0^2 - w1*w2*tau) + (w2^2*tau - w0*w1)*z + (w1^2 - w0*w2)*z^2) +
        // w1*z*((w0^2 - w1*w2*tau) + (w2^2*tau - w0*w1)*z + (w1^2 - w0*w2)*z^2) +
        // w2*z^2*((w0^2 - w1*w2*tau) + (w2^2*tau - w0*w1)*z + (w1^2 - w0*w2)*z^2) =

        // w0*(w0^2 - w1*w2*tau) + w2*(w2^2*tau - w0*w1)*tau + w1*(w1^2 - w0*w2)*tau +
        // w0*(w2^2*tau - w0*w1)*z + w1*(w0^2 - w1*w2*tau)*z + w2*(w1^2 - w0*w2)*z^3*z +
        // w0*(w1^2 - w0*w2)*z^2 + w1*(w2^2*tau - w0*w1)*z^2 + w2*(w0^2 - w1*w2*tau)*z^2 =

        // w0*(w0^2 - w1*w2*tau) + w1*(w1^2 - w0*w2)*tau + w2*(w2^2*tau - w0*w1)*tau

        // |w| = w*w.conj(2)*w.conj(4) =
        // w0*(w0^2 - w1*w2*tau) + w1*(w1^2 - w0*w2)*tau + w2*(w2^2*tau - w0*w1)*tau =
        // (w0^3 - w0*w1*w2*tau) + (w1^3 - w0*w1*w2)*tau + (w2^3*tau - w0*w1*w2)*tau
        let w0 = BNFp4::from(self.v0, self.v3);
        let w1 = BNFp4::from(self.v1, self.v4);
        let w2 = BNFp4::from(self.v2, self.v5);
        let w012 = w0*w1*w2;
        (w0.cb() - w012.mul_tau()) +
        (w1.cb() - w012).mul_tau() +
        (w2.cb().mul_tau() - w012).mul_tau()
    }

    /// Compute the <b>F</b><sub><i>p&#x2074;</i></sub>-trace of this <b>F</b><sub><i>p&sup1;&#xFEFF;&sup2;</i></sub> element.
    #[inline]
    pub fn tr4(&self) -> BNFp4<BN, LIMBS> {
        3*BNFp4::from(self.v0, self.v3)
    }

    /// Compute the square of this <b>F</b><sub><i>p&sup1;&#xFEFF;&sup2;</i></sub> element.
    #[inline]
    pub fn sq(self) -> Self {
        // Karatsuba multiplication:

        let d_00 = self.v0.sq();
        let d_11 = self.v1.sq();
        let d_22 = self.v2.sq();
        let d_33 = self.v3.sq();
        let d_44 = self.v4.sq();
        let d_55 = self.v5.sq();

        let d_01 = (self.v0 + self.v1).sq() - d_00 - d_11;
        let d_02 = (self.v0 + self.v2).sq() - d_00 - d_22;
        let d_04 = (self.v0 + self.v4).sq() - d_00 - d_44;
        let d_13 = (self.v1 + self.v3).sq() - d_11 - d_33;
        let d_15 = (self.v1 + self.v5).sq() - d_11 - d_55;
        let d_23 = (self.v2 + self.v3).sq() - d_22 - d_33;
        let d_24 = (self.v2 + self.v4).sq() - d_22 - d_44;
        let d_35 = (self.v3 + self.v5).sq() - d_33 - d_55;
        let d_45 = (self.v4 + self.v5).sq() - d_44 - d_55;

        let s_01 = d_00 + d_11;
        let s_23 = d_22 + d_33;
        let s_45 = d_44 + d_55;
        let d_03 = (self.v0 + self.v1 + self.v2 + self.v3).sq()
            - (s_01 + s_23 + d_01 + d_02 + d_13 + d_23);
        let d_05 = (self.v0 + self.v1 + self.v4 + self.v5).sq()
            - (s_01 + s_45 + d_01 + d_04 + d_15 + d_45);
        let d_25 = (self.v2 + self.v3 + self.v4 + self.v5).sq()
            - (s_23 + s_45 + d_23 + d_24 + d_35 + d_45);

        Self {
            v0: (d_15 + d_24 + d_33).mul_xi() + d_00,
            v1: d_25.mul_xi() + d_01,
            v2: (d_35 + d_44).mul_xi() + d_02 + d_11,
            v3: d_45.mul_xi() + d_03,
            v4: d_55.mul_xi() + d_04 + d_13 + d_22,
            v5: d_05 + d_23,
        }
    }

    /// Compute the cube of this <b>F</b><sub><i>p&sup1;&#xFEFF;&sup2;</i></sub> element.
    #[inline]
    pub fn cb(self) -> Self {
        self.sq()*self
    }

    /// Compute the inverse of this <b>F</b><sub><i>p&sup1;&#xFEFF;&sup2;</i></sub> element
    /// (or 0, if this element is itself 0).
    #[inline]
    pub fn inv(&self) -> Self {
        // w = w0 + w1*z + w2*z^2
        // split this Fp12 element into its Fp4 components:
        let w0 = BNFp4::from(self.v0, self.v3);
        let w1 = BNFp4::from(self.v1, self.v4);
        let w2 = BNFp4::from(self.v2, self.v5);

        // w.conj(2)*w.conj(4) = (w0^2 - w1*w2*tau) + (w2^2*tau - w0*w1)*z + (w1^2 - w2*w0)*z^2
        // compute the components of the product of proper conjugates:
        let c0 = w0.sq() - w1*w2.mul_tau();
        let c1 = w2.sq().mul_tau() - w0*w1;
        let c2 = w1.sq() - w2*w0;
        assert_eq!(self.conj2(2)*self.conj2(4), Self::from([c0.re, c1.re, c2.re, c0.im, c1.im, c2.im]));

        // compute the inverse of the Fp4-norm:
        // |w| = w*w.conj(2)*w.conj(4) =
        // w0*(w0^2 - w1*w2*tau) + w1*(w1^2 - w2*w0)*tau + w2*(w2^2*tau - w0*w1)*tau
        let norm_inv = (w0*c0 + (w1*c2 + w2*c1).mul_tau()).inv();

        // |w| = w*w.conj(2)*w.conj(4) <=> w^-1 = |w|^-1*w.conj(2)*w.conj(4)
        // complete the inversion in Fp12:
        norm_inv*Self::from([c0.re, c1.re, c2.re, c0.im, c1.im, c2.im])
    }

    /// Compute <i>`self`&#x1D4F;</i> in <b>F</b><sub><i>p&sup1;&#xFEFF;&sup2;</i></sub>.
    #[inline]
    pub fn pow(&self, k: &Uint<LIMBS>) -> Self {
        // prepare a table such that t[d] = v^d, where 0 <= d < 16:
        let mut t = [Self::one(); 16];
        t[1] = self.clone();
        for d in 1..8 {
            t[2*d] = t[d].sq();  // v^(2*d) = (v^d)^2
            t[2*d + 1] = t[2*d].clone()*(*self);  // v^(2*d + 1) = (v^d)^2*v
        }

        // perform fixed-window raising to the exponent, one hex digit at a time:
        let mut v = Self::one();  // accumulator
        let x = k.as_words();  // exponent
        for j in (0..x.len() << 4).rev() {  // scan the exponent from most to least significant nybble
            v = v.sq().sq().sq().sq();  // raise the accumulator to the 16th
            let d = ((x[j >> 4] >> ((j & 0xF) << 2)) & 0xF) as usize;  // hex digit at index k
            // perform constant-time sequential search on t to extract t[d]:
            let mut w = Self::one();
            for e in 0..16 {  // t[] contains 16 serialized points...
                w = Self::conditional_select(&w, &t[e], e.ct_eq(&d)); // ... (of which only the d-th is to be kept)
            }
            v *= w;  // accumulate pt[d] into v
        }
        v
    }

    /// Compute <i>`self`&#x207F;</i> in <b>F</b><sub><i>p&sup1;&#xFEFF;&sup2;</i></sub>,
    /// where <i>n</i> is the BN curve order over <i><b>F</b><sub>p</sub></i>.
    #[inline]
    pub(crate) fn pow_n(&self) -> Self {
        // this method is local to the crate, and the exponent (restricted to the curve order)
        // is fixed, public, and fairly sparse, hence the square-and-multiply method suffices
        // (isochronous for that exponent, and more efficient than a fixed-window approach):
        let n = <[Word; LIMBS]>::try_from(BN::ORDER).unwrap();  // presumed NOT to be in Montgomery form
        let mut r = Self::one();
        for j in (0..64*LIMBS - 2).rev() {
            r = r.sq();
            if ((n[j >> 6] >> (j & 63)) & 1) == 1 {
                r *= *self;
            }
        }
        r
    }

    /// Compute <i>`self`&#x1D58;</i> in <b>F</b><sub><i>p&sup1;&#xFEFF;&sup2;</i></sub>,
    /// where <i>u</i> is the BN curve selector.
    #[inline]
    fn pow_u(&self) -> Self {
        // this method is private, and the exponent (restricted to the BN selector)
        // is fixed, public, and rather sparse, hence the square-and-multiply method suffices:
        // (isochronous for that exponent, and more efficient than a fixed-window approach):
        let u = <[Word; LIMBS]>::try_from(BN::U).unwrap();  // presumed NOT to be in Montgomery form
        let mut r = Self::one();
        for j in (0..16*LIMBS - 1).rev() {
            r = r.sq();
            if ((u[j >> 6] >> (j & 63)) & 1) == 1 {
                r *= *self;
            }
        }
        r
    }

    /// Compute <i>self<sup>(p&sup1;&sup2;-1)/n</sup></i> in <b>F</b><sub><i>p&sup1;&#xFEFF;&sup2;</i></sub>.
    ///
    /// Reference:
    ///
    /// * Mike Scott, Naomi Benger, Manuel Charlemagne, Luís J. Domínguez-Pérez, Ezekiel J. Kachisa:
    ///"On the Final Exponentiation for Calculating Pairings on Ordinary Elliptic Curves."
    /// In: Shacham, H., Waters, B. (eds), Pairing-Based Cryptography -- Pairing 2009.
    /// Lecture Notes in Computer Science, vol. 5671, pp, 78--88. Springer, 2009.
    /// https://doi.org/10.1007/978-3-642-03298-1_6
    #[inline]
    pub(crate) fn final_exp(&self) -> Self {
        // NB: u < 0 by choice!
        // p = 36*u^4 - 36*u^3 + 24*u^2 - 6*u + 1;

        let mut m = self.clone();

        // easy part of final exponentiation: m := m^((p^2 + 1)*(p^6 - 1))
        m = m.conj2(3)*m.inv();  // m = m^(p^6 - 1)
        m = m.conj2(1)*m;  // m = m^(p^2 + 1)
        assert_eq!(m.inv(), m.conj2(3));

        // hard part of final exponentiation: m := m^((p^4 - p^2 + 1)/n)
        let mu = m.pow_u();  // m^u
        let mu2 = mu.pow_u();  // m^(u^2)
        let mu3 = mu2.pow_u();  // m^(u^3)

        let mp = m.frob();
        let mp2 = m.conj2(1);
        let mp3 = mp2.frob();
        let mup = mu.frob();
        let mu2p = mu2.frob();
        let mu3p = mu3.frob();
        let mu2p2 = mu2.conj2(1);

        let y0 = mp*mp2*mp3;
        let y1 = m.conj2(3);  // conj(3) <-> inv()
        let y2 = mu2p2;
        let y3 = mup;
        let y4 = mu*mu2p.conj2(3);  // conj(3) <-> inv()
        let y5 = mu2.conj2(3);  // conj(3) <-> inv()
        let y6 = mu3*mu3p;

        let mut t0 = y6.sq();
        t0 = t0 *y4;
        t0 = t0 *y5;
        let mut t1 = y3*y5;
        t1 = t1*t0;
        t0 = t0 *y2;
        t1 = t1.sq();
        t1 = t1*t0;
        t1 = t1.sq();
        t0 = t1 *y1;
        t1 = t1 *y0;
        t0 = t0.sq();
        t0 = t0*t1;

        t0
    }

    /// Multiply this <b>F</b><sub><i>p&sup1;&#xFEFF;&sup2;</i></sub> element by a sparse one
    /// of form <i>v&#8320; + v&#8321;z + v&#8323;z&sup3;</i>.
    #[inline]
    pub(crate) fn mul_013(&mut self, rhs0: BNFp2<BN, LIMBS>, rhs1: BNFp2<BN, LIMBS>, rhs3: BNFp2<BN, LIMBS>) -> Self {
        // Karatsuba multiplication:

        let d_00 = self.v0*rhs0;
        let d_11 = self.v1*rhs1;
        let d_33 = self.v3*rhs3;

        let d_01 = (self.v0 + self.v1)*(rhs0 + rhs1) - d_00 - d_11;
        let d_02 = (self.v0 + self.v2)*rhs0 - d_00;
        let d_04 = (self.v0 + self.v4)*rhs0 - d_00;
        let d_13 = (self.v1 + self.v3)*(rhs1 + rhs3) - d_11 - d_33;
        let d_15 = (self.v1 + self.v5)*rhs1 - d_11;
        let d_23 = (self.v2 + self.v3)*rhs3 - d_33;
        let d_35 = (self.v3 + self.v5)*rhs3 - d_33;

        let d_03 = (self.v0 + self.v1 + self.v2 + self.v3)*(rhs0 + rhs1 + rhs3)
            - (d_00 + d_11 + d_33 + d_01 + d_02 + d_13 + d_23);
        let d_05 = (self.v0 + self.v1 + self.v4 + self.v5)*(rhs0 + rhs1)
            - (d_00 + d_11 + d_01 + d_04 + d_15);
        let d_25 = (self.v2 + self.v3 + self.v4 + self.v5)*rhs3
            - (d_33 + d_23 + d_35);

        Self {
            v0: (d_15 + d_33).mul_xi() + d_00,
            v1: d_25.mul_xi() + d_01,
            v2: d_35.mul_xi() + d_02 + d_11,
            v3: d_03,
            v4: d_04 + d_13,
            v5: d_05 + d_23,
        }
    }

    /// Multiply this <b>F</b><sub><i>p&sup1;&#xFEFF;&sup2;</i></sub> element by a sparse one
    /// of form <i>v&#8320; + v&#8322;z&sup2; + v&#8323;z&sup3;</i>.
    #[inline]
    pub(crate) fn mul_023(&mut self, rhs0: BNFp2<BN, LIMBS>, rhs2: BNFp2<BN, LIMBS>, rhs3: BNFp2<BN, LIMBS>) -> Self {
        // Karatsuba multiplication:

        let d_00 = self.v0*rhs0;
        let d_22 = self.v2*rhs2;
        let d_33 = self.v3*rhs3;

        let d_01 = (self.v0 + self.v1)*rhs0 - d_00;
        let d_02 = (self.v0 + self.v2)*(rhs0 + rhs2) - d_00 - d_22;
        let d_04 = (self.v0 + self.v4)*rhs0 - d_00;
        let d_13 = (self.v1 + self.v3)*rhs3 - d_33;
        let d_23 = (self.v2 + self.v3)*(rhs2 + rhs3) - d_22 - d_33;
        let d_24 = (self.v2 + self.v4)*rhs2 - d_22;
        let d_35 = (self.v3 + self.v5)*rhs3 - d_33;

        let d_03 = (self.v0 + self.v1 + self.v2 + self.v3)*(rhs0 + rhs2 + rhs3)
            - (d_00 + d_22 + d_33 + d_01 + d_02 + d_13 + d_23);
        let d_05 = (self.v0 + self.v1 + self.v4 + self.v5)*rhs0
            - (d_00 + d_01 + d_04);
        let d_25 = (self.v2 + self.v3 + self.v4 + self.v5)*(rhs2 + rhs3)
            - (d_22 + d_33 + d_23 + d_24 + d_35);

        Self {
            v0: (d_24 + d_33).mul_xi() + d_00,
            v1: d_25.mul_xi() + d_01,
            v2: d_35.mul_xi() + d_02,
            v3: d_03,
            v4: d_04 + d_13 + d_22,
            v5: d_05 + d_23,
        }
    }

    /// Convert `self` to serialized (byte array) representation.
    #[inline]
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = self.v0.to_bytes();
        let mut next = self.v1.to_bytes(); bytes.append(&mut next);
        let mut next = self.v2.to_bytes(); bytes.append(&mut next);
        let mut next = self.v3.to_bytes(); bytes.append(&mut next);
        let mut next = self.v4.to_bytes(); bytes.append(&mut next);
        let mut next = self.v5.to_bytes(); bytes.append(&mut next);
        bytes
    }

}

impl<BN: BNParam, const LIMBS: usize> Add for BNFp12<BN, LIMBS> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let mut val = self;
        val += rhs;
        val
    }
}

impl<BN: BNParam, const LIMBS: usize> AddAssign for BNFp12<BN, LIMBS> {
    fn add_assign(&mut self, rhs: Self) {
        self.v0 += rhs.v0;
        self.v1 += rhs.v1;
        self.v2 += rhs.v2;
        self.v3 += rhs.v3;
        self.v4 += rhs.v4;
        self.v5 += rhs.v5;
    }
}

impl<BN: BNParam, const LIMBS: usize> Clone for BNFp12<BN, LIMBS> {
    fn clone(&self) -> Self {
        Self {
            v0: self.v0.clone(), v1: self.v1.clone(), v2: self.v2.clone(),
            v3: self.v3.clone(), v4: self.v4.clone(), v5: self.v5.clone(),
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> ConditionallySelectable for BNFp12<BN, LIMBS> {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        let v0 = BNFp2::conditional_select(&a.v0, &b.v0, choice);
        let v1 = BNFp2::conditional_select(&a.v1, &b.v1, choice);
        let v2 = BNFp2::conditional_select(&a.v2, &b.v2, choice);
        let v3 = BNFp2::conditional_select(&a.v3, &b.v3, choice);
        let v4 = BNFp2::conditional_select(&a.v4, &b.v4, choice);
        let v5 = BNFp2::conditional_select(&a.v5, &b.v5, choice);
        Self { v0, v1, v2, v3, v4, v5 }
    }
}

impl<BN: BNParam, const LIMBS: usize> ConstantTimeEq for BNFp12<BN, LIMBS> {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.v0.ct_eq(&other.v0) & self.v1.ct_eq(&other.v1) & self.v2.ct_eq(&other.v2) &
        self.v3.ct_eq(&other.v3) & self.v4.ct_eq(&other.v4) & self.v5.ct_eq(&other.v5)
    }

    fn ct_ne(&self, other: &Self) -> Choice {
        self.v0.ct_ne(&other.v0) | self.v1.ct_ne(&other.v1) | self.v2.ct_ne(&other.v2) |
        self.v3.ct_ne(&other.v3) | self.v4.ct_ne(&other.v4) | self.v5.ct_ne(&other.v5)
    }
}

impl<BN: BNParam, const LIMBS: usize> Copy for BNFp12<BN, LIMBS> {}

impl<BN: BNParam, const LIMBS: usize> Debug for BNFp12<BN, LIMBS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self, f)
    }
}

impl<BN: BNParam, const LIMBS: usize> Display for BNFp12<BN, LIMBS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if bool::from(self.v1.is_zero() &
                      self.v2.is_zero() &
                      self.v3.is_zero() &
                      self.v4.is_zero() &
                      self.v5.is_zero()) {
            // element in F_{p^2}:
            write!(f, "{}", self.v0)
        } else if bool::from(self.v1.is_zero() & self.v2.is_zero() &
                                    self.v4.is_zero() & self.v5.is_zero()) {
            // element in F_{p^4}:
            write!(f, "({}) + ({})*z^3", self.v0, self.v3)
        } else if bool::from(self.v1.is_zero() & self.v3.is_zero() & self.v5.is_zero()) {
            // element in F_{p^6}:
            write!(f, "({}) + ({})*z^2 + ({})*z^4",
                   self.v0, self.v2, self.v4)
        } else {
            write!(f, "({}) + ({})*z + ({})*z^2 + ({})*z^3 + ({})*z^4 + ({})*z^5",
                self.v0, self.v1, self.v2, self.v3, self.v4, self.v5)
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> Mul for BNFp12<BN, LIMBS> {
    type Output = Self;

    /// Compute a product in <b>F</b><sub><i>p&sup1;&#xFEFF;&sup2;</i></sub>.
    fn mul(self, rhs: Self) -> Self::Output {
        let mut val = self;
        val *= rhs;
        val
    }
}

impl<BN: BNParam, const LIMBS: usize> Mul<BNFp12<BN, LIMBS>> for Word {
    type Output = BNFp12<BN, LIMBS>;

    /// Compute the product of an integer left factor
    /// by a right factor from <b>F</b><sub><i>p&sup1;&#xFEFF;&sup2;</i></sub>.
    fn mul(self, rhs: BNFp12<BN, LIMBS>) -> Self::Output {
        Self::Output {
            v0: self*rhs.v0, v1: self*rhs.v1, v2: self*rhs.v2,
            v3: self*rhs.v3, v4: self*rhs.v4, v5: self*rhs.v5
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> Mul<BNFp12<BN, LIMBS>> for Uint<LIMBS> {
    type Output = BNFp12<BN, LIMBS>;

    /// Compute the product of an integer left factor
    /// by a right factor from <b>F</b><sub><i>p&sup1;&#xFEFF;&sup2;</i></sub>.
    fn mul(self, rhs: BNFp12<BN, LIMBS>) -> Self::Output {
        Self::Output {
            v0: self*rhs.v0, v1: self*rhs.v1, v2: self*rhs.v2,
            v3: self*rhs.v3, v4: self*rhs.v4, v5: self*rhs.v5
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> Mul<BNFp12<BN, LIMBS>> for BNFp<BN, LIMBS> {
    type Output = BNFp12<BN, LIMBS>;

    /// Compute the product of a left factor from <i><b>F</b><sub>p</sub></i>
    /// by a right factor from <b>F</b><sub><i>p&sup1;&#xFEFF;&sup2;</i></sub>.
    fn mul(self, rhs: BNFp12<BN, LIMBS>) -> Self::Output {
        Self::Output {
            v0: self*rhs.v0, v1: self*rhs.v1, v2: self*rhs.v2,
            v3: self*rhs.v3, v4: self*rhs.v4, v5: self*rhs.v5
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> Mul<BNFp12<BN, LIMBS>> for BNFp2<BN, LIMBS> {
    type Output = BNFp12<BN, LIMBS>;

    /// Compute the product of a left factor from <i><b>F</b><sub>p&sup2;</sub></i>
    /// by a right factor from <b>F</b><sub><i>p&sup1;&#xFEFF;&sup2;</i></sub>.
    fn mul(self, rhs: BNFp12<BN, LIMBS>) -> Self::Output {
        Self::Output {
            v0: self*rhs.v0, v1: self*rhs.v1, v2: self*rhs.v2,
            v3: self*rhs.v3, v4: self*rhs.v4, v5: self*rhs.v5
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> Mul<BNFp12<BN, LIMBS>> for BNFp4<BN, LIMBS> {
    type Output = BNFp12<BN, LIMBS>;

    /// Compute the product of a left factor from <i><b>F</b><sub>p&#x2074;</sub></i>
    /// by a right factor from <b>F</b><sub><i>p&sup1;&#xFEFF;&sup2;</i></sub>.
    fn mul(self, rhs: BNFp12<BN, LIMBS>) -> Self::Output {
        let u0 = self*BNFp4::from(rhs.v0, rhs.v3);
        let u1 = self*BNFp4::from(rhs.v1, rhs.v4);
        let u2 = self*BNFp4::from(rhs.v2, rhs.v5);
        Self::Output {
            v0: u0.re, v1: u1.re, v2: u2.re,
            v3: u0.im, v4: u1.im, v5: u2.im,
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> MulAssign for BNFp12<BN, LIMBS> {
    fn mul_assign(&mut self, rhs: Self) {
        // Karatsuba multiplication:

        let d_00 = self.v0*rhs.v0;
        let d_11 = self.v1*rhs.v1;
        let d_22 = self.v2*rhs.v2;
        let d_33 = self.v3*rhs.v3;
        let d_44 = self.v4*rhs.v4;
        let d_55 = self.v5*rhs.v5;

        let d_01 = (self.v0 + self.v1)*(rhs.v0 + rhs.v1) - d_00 - d_11;
        let d_02 = (self.v0 + self.v2)*(rhs.v0 + rhs.v2) - d_00 - d_22;
        let d_04 = (self.v0 + self.v4)*(rhs.v0 + rhs.v4) - d_00 - d_44;
        let d_13 = (self.v1 + self.v3)*(rhs.v1 + rhs.v3) - d_11 - d_33;
        let d_15 = (self.v1 + self.v5)*(rhs.v1 + rhs.v5) - d_11 - d_55;
        let d_23 = (self.v2 + self.v3)*(rhs.v2 + rhs.v3) - d_22 - d_33;
        let d_24 = (self.v2 + self.v4)*(rhs.v2 + rhs.v4) - d_22 - d_44;
        let d_35 = (self.v3 + self.v5)*(rhs.v3 + rhs.v5) - d_33 - d_55;
        let d_45 = (self.v4 + self.v5)*(rhs.v4 + rhs.v5) - d_44 - d_55;

        let d_03 = (self.v0 + self.v1 + self.v2 + self.v3)*(rhs.v0 + rhs.v1 + rhs.v2 + rhs.v3)
            - (d_00 + d_11 + d_22 + d_33 + d_01 + d_02 + d_13 + d_23);
        let d_05 = (self.v0 + self.v1 + self.v4 + self.v5)*(rhs.v0 + rhs.v1 + rhs.v4 + rhs.v5)
            - (d_00 + d_11 + d_44 + d_55 + d_01 + d_04 + d_15 + d_45);
        let d_25 = (self.v2 + self.v3 + self.v4 + self.v5)*(rhs.v2 + rhs.v3 + rhs.v4 + rhs.v5)
            - (d_22 + d_33 + d_44 + d_55 + d_23 + d_24 + d_35 + d_45);

        self.v0 = (d_15 + d_24 + d_33).mul_xi() + d_00;
        self.v1 = d_25.mul_xi() + d_01;
        self.v2 = (d_35 + d_44).mul_xi() + d_02 + d_11;
        self.v3 = d_45.mul_xi() + d_03;
        self.v4 = d_55.mul_xi() + d_04 + d_13 + d_22;
        self.v5 = d_05 + d_23;
    }
}

impl<BN: BNParam, const LIMBS: usize> Neg for BNFp12<BN, LIMBS> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::Output {
            v0: -self.v0, v1: -self.v1, v2: -self.v2,
            v3: -self.v3, v4: -self.v4, v5: -self.v5
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> One for BNFp12<BN, LIMBS> {
    #[inline]
    fn one() -> Self {
        Self {
            v0: BNFp2::one(), v1: BNFp2::zero(), v2: BNFp2::zero(),
            v3: BNFp2::zero(), v4: BNFp2::zero(), v5: BNFp2::zero()
        }
    }

    fn is_one(&self) -> Choice {
        self.v0.is_one() &
        self.v1.is_zero() &
        self.v2.is_zero() &
        self.v3.is_zero() &
        self.v4.is_zero() &
        self.v5.is_zero()
    }
}

impl<BN: BNParam, const LIMBS: usize> PartialEq for BNFp12<BN, LIMBS> {
    fn eq(&self, other: &Self) -> bool { self.ct_eq(&other).into() }

    fn ne(&self, other: &Self) -> bool { self.ct_ne(&other).into() }
}

impl<BN: BNParam, const LIMBS: usize> Random for BNFp12<BN, LIMBS> {
    /// Pick a uniform element from <b>F</b><sub><i>p&sup1;&#xFEFF;&sup2;</i></sub> by rejection sampling.
    fn random<R: RngCore + ?Sized>(rng: &mut R) -> Self {
        Self {
            v0: BNFp2::random(rng),
            v1: BNFp2::random(rng),
            v2: BNFp2::random(rng),
            v3: BNFp2::random(rng),
            v4: BNFp2::random(rng),
            v5: BNFp2::random(rng),
        }
    }

    /// Try to pick a uniform element from <b>F</b><sub><i>p&sup1;&#xFEFF;&sup2;</i></sub> by rejection sampling.
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

        let try_v3 = match BNFp2::try_random(rng) {
            Ok(val) => Ok(val),
            Err(e) => Err(e),
        }?;

        let try_v4 = match BNFp2::try_random(rng) {
            Ok(val) => Ok(val),
            Err(e) => Err(e),
        }?;

        let try_v5 = match BNFp2::try_random(rng) {
            Ok(val) => Ok(val),
            Err(e) => Err(e),
        }?;

        Ok(Self { v0: try_v0, v1: try_v1, v2: try_v2, v3: try_v3, v4: try_v4, v5: try_v5 })
    }
}

impl<BN: BNParam, const LIMBS: usize> Sub for BNFp12<BN, LIMBS> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        let mut val = self;
        val -= rhs;
        val
    }
}

impl<BN: BNParam, const LIMBS: usize> SubAssign for BNFp12<BN, LIMBS> {
    fn sub_assign(&mut self, rhs: Self) {
        self.v0 -= rhs.v0;
        self.v1 -= rhs.v1;
        self.v2 -= rhs.v2;
        self.v3 -= rhs.v3;
        self.v4 -= rhs.v4;
        self.v5 -= rhs.v5;
    }
}

impl<BN: BNParam, const LIMBS: usize> Zero for BNFp12<BN, LIMBS> {
    fn zero() -> Self {
        Self {
            v0: BNFp2::zero(), v1: BNFp2::zero(), v2: BNFp2::zero(),
            v3: BNFp2::zero(), v4: BNFp2::zero(), v5: BNFp2::zero()
        }
    }

    fn is_zero(&self) -> Choice {
        self.v0.is_zero() & self.v1.is_zero() & self.v2.is_zero() &
        self.v3.is_zero() & self.v4.is_zero() & self.v5.is_zero()
    }

    fn set_zero(&mut self) {
        self.v0.set_zero();
        self.v1.set_zero();
        self.v2.set_zero();
        self.v3.set_zero();
        self.v4.set_zero();
        self.v5.set_zero();
    }
}


#[cfg(test)]
mod tests {
    use crate::bnparam::{BN062Param, BN126Param, BN190Param, BN254Param, BN318Param, BN382Param, BN446Param, BN510Param, BN574Param, BN638Param, BN702Param, BN766Param};
    use crypto_bigint::{NonZero, RandomMod};
    use std::time::SystemTime;
    use super::*;

    const TESTS: usize = 100;

    /// General BNFp12 test template.
    #[allow(non_snake_case)]
    fn BNFp12_test<BN: BNParam, const LIMBS: usize>() {
        //let mut rng: SmallRng = SmallRng::from_seed([0; 32]);
        let mut rng = rand::rng();

        println!();
        println!("Performing {} BN{:03}Fp12 test(s)...", TESTS, 64*LIMBS - 2);
        let now = SystemTime::now();

        // neutral elements:
        //println!("0 = {}", BNFp12::zero());
        assert!(bool::from(BNFp12::<BN, LIMBS>::zero().is_zero()));
        //println!("1 = {}", BNFp12::one());
        assert!(bool::from(BNFp12::<BN, LIMBS>::one().is_one()));

        for _t in 0..TESTS {
            //println!("======== {}", _t);

            let e12: BNFp12<BN, LIMBS> = BNFp12::random(&mut rng);
            //println!("e12 = {}", e12);
            //println!("e12 + 0 = {}", e12 + BNFp12::zero());
            assert_eq!(e12 + BNFp12::zero(), e12);
            //println!("e12*1 = {}", e12*BNFp12::one());
            assert_eq!(e12*BNFp12::one(), e12);
            let e2: BNFp2<BN, LIMBS> = BNFp2::random(&mut rng);
            assert_eq!(BNFp12::from_base(e2), BNFp12::from([e2, BNFp2::zero(), BNFp2::zero(), BNFp2::zero(), BNFp2::zero(), BNFp2::zero()]));

            // addition vs subtraction:
            //println!("-e12      = {}", -e12);
            //println!("e12 - e12  = {}", e12 - e12);
            //println!("e12+(-e12) = {}", e12 + (-e12));
            assert!(bool::from((e12 - e12).is_zero()));
            assert!(bool::from((e12 + (-e12)).is_zero()));

            // double and half:
            //println!("2*e12   = {}", e12.double());
            //println!("e12/2   = {}", e12.half());
            assert_eq!(e12.double().half(), e12);
            assert_eq!(e12.half().double(), e12);
            assert_eq!(e12.double()*e12.half(), e12.sq());

            // square and cube:
            //println!("e12^2       = {}", e12.sq());
            //println!("e12^2 = e12*e12 ? {}", e12.sq() == e12*e12);
            assert_eq!(e12.sq(), e12*e12);
            //println!("e12^3       = {}", e12.cb());
            //println!("e12^3 = e12*e12*e12 ? {}", e12.cb() == e12*e12*e12);
            assert_eq!(e12.cb(), e12*e12*e12);

            // norm:
            //println!("|e12|_4 = {}", e12.norm4());
            //println!("|e12|_4 ? {}", e12*e12.conj(2)*e12.conj(4));
            let e12_conj_prod = e12*e12.conj2(2)*e12.conj2(4);
            let w0 = BNFp4::from(e12_conj_prod.v0, e12_conj_prod.v3);
            let w1 = BNFp4::from(e12_conj_prod.v1, e12_conj_prod.v4);
            let w2 = BNFp4::from(e12_conj_prod.v2, e12_conj_prod.v5);
            //println!("|e12|_4 = e12*e12.conj(2)*e12.conj(4) ? {}", bool::from(w0.ct_eq(&e12.norm4()) & w1.is_zero() & w2.is_zero()));
            assert!(bool::from(w0.ct_eq(&e12.norm4()) & w1.is_zero() & w2.is_zero()));

            // field inversion:
            //println!("e12^-1 = {};", e12.inv());
            //println!("e12*e12^-1 = {}", e12*e12.inv());
            assert!(bool::from((e12*e12.inv()).is_one()));

            // subring multiplication (Word*BNFp12, Uint*BNFp12, BNFp*BNFp12, BNFp2*BNFp12, BNFp4*BNFp12):
            let p: Uint<LIMBS> = Uint::from_words(BN::MODULUS.try_into().unwrap());
            let k12: Word = rng.next_u64() & 0xF;
            //println!("k12*e12 = {}", k12*e12);
            //println!("k12*e12 ? {}", BNFp::from_word(k12)*e12);
            assert_eq!(k12*e12, BNFp::from_word(k12)*e12);
            let u12 = Uint::random_mod(&mut rng, &NonZero::new(p).unwrap());
            //println!("u12 = {}", u12.to_string_radix_vartime(20));
            //println!("u12*e12 = {}", u12*e12);
            assert_eq!(u12*e12, BNFp::from_uint(u12)*e12);
            assert_eq!(u12*e12, BNFp2::from_base(BNFp::from_uint(u12))*e12);

            // norm homomorphism:
            let e13 = BNFp12::random(&mut rng);
            //println!("e13 = {}", e13);
            //println!("|e13| = {}", e13.norm());
            //println!("|e12*e13| = |e12|*|e13| ? {}", (e12*e13).norm() == e12.norm()*e13.norm());
            assert_eq!((e12*e13).norm4(), e12.norm4()*e13.norm4());

            let f12 = BNFp12::random(&mut rng);
            //println!("f12     = {}", f12);
            let g12 = BNFp12::random(&mut rng);
            //println!("g12     = {}", g12);

            // commutativity of addition and multiplication:
            //println!("e12 + f12 = {}", e12 + f12);
            //println!("f12 + e12 = {}", f12 + e12);
            assert_eq!(e12 + f12, f12 + e12);
            assert_eq!(e12*f12, f12*e12);

            // associativity:
            //println!("(e12 + f12) + g12 = {}", (e12 + f12) + g12);
            //println!("e12 + (f12 + g12) = {}", e12 + (f12 + g12));
            assert_eq!((e12 + f12) + g12, e12 + (f12 + g12));
            //println!("(e12*f12)*g12 = {}", (e12*f12)*g12);
            //println!("e12*(f12*g12) = {}", e12*(f12*g12));
            assert_eq!((e12*f12)*g12, e12*(f12*g12));

            // trace:
            let g: BNFp12<BN, LIMBS> = BNFp12::random(&mut rng).final_exp();  // random element of order n
            //println!(">>>> g = {}", g);
            //println!(">>>> |g|_4   = {}", g.norm4());
            assert!(bool::from(g.norm4().is_one()));
            //println!(">>>> tr(g)   = {}", g + g.conj(2) + g.conj(4));
            //println!(">>>> tr(g)   = {}", g.tr());
            let k = Uint::random(&mut rng);
            //println!(">>>> tr(g^k) = {}", g.pow(&k).tr());
            //println!(">>>> tr(g^k) ? {}", g.tr().trexp(&k));
            assert_eq!(g.pow(&k).tr4(), g.tr4().trexp(&k));
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
    fn BN062Fp12_test() {
        const LIMBS: usize = BN062Param::LIMBS;
        BNFp12_test::<BN062Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN126Fp12_test() {
        const LIMBS: usize = BN126Param::LIMBS;
        BNFp12_test::<BN126Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN190Fp12_test() {
        const LIMBS: usize = BN190Param::LIMBS;
        BNFp12_test::<BN190Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN254Fp12_test() {
        const LIMBS: usize = BN254Param::LIMBS;
        BNFp12_test::<BN254Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN318Fp12_test() {
        const LIMBS: usize = BN318Param::LIMBS;
        BNFp12_test::<BN318Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN382Fp12_test() {
        const LIMBS: usize = BN382Param::LIMBS;
        BNFp12_test::<BN382Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN446Fp12_test() {
        const LIMBS: usize = BN446Param::LIMBS;
        BNFp12_test::<BN446Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN510Fp12_test() {
        const LIMBS: usize = BN510Param::LIMBS;
        BNFp12_test::<BN510Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN574Fp12_test() {
        const LIMBS: usize = BN574Param::LIMBS;
        BNFp12_test::<BN574Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN638Fp12_test() {
        const LIMBS: usize = BN638Param::LIMBS;
        BNFp12_test::<BN638Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN702Fp12_test() {
        const LIMBS: usize = BN702Param::LIMBS;
        BNFp12_test::<BN702Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN766Fp12_test() {
        const LIMBS: usize = BN766Param::LIMBS;
        BNFp12_test::<BN766Param, LIMBS>();
    }

}
