#[cfg(not(any(target_pointer_width = "64")))]
compile_error!("this crate requires 64-bit limbs");

use crate::bnfp::BNFp;
use crate::bnfp2::BNFp2;
use crate::bnparam::BNParam;
use crate::bnzn::BNZn;
use crate::traits::{BNField, One};
use crypto_bigint::{Random, Uint, Zero};
use crypto_bigint::subtle::{Choice, ConditionallySelectable, ConstantTimeEq};
use crypto_bigint::rand_core::TryRngCore;
use rand::Rng;
use std::fmt::{Debug, Display, Formatter};
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

/// The group <b>G&#x2082;</b> &#x2254; <i>E'</i>&lbrack;<i>n</i>&rbrack;(<b>F</b><sub><i>p&sup2;</i></sub>)
/// of <b>F</b><sub><i>p&sup2;</i></sub>&thinsp;-rational <i>n</i>-torsion points on the curve twist <i>E'</i>/<b>F</b><sub><i>p&sup2;</i></sub>.
pub struct BNPoint2<BN: BNParam, const LIMBS: usize> {
    pub(crate) x: BNFp2<BN, LIMBS>,
    pub(crate) y: BNFp2<BN, LIMBS>,
    pub(crate) z: BNFp2<BN, LIMBS>,
}

/*
// the Litany of All Saints:
pub type BN062Point2 = BNPoint2<BN062Param, 1>;
pub type BN126Point2 = BNPoint2<BN126Param, 2>;
pub type BN190Point2 = BNPoint2<BN190Param, 3>;
pub type BN254Point2 = BNPoint2<BN254Param, 4>;
pub type BN318Point2 = BNPoint2<BN318Param, 5>;
pub type BN382Point2 = BNPoint2<BN382Param, 6>;
pub type BN446Point2 = BNPoint2<BN446Param, 7>;
pub type BN510Point2 = BNPoint2<BN510Param, 8>;
pub type BN574Point2 = BNPoint2<BN574Param, 9>;
pub type BN638Point2 = BNPoint2<BN638Param, 10>;
pub type BN702Point2 = BNPoint2<BN702Param, 11>;
pub type BN766Point2 = BNPoint2<BN766Param, 12>;
// */


impl<BN: BNParam, const LIMBS: usize> BNPoint2<BN, LIMBS> {

    /// Create a normalized point on a BN curve twist
    /// <i>E'</i>/<b>F</b><sub><i>p&sup2;</i></sub> : <i>Y'&sup2;Z'</i> = <i>X'&sup3;</i> + <i>b'Z'&sup3;</i>
    /// from a given affine <i>X'</i>-coordinate and the least significant bit (LSB) of the <i>Y'</i>-coordinate.
    ///
    /// NB: specify y_lsb as Choice::FALSE if LSB==0 and as Choice::TRUE if LSB==1.
    #[inline]
    pub(crate) fn new(x: BNFp2<BN, LIMBS>, y_lsb: Choice) -> Self {
        let bt = BNFp2::from_base(BNFp::from_word(BN::CURVE_B)).div_xi();
        let y2 = x.cb() + bt;
        let mut y = y2.sqrt(y_lsb);
        assert_eq!(y.sq(), y2);
        y = BNFp2::conditional_select(&y, &(-y), y.is_odd() ^ y_lsb);
        Self { x, y, z: BNFp2::one() }
    }

    /// Determine if given projective coordinates <i>X'</i>, <i>Y'</i>, and <i>Z'</i>
    /// specify a point on a BN curve twist <i>E'</i>/<b>F</b><sub><i>p&sup2;</i></sub> : <i>Y'&sup2;Z'</i> = <i>X'&sup3;</i> + <i>b'Z'&sup3;</i>.
    #[inline]
    pub fn is_point(x: BNFp2<BN, LIMBS>, y: BNFp2<BN, LIMBS>, z: BNFp2<BN, LIMBS>) -> Choice {
        // projective curve equation: Y'^2*Z' = X'^3 + b'*Z'^3 where b' = b/xi
        (y.sq()*z).ct_eq(&(x.cb() + BNFp2::from_word(BN::CURVE_B).div_xi()*z.cb()))
    }

    /// Create a normalized point on a BN curve twist
    /// <i>E'</i>/<b>F</b><sub><i>p&sup2;</i></sub> : <i>Y'&sup2;Z'</i> = <i>X'&sup3;</i> + <i>b'Z'&sup3;</i>
    /// from given affine coordinates <i>X'</i> and <i>Y'</i>.
    #[inline]
    fn from_affine(x: BNFp2<BN, LIMBS>, y: BNFp2<BN, LIMBS>) -> Self {
        assert!(bool::from(Self::is_point(x, y, BNFp2::one())));
        Self { x, y, z: BNFp2::one() }
    }

    /// Create a point on a BN curve twist <i>E'</i>/<b>F</b><sub><i>p&sup2;</i></sub> : <i>Y'&sup2;Z'</i> = <i>X'&sup3;</i> + <i>b'Z'&sup3;</i>
    /// from given projective coordinates <i>X'</i>, <i>Y'</i>, and <i>Z'</i>.
    #[inline]
    pub(crate) fn from_proj(x: BNFp2<BN, LIMBS>, y: BNFp2<BN, LIMBS>, z: BNFp2<BN, LIMBS>) -> Self {
        assert!(bool::from(Self::is_point(x, y, z)));
        Self { x: x.clone(), y: y.clone(), z: z.clone() }
    }

    /// Create an instance of the default generator of <i>n</i>-torsion <i>G&#x2082; &#x2254; (-i, 1)</i>
    /// on a BN curve twist <i>E'</i>/<b>F</b><sub><i>p&sup2;</i></sub> : <i>Y'&sup2;Z'</i> = <i>X'&sup3;</i> + <i>b'Z'&sup3;</i>.
    #[inline]
    pub fn default_generator() -> Self {
        Self::new(-BNFp2::i(), Choice::from(1)).elim_cof()
    }

    /// Hash input data into a point on the (quadratic extension field) <i>n</i>-torsion group
    /// <i><b>G</b>&#x2082;</i> &#x2254; <i>E'</i>&lbrack;<i>n</i>&rbrack;(<b>F</b><sub><i>p&sup2;</i></sub>)
    /// of a BN curve twist <i>E'</i>/<b>F</b><sub><i>p&sup2;</i></sub> :
    /// <i>Y'&sup2;Z'</i> = <i>X'&sup3;</i> + <i>b'Z'&sup3;</i> with SHAKE-128.
    #[inline]
    pub fn shake128(data: &[u8]) -> Self {
        Self::point_factory(BNFp2::shake128(data)).elim_cof()
    }

    /// Hash input data into a point on the (quadratic extension field) <i>n</i>-torsion group
    /// <i><b>G</b>&#x2082;</i> &#x2254; <i>E'</i>&lbrack;<i>n</i>&rbrack;(<b>F</b><sub><i>p&sup2;</i></sub>)
    /// of a BN curve twist <i>E'</i>/<b>F</b><sub><i>p&sup2;</i></sub> : <i>Y'&sup2;Z'</i> = <i>X'&sup3;</i> + <i>b'Z'&sup3;</i> with SHAKE-256.
    #[inline]
    pub fn shake256(data: &[u8]) -> Self {
        Self::point_factory(BNFp2::shake256(data)).elim_cof()
    }

    /// Compute a normalized (i.e. affine) point equivalent to this
    /// on a BN curve twist <i>E'</i>/<b>F</b><sub><i>p&sup2;</i></sub> : <i>Y'&sup2;Z'</i> = <i>X'&sup3;</i> + <i>b'Z'&sup3;</i>.
    #[inline]
    pub(crate) fn normalize(&self) -> Self {
        let ch = self.z.is_zero();
        let inv = BNFp2::conditional_select(&self.z, &self.y, ch).inv();
        Self {
            x: self.x*inv,
            y: self.y*inv,
            z: BNFp2::conditional_select(&BNFp2::one(), &BNFp2::zero(), ch),
        }
    }

    /// Compute &lbrack;<i>2&#x1D57;</i>&rbrack;<i>Q'</i> for a BN curve twist point
    /// <i>Q'</i> &in; <i>E'</i>/<b>F</b><sub><i>p&sup2;</i></sub> : <i>Y'&sup2;Z'</i> = <i>X'&sup3;</i> + <i>b'Z'&sup3;</i>
    /// (i.e. double <i>t</i> times) via complete elliptic point doubling.
    #[inline]
    pub fn double(&self, t: usize) -> Self {
        let mut d = self.clone();
        d.double_self(t);
        d
    }

    /// Compute &lbrack;<i>2&#x1D57;</i>&rbrack;<i>Q'</i> for a BN curve twist point
    /// <i>Q'</i> &in; <i>E'</i>/<b>F</b><sub><i>p&sup2;</i></sub> : <i>Y'&sup2;Z'</i> = <i>X'&sup3;</i> + <i>b'Z'&sup3;</i>
    /// (i.e. double <i>t</i> times) via complete elliptic point doubling.
    ///
    /// Reference:
    ///
    /// * Joost Renes, Craig Costello, Lejla Batina:
    /// <a href="https://link.springer.com/content/pdf/10.1007/978-3-662-49890-3_16">
    /// "Complete addition formulas for prime order elliptic curves"</a>
    /// (Algorithm 9), Eurocrypt 2016, LNCS 9665 (part I), pp. 403--428, Springer, 2016.
    #[inline]
    pub(crate) fn double_self(&mut self, t: usize) {
        let mut x = self.x;
        let mut y = self.y;
        let mut z = self.z;

        let mut t0: BNFp2<BN, LIMBS>;
        let mut t1: BNFp2<BN, LIMBS>;
        let mut t2: BNFp2<BN, LIMBS>;
        let mut x3: BNFp2<BN, LIMBS>;
        let mut y3: BNFp2<BN, LIMBS>;
        let mut z3: BNFp2<BN, LIMBS>;

        for _ in 0..t {
            t0 = y.sq();
            z3 = t0+t0;
            z3 = z3+z3;

            z3 = z3+z3;
            t1 = y*z;
            t2 = z*z;

            t2 = (3*BN::CURVE_B)*t2.div_xi();
            x3 = t2*z3;
            y3 = t0+t2;

            z3 = t1*z3;
            t1 = t2+t2;
            t2 = t1+t2;

            t0 = t0-t2;
            y3 = t0*y3;
            y3 = x3+y3;

            t1 = x*y;
            x3 = t0*t1;
            x3 = x3+x3;

            x = x3;
            y = y3;
            z = z3;
        }
        self.x = x;
        self.y = y;
        self.z = z;
    }

    /// Map a field element <i>t</i> &in; <b>F</b><sub><i>p&sup2;</i></sub> to a point on this BN curve twist
    /// using the isochronous Shallue-van de Woestijne method.
    ///
    /// NB: the output point is only guaranteed to be on the curve,
    /// <i>not</i> in the (quadratic extension field) <i>n</i>-torsion group
    /// <b>G</b><i>&#x2082;</i> &#x2254; <i>E'</i>&lbrack;<i>n</i>&rbrack;(<b>F</b><sub><i>p&sup2;</i></sub>),
    /// that is, cofactor multiplication is not implicitly applied here.
    ///
    /// If a point in <b>G</b><i>&#x2082;</i> is required, either resort to explicit
    /// cofactor multiplication or use method BNPoint2::shake256(.) instead.
    ///
    /// Reference:
    ///
    /// * Andrew Shallue, Christiaan E. van de Woestijne:
    /// "Construction of rational points on elliptic curves over finite fields."
    /// In: Hess, F., Pauli, S., Pohst, M. E. (eds.), <i>Algorithmic Number Theory -- ANTS-VII</i>,
    /// Lecture Notes in Computer Science, vol. 4076, pp. 510--524, 2006.
    /// Springer, Berlin Heidelberg, 2006.
    /// https://doi.org/10.1007/11792086_36
    #[inline]
    pub fn point_factory(t: BNFp2<BN, LIMBS>) -> BNPoint2<BN, LIMBS> {
        let one = BNFp2::one();
        let bt = BNFp2::from(BNFp::from_word(BN::FIELD_XI_RE), -BNFp::from_word(BN::FIELD_XI_IM));
        let sqrt_m3 = BNFp::from_words(BN::SQRT_NEG_3.try_into().unwrap());
        let num = sqrt_m3*t;  // sqrt(-3)*t
        let den = one + bt + t.sq();  // 1 + b + t^2
        // Montgomery's trick to use a single inversion, (num*den)^-1, to compute
        // the inverse of num = den*(num*den)^-1 and the inverse of den = num*(num*den)^-1:
        let monty = (num*den).inv();

        let w = num.sq()*monty;  // sqrt(-3)*t/(1 + b + t^2)
        let inv_w = den.sq()*monty;
        let svdw = BNFp2::from_base(BNFp::from_words(BN::SVDW.try_into().unwrap()));  // (-1 + sqrt(-3))/2

        // candidate x-coordinates:
        let x0 = svdw - t*w;  // (-1 + sqrt(-3))/2 - t*w
        let x1 = -(one + x0); // -1 - x_0
        let x2 = one + inv_w.sq(); // 1 + 1/w^2

        // quadratic characters of the corresponding curve equation RHS:
        let q0 = (x0.cb() + bt).legendre();  // legendre((x0^3 + b), p)
        assert_ne!(q0, 0);  // no point of order 2 exists on a curve of (large) prime order
        let q1 = (x1.cb() + bt).legendre();  // legendre((x1^3 + b), p)
        assert_ne!(q1, 0);  // no point of order 2 exists on a curve of (large) prime order

        // constant-time sequential search for the proper choice of x:
        let mut xc = x2;
        xc = BNFp2::conditional_select(&xc, &x1, q1.ct_eq(&1));
        xc = BNFp2::conditional_select(&xc, &x0, q0.ct_eq(&1));
        let leg = t.legendre();

        // point construction:
        BNPoint2::new(xc, leg.ct_ne(&0) & leg.ct_ne(&1))
    }

    /// Compute the <i>k</i>-th Frobenius endomorphism on the BN curve twist
    /// <i>E'</i>/<b>F</b><sub><i>p&sup2;</i></sub> : <i>Y'&sup2;Z'</i> = <i>X'&sup3;</i> + <i>b'Z'&sup3;</i>,
    /// namely the map <i>&psi;&#x1D4F;</i> : <i>E'</i> &#8594; <i>E'</i> defined as
    /// the composition <i>&psi;&#x1D4F;</i> &#x2254; <i>&phi;&#x207B;&sup1;</i>&nbsp;o&nbsp;<i>&pi;&#x1D4F;</i>&nbsp;o&nbsp;<i>&phi;</i>,
    /// where <i>&phi;</i> : <i>E'</i> &#8594; <i>E</i> is the embedding
    /// <i>&phi;</i>(<i>x'</i>, <i>y'</i>) = (<i>x'&xi;<sup>&frac13;</sup></i>, <i>y'&xi;<sup>&half;</sup></i>) and
    /// <i>&pi;</i> : <i>E</i> &#8594; <i>E</i> is the Frobenius endomorphism on <i>E</i>,
    /// <i>&pi;</i>(<i>x</i>, <i>y</i>) &#x2254; (<i>x&#x1D56;</i>, <i>y&#x1D56;</i>), with <i>0&leq;k&lt;12</i>.
    #[inline]
    pub(crate) fn psi(&self, k: usize) -> Self {
        let zeta = BNFp::from_words(BN::ZETA.try_into().unwrap());
        let sigma = BNFp::from_words(BN::THETA.try_into().unwrap());
        let one = BNFp::one();
        assert!(k < 12);
        match k {
            0 => self.clone(),
            1 => Self {
                x: -(zeta + one)*self.x.conj().mul_i(),
                y: -(zeta*sigma)*self.y.conj().mul_xi(),
                z: self.z.conj(),
            },
            2 => Self {
                x: zeta*self.x,
                y: -self.y,
                z: self.z,
            },
            3 => Self {
                x: self.x.conj().mul_i(),
                y: (zeta*sigma)*self.y.conj().mul_xi(),
                z: self.z.conj(),
            },
            4 => Self {
                x: -(zeta + one)*self.x,
                y: self.y,
                z: self.z,
            },
            5 => Self {
                x: zeta*self.x.conj().mul_i(),
                y: -(zeta*sigma)*self.y.conj().mul_xi(),
                z: self.z.conj(),
            },
            6 => Self {
                x: self.x,
                y: -self.y,
                z: self.z,
            },
            7 => Self {
                x: -(zeta + one)*self.x.conj().mul_i(),
                y: (zeta*sigma)*self.y.conj().mul_xi(),
                z: self.z.conj(),
            },
            8 => Self {
                x: zeta*self.x,
                y: self.y,
                z: self.z,
            },
            9 => Self {
                x: self.x.conj().mul_i(),
                y: -(zeta*sigma)*self.y.conj().mul_xi(),
                z: self.z.conj(),
            },
            10 => Self {
                x: -(zeta + one)*self.x,
                y: -self.y,
                z: self.z,
            },
            11 => Self {
                x: zeta*self.x.conj().mul_i(),
                y: (zeta*sigma)*self.y.conj().mul_xi(),
                z: self.z.conj(),
            },
            _ => self.clone(),  // just to make the compiler happy
        }
    }

    /// Compute &lbrack;<i>u</i>&rbrack;<i>`self`</i>.
    #[inline]
    fn mul_u(&self) -> Self {
        // since the coefficient u is public and fixed, the simple double-and-add method suffices:
        let u: Uint<LIMBS> = Uint::from_words(BN::U.try_into().unwrap());
        let mut v = self.clone();
        let ubits = u.bits();
        for k in (0..ubits-1).rev() {
            v.double_self(1);
            if bool::from(u.bit(k)) {
                v += *self;
            }
        }
        -v  // NB: constant U is actually |u| = -u.
    }

    /// Eliminate the cofactor from this point <i>Q</i> &in; <i>E'</i>/<b>F</b><sub><i>p&sup2;</i></sub>,
    /// yielding a point of <i>n</i>-torsion <i>Q'</i> &in; <b>G</b><i>&#x2082;</i> &#x2254;
    /// <i>E'</i>&lbrack;<i>n</i>&rbrack;(<b>F</b><sub><i>p&sup2;</i></sub>).
    ///
    /// NB: This operation is carried out through the efficient Frobenius endomorphism,
    /// <i>not</i> by cofactor multiplication, which would be more computationally expensive.
    ///
    /// References:
    ///
    /// * Mike Scott, Naomi Benger, Manuel Charlemagne, Luís J. Domínguez-Pérez, Ezekiel J. Kachisa:
    /// "Fast Hashing to <b>G</b><i>&#x2082;</i> on Pairing-Friendly Curves."
    /// In: Shacham, H., Waters, B. (eds.),
    /// <i>Pairing-Based Cryptography -- Pairing 2009</i>.
    /// Lecture Notes in Computer Science, vol. 5671, pp. 102–113.
    /// Springer, Berlin Heidelberg (2009).
    /// https://doi.org/10.1007/978-3-642-03298-1_8
    ///
    /// * Laura Fuentes-Castañeda, Edward Knapp, Francisco Rodríguez-Henríquez:
    /// "Faster Hashing to <b>G</b><i>&#x2082;</i>."
    /// In: <i>Selected Areas in Cryptography</i>. SAC 2011.
    /// Lecture Notes in Computer Science, vol. 7118, pp. 412--430, 2012.
    /// Springer, Berlin Heidelberg (2012).
    /// https://doi.org/10.1007/978-3-642-28496-0_25
    #[allow(non_snake_case)]
    #[inline]
    pub fn elim_cof(&self) -> Self {
        let Q = *self;
        let uQ = Q.mul_u();  // [u]Q
        let u3Q = uQ.double(1) + uQ;  // [3u]Q
        uQ + u3Q.psi(1) + uQ.psi(2) + Q.psi(3)
    }

    /// Convert `self` to byte array representation.
    /// This is the ANSI X9.62 Point-to-Octet-String Conversion primitive, compressed form.
    #[allow(non_snake_case)]
    #[inline]
    pub fn to_bytes(&self) -> Vec<u8> {
        let N = self.normalize();
        // ANSI X9.62 'compressed' prefix: 0x02 | lsb(N.y)
        let mut cp = 0x2u8;  // lsb(N.y) == 0
        cp.conditional_assign(&0x3u8, N.y.is_odd());  // lsb(N.y) == 1
        let mut bytes = Vec::new();
        bytes.push(cp);
        let mut next = N.x.to_bytes(); bytes.append(&mut next);
        bytes
    }

}

impl<BN: BNParam, const LIMBS: usize> Add for BNPoint2<BN, LIMBS> {
    type Output = Self;

    /// Complete elliptic point addition
    /// for a BN curve <i>E</i>/<b>F</b><sub><i>p</i></sub> : <i>Y&sup2;Z</i> = <i>X&sup3; + bZ&sup3;</i>.
    ///
    /// Reference:
    ///
    /// * Joost Renes, Craig Costello, Lejla Batina:
    /// <a href="https://link.springer.com/content/pdf/10.1007/978-3-662-49890-3_16">
    /// "Complete addition formulas for prime order elliptic curves"</a>
    /// (Algorithm 7), Eurocrypt 2016, LNCS 9665 (part I), pp. 403--428, Springer, 2016.
    fn add(self, other: Self) -> Self::Output {
        let mut point = self;
        point += other;
        point
    }
}

impl<BN: BNParam, const LIMBS: usize> AddAssign for BNPoint2<BN, LIMBS> {

    /// Complete elliptic point addition
    /// for a BN curve <i>E</i>/<b>F</b><sub><i>p</i></sub> : <i>Y&sup2;Z</i> = <i>X&sup3; + bZ&sup3;</i>.
    ///
    /// Reference:
    ///
    /// * Joost Renes, Craig Costello, Lejla Batina:
    /// <a href="https://link.springer.com/content/pdf/10.1007/978-3-662-49890-3_16">
    /// "Complete addition formulas for prime order elliptic curves"</a>
    /// (Algorithm 7), Eurocrypt 2016, LNCS 9665 (part I), pp. 403--428, Springer, 2016.
    fn add_assign(&mut self, pair: Self) {
        let x1 = self.x;
        let y1 = self.y;
        let z1 = self.z;
        let x2 = pair.x;
        let y2 = pair.y;
        let z2 = pair.z;

        let mut t0: BNFp2<BN, LIMBS>;
        let mut t1: BNFp2<BN, LIMBS>;
        let mut t2: BNFp2<BN, LIMBS>;
        let mut t3: BNFp2<BN, LIMBS>;
        let mut t4: BNFp2<BN, LIMBS>;
        let mut x3: BNFp2<BN, LIMBS>;
        let mut y3: BNFp2<BN, LIMBS>;
        let mut z3: BNFp2<BN, LIMBS>;

        t0 = x1*x2;
        t1 = y1*y2;
        t2 = z1*z2;

        t3 = x1 + y1;
        t4 = x2 + y2;
        t3 = t3*t4;

        t4 = t0 + t1;
        t3 = t3 - t4;
        t4 = y1 + z1;

        x3 = y2 + z2;
        t4 = t4*x3;
        x3 = t1 + t2;

        t4 = t4 - x3;
        x3 = x1 + z1;
        y3 = x2 + z2;

        x3 = x3*y3;
        y3 = t0 + t2;
        y3 = x3 - y3;

        x3 = t0 + t0;
        t0 = x3 + t0;
        t2 = (3*BN::CURVE_B)*t2.div_xi();

        z3 = t1 + t2;
        t1 = t1 - t2;
        y3 = (3*BN::CURVE_B)*y3.div_xi();

        x3 = t4*y3;
        t2 = t3*t1;
        x3 = t2 - x3;

        y3 = y3*t0;
        t1 = t1*z3;
        y3 = t1 + y3;

        t0 = t0*t3;
        z3 = z3*t4;
        z3 = z3 + t0;

        self.x = x3;
        self.y = y3;
        self.z = z3;
    }
}

impl<BN: BNParam, const LIMBS: usize> Clone for BNPoint2<BN, LIMBS> {
    fn clone(&self) -> Self {
        Self {
            x: self.x.clone(),
            y: self.y.clone(),
            z: self.z.clone(),
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> Copy for BNPoint2<BN, LIMBS> {}

impl<BN: BNParam, const LIMBS: usize> ConditionallySelectable for BNPoint2<BN, LIMBS> {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        let x = BNFp2::conditional_select(&a.x, &b.x, choice);
        let y = BNFp2::conditional_select(&a.y, &b.y, choice);
        let z = BNFp2::conditional_select(&a.z, &b.z, choice);
        Self { x, y, z }
    }
}

impl<BN: BNParam, const LIMBS: usize> ConstantTimeEq for BNPoint2<BN, LIMBS> {
    fn ct_eq(&self, pair: &Self) -> Choice {
        // x/z = pair.x/pair.z <=> x*pair.z = pair.x*z
        // y/z = pair.y/pair.z <=> y*pair.z = pair.y*z
        (self.x*pair.z).ct_eq(&(pair.x*self.z)) &
        (self.y*pair.z).ct_eq(&(pair.y*self.z))
    }

    fn ct_ne(&self, pair: &Self) -> Choice {
        // x/z != pair.x/pair.z <=> x*pair.z != pair.x*z
        // y/z != pair.y/pair.z <=> y*pair.z != pair.y*z
        (self.x*pair.z).ct_ne(&(pair.x*self.z)) |
        (self.y*pair.z).ct_ne(&(pair.y*self.z))
    }
}

impl<BN: BNParam, const LIMBS: usize> Debug for BNPoint2<BN, LIMBS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self, f)
    }
}

impl<BN: BNParam, const LIMBS: usize> Display for BNPoint2<BN, LIMBS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let normal = self.normalize();
        write!(f, "[{} : {} : {}]", normal.x, normal.y, normal.z)
    }
}

impl<BN: BNParam, const LIMBS: usize> Mul<BNPoint2<BN, LIMBS>> for Uint<LIMBS> {
    type Output = BNPoint2<BN, LIMBS>;

    fn mul(self, point: BNPoint2<BN, LIMBS>) -> Self::Output {
        let mut v = point;
        v *= self;
        v
    }
}

impl<BN: BNParam, const LIMBS: usize> Mul<BNPoint2<BN, LIMBS>> for BNZn<BN, LIMBS> {
    type Output = BNPoint2<BN, LIMBS>;

    fn mul(self, point: BNPoint2<BN, LIMBS>) -> Self::Output {
        let mut v = point;
        v *= self.to_uint();
        v
    }
}

impl<BN: BNParam, const LIMBS: usize> MulAssign<Uint<LIMBS>> for BNPoint2<BN, LIMBS> {

    /// Multiply a scalar (mod <i>n</i>) and a point via fixed-window multiplication.
    ///
    /// Reference:
    ///
    /// * Alfred J. Menezes, Paul C. van Oorschot, Scott A. Vanstone,
    /// <a href="https://cacr.uwaterloo.ca/hac/">"Handbook of Applied Cryptography"</a>,
    /// CRC Press (1997), section 14.6 (Exponentiation), algorithm 14.82.
    fn mul_assign(&mut self, scalar: Uint<LIMBS>) {
        // prepare a table such that t[d] = d*P, where 0 <= d < 16:
        let mut t = [Self::zero(); 16];
        t[1] = self.clone();
        for d in 1..8 {
            t[2*d] = t[d].double(1);  // (2*d)*P = 2*(d*P)
            t[2*d + 1] = t[2*d].clone() + *self;  // (2*d + 1)*P = 2*(d*P) + P
        }

        // perform fixed-window multiplication by scalar, one hex digit at a time:
        let mut v = Self::zero();  // accumulator
        let s = scalar.as_words();  // scalar
        for j in (0..s.len() << 4).rev() {  // scan the scalar from most to least significant nybble
            v.double_self(4);  // multiply the accumulator by 16
            let d = ((s[j >> 4] >> ((j & 0xF) << 2)) & 0xF) as usize;  // hex digit at index k
            // perform constant-time sequential search on t to extract t[d]:
            let mut w = Self::zero();
            for e in 0..16 {  // t[] contains 16 points...
                w = Self::conditional_select(&w, &t[e], e.ct_eq(&d)); // ... (of which only the d-th is to be kept)
            }
            v += w;  // accumulate pt[d] into v
        }
        *self = v
    }
}

impl<BN: BNParam, const LIMBS: usize> Neg for BNPoint2<BN, LIMBS> {
    type Output = Self;

    /// Compute the opposite of a point on a BN curve.
    fn neg(self) -> Self::Output {
        Self::Output {
            x: self.x,
            y: self.y.neg(),
            z: self.z,
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> PartialEq<Self> for BNPoint2<BN, LIMBS> {
    fn eq(&self, pair: &Self) -> bool {
        self.ct_eq(&pair).into()
    }

    fn ne(&self, pair: &Self) -> bool {
        self.ct_ne(&pair).into()
    }
}

impl<BN: BNParam, const LIMBS: usize> Random for BNPoint2<BN, LIMBS> {
    /// Pick a uniform point from the <i>n</i>-torsion of the BN curve twist
    /// <i>E'</i>/<b>F</b><sub><i>p&sup2;</i></sub> : <i>Y'&sup2;Z'</i> = <i>X'&sup3;</i> + <i>b'Z'&sup3;</i>.
    fn random<R: Rng + ?Sized>(rng: &mut R) -> Self {
        Self::point_factory(BNFp2::random(rng)).elim_cof()
    }

    /// Try to pick a uniform point from the <i>n</i>-torsion of the BN curve twist
    /// <i>E'</i>/<b>F</b><sub><i>p&sup2;</i></sub> : <i>Y'&sup2;Z'</i> = <i>X'&sup3;</i> + <i>b'Z'&sup3;</i>.
    fn try_random<R: TryRngCore + ?Sized>(rng: &mut R) -> Result<Self, <R as TryRngCore>::Error> where R: TryRngCore {
        match BNFp2::try_random(rng) {
            Ok(val) => Ok(Self::point_factory(val).elim_cof()),
            Err(e) => Err(e),
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> Sub for BNPoint2<BN, LIMBS> {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        let mut point = self;
        point -= other;
        point
    }
}

impl<BN: BNParam, const LIMBS: usize> SubAssign for BNPoint2<BN, LIMBS> {
    fn sub_assign(&mut self, pair: Self) {
        self.add_assign(pair.neg())
    }
}

impl<BN: BNParam, const LIMBS: usize> Zero for BNPoint2<BN, LIMBS> {
    /// Create an instance of the neutral element ("point at infinity") on a BN curve
    /// <i>E</i>/<b>F</b><sub><i>p</i></sub> : <i>Y&sup2;Z</i> = <i>X&sup3; + bZ&sup3;</i>
    /// in projective coordinates, hence &lbrack;<i>0</i> : <i>1</i> : <i>0</i>&rbrack;.
    fn zero() -> Self {
        Self { x: BNFp2::zero(), y: BNFp2::one(), z: BNFp2::zero() }
    }

    /// Determine if this projective point is the neutral element
    /// on a BN curve <i>E/<b>F</b><sub>p</sub>: Y&sup2;Z = X&sup3; + bZ&sup3;</i>.
    fn is_zero(&self) -> Choice {
        self.z.is_zero()
    }

    fn set_zero(&mut self) {
        self.x.set_zero();  // otherwise the curve equation Y^2*Z = X^3 + b*Z^3 is not satisfied
        self.z.set_zero()
    }
}


#[cfg(test)]
mod tests {
    use crate::bnparam::{BN062Param, BN126Param, BN190Param, BN254Param, BN318Param, BN382Param, BN446Param, BN510Param, BN574Param, BN638Param, BN702Param, BN766Param};
    use std::time::SystemTime;
    use super::*;

    const TESTS: usize = 100;

    /// General BNPoint test template.
    #[allow(non_snake_case)]
    fn BNPoint2_test<BN: BNParam, const LIMBS: usize>() {
        //let mut rng: SmallRng = SmallRng::from_seed([0; 32]);
        let mut rng = rand::rng();
        let p: Uint<LIMBS> = Uint::from_words(BN::MODULUS.try_into().unwrap());
        //println!("p = {}", p.to_string_radix_vartime(10));
        let n: Uint<LIMBS> = Uint::from_words(BN::ORDER.try_into().unwrap());
        //println!("n = {}", n.to_string_radix_vartime(10));
        let t: Uint<LIMBS> = p + Uint::ONE - n;
        //println!("t = {}", t.to_string_radix_vartime(10));

        println!();
        println!("Performing {} BN{:03}Point2 test(s)...", TESTS, 64*LIMBS - 2);
        let now = SystemTime::now();

        // neutral element:
        let O2: BNPoint2<BN, LIMBS> = BNPoint2::zero();
        //println!("O2 = {} is zero ? {}", O2, bool::from(O2.is_zero()));
        assert!(bool::from(O2.is_zero()));

        // default generator (-i, 1):
        let Gt: BNPoint2<BN, LIMBS> = BNPoint2::new(-BNFp2::i(), Choice::from(1));
        //println!("Gt = {}", Gt);
        let G2: BNPoint2<BN, LIMBS> = Gt.elim_cof();
        //println!("G2 = {}", G2);
        //println!("[n]G2 = {}", n*G2);
        assert!(bool::from((n*G2).is_zero()));

        for _t in 0..TESTS {
            //println!("======== {}", _t);

            // hashing to G_2:
            let Q1: BNPoint2<BN, LIMBS> = BNPoint2::point_factory(BNFp2::random(&mut rng)).elim_cof();
            //println!("Q1 = {}", Q1);
            let Q2: BNPoint2<BN, LIMBS> = BNPoint2::point_factory(BNFp2::random(&mut rng)).elim_cof();
            //println!("Q2 = {}", Q2);
            let Q3: BNPoint2<BN, LIMBS> = BNPoint2::point_factory(BNFp2::random(&mut rng)).elim_cof();
            //println!("Q3 = {}", Q3);

            // point construction:
            assert_eq!(Q1, BNPoint2::from_proj(Q1.x, Q1.y, Q1.z));
            let P1N = Q1.normalize();
            assert_eq!(Q1, BNPoint2::from_affine(P1N.x, P1N.y));
            assert_eq!(Q2, BNPoint2::from_proj(Q2.x, Q2.y, Q2.z));
            let P2N = Q2.normalize();
            assert_eq!(Q2, BNPoint2::from_affine(P2N.x, P2N.y));
            assert_eq!(Q3, BNPoint2::from_proj(Q3.x, Q3.y, Q3.z));
            let P3N = Q3.normalize();
            assert_eq!(Q3, BNPoint2::from_affine(P3N.x, P3N.y));

            // point order:
            //println!("[n]Q1 = O1 ? {}", bool::from((n*Q1).is_zero()));
            assert!(bool::from((n*Q1).is_zero()));
            //println!("[n]Q2 = O1 ? {}", bool::from((n*Q2).is_zero()));
            assert!(bool::from((n*Q2).is_zero()));
            //println!("[n]Q3 = O1 ? {}", bool::from((n*Q3).is_zero()));
            assert!(bool::from((n*Q3).is_zero()));

            // opposite point:
            //println!("Q1 + (-Q1) = O1 ? {}", bool::from((Q1 + (-Q1)).is_zero()));
            assert!(bool::from((Q1 + (-Q1)).is_zero()));
            //println!("Q2 + (-Q2) = O1 ? {}", bool::from((Q2 + (-Q2)).is_zero()));
            assert!(bool::from((Q2 + (-Q2)).is_zero()));
            //println!("Q3 + (-Q3) = O1 ? {}", bool::from((Q3 + (-Q3)).is_zero()));
            assert!(bool::from((Q3 + (-Q3)).is_zero()));

            // point doubling:
            //println!("[2]Q1 = Q1 + Q1 ? {}", Q1.double(1) == Q1 + Q1);
            assert_eq!(Q1.double(1), Q1 + Q1);
            //println!("[2]Q2 = Q2 + Q2 ? {}", Q2.double(1) == Q2 + Q2);
            assert_eq!(Q2.double(1), Q2 + Q2);
            //println!("[2]Q3 = Q3 + Q3 ? {}", Q3.double(1) == Q3 + Q3);
            assert_eq!(Q3.double(1), Q3 + Q3);

            // commutativity:
            //println!("Q1 + Q2 = Q2 + Q1 ? {}", Q1 + Q2 == Q2 + Q1);
            assert_eq!(Q1 + Q2, Q2 + Q1);
            //println!("Q1 + Q3 = Q3 + Q1 ? {}", Q1 + Q3 == Q3 + Q1);
            assert_eq!(Q1 + Q3, Q3 + Q1);
            //println!("Q2 + Q3 = Q3 + Q2 ? {}", Q2 + Q3 == Q3 + Q2);
            assert_eq!(Q2 + Q3, Q3 + Q2);

            // associativity:
            //println!("(Q1 + Q2) + Q3 = Q1 + (Q2 + Q3) ? {}", (Q1 + Q2) + Q3 == Q1 + (Q2 + Q3));
            assert_eq!((Q1 + Q2) + Q3, Q1 + (Q2 + Q3));

            // Frobenius endomorphism:
            //println!("psi^2(Q1) - [t]psi(Q1) + [p]Q1 = {}", Q1.psi(2) - t*Q1.psi(1) + p*Q1);
            assert!(bool::from((Q1.psi(2) - t*Q1.psi(1) + p*Q1).is_zero()));
            for k in 0..12usize {
                let mut Qpk = Q1;
                for _ in 0..k {
                    Qpk = Qpk.psi(1);
                }
                assert_eq!(Qpk, Q1.psi(k));
            }
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
    fn BN062Point2_test() {
        const LIMBS: usize = BN062Param::LIMBS;
        BNPoint2_test::<BN062Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN126Point2_test() {
        const LIMBS: usize = BN126Param::LIMBS;
        BNPoint2_test::<BN126Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN190Point2_test() {
        const LIMBS: usize = BN190Param::LIMBS;
        BNPoint2_test::<BN190Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN254Point2_test() {
        const LIMBS: usize = BN254Param::LIMBS;
        BNPoint2_test::<BN254Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN318Point2_test() {
        const LIMBS: usize = BN318Param::LIMBS;
        BNPoint2_test::<BN318Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN382Point2_test() {
        const LIMBS: usize = BN382Param::LIMBS;
        BNPoint2_test::<BN382Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN446Point2_test() {
        const LIMBS: usize = BN446Param::LIMBS;
        BNPoint2_test::<BN446Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN510Point2_test() {
        const LIMBS: usize = BN510Param::LIMBS;
        BNPoint2_test::<BN510Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN574Point2_test() {
        const LIMBS: usize = BN574Param::LIMBS;
        BNPoint2_test::<BN574Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN638Point2_test() {
        const LIMBS: usize = BN638Param::LIMBS;
        BNPoint2_test::<BN638Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN702Point2_test() {
        const LIMBS: usize = BN702Param::LIMBS;
        BNPoint2_test::<BN702Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN766Point2_test() {
        const LIMBS: usize = BN766Param::LIMBS;
        BNPoint2_test::<BN766Param, LIMBS>();
    }

}
