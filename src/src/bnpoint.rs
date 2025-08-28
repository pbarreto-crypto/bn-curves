#[cfg(not(any(target_pointer_width = "64")))]
compile_error!("this crate requires 64-bit limbs");

use crate::bnfp::BNFp;
use crate::bnparam::BNParam;
use crate::bnzn::BNZn;
use crate::traits::{BNField, One};
use crypto_bigint::{Random, Uint, Zero};
use crypto_bigint::subtle::{Choice, ConditionallySelectable, ConstantTimeEq};
use crypto_bigint::rand_core::TryRngCore;
use rand::Rng;
use std::fmt::{Debug, Display, Formatter};
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

pub struct BNPoint<BN: BNParam, const LIMBS: usize> {
    pub(crate) x: BNFp<BN, LIMBS>,
    pub(crate) y: BNFp<BN, LIMBS>,
    pub(crate) z: BNFp<BN, LIMBS>,
}

/*
// the Litany of All Saints:
pub type BN062Point = BNPoint<BN062Param, 1>;
pub type BN126Point = BNPoint<BN126Param, 2>;
pub type BN190Point = BNPoint<BN190Param, 3>;
pub type BN254Point = BNPoint<BN254Param, 4>;
pub type BN318Point = BNPoint<BN318Param, 5>;
pub type BN382Point = BNPoint<BN382Param, 6>;
pub type BN446Point = BNPoint<BN446Param, 7>;
pub type BN510Point = BNPoint<BN510Param, 8>;
pub type BN574Point = BNPoint<BN574Param, 9>;
pub type BN638Point = BNPoint<BN638Param, 10>;
pub type BN702Point = BNPoint<BN702Param, 11>;
pub type BN766Point = BNPoint<BN766Param, 12>;
// */


impl<BN: BNParam, const LIMBS: usize> BNPoint<BN, LIMBS> {

    /// Create a normalized point on a BN curve <i>E/<b>F</b><sub>p</sub>: Y&sup2;Z = X&sup3; + bZ&sup3;</i>
    /// from a given affine <i>x</i>-coordinate and the least significant bit (LSB) of the <i>y</i>-coordinate.
    ///
    /// NB: specify y_lsb as Choice::FALSE if LSB==0 and as Choice::TRUE if LSB==1.
    #[inline]
    pub(crate) fn new(x: BNFp<BN, LIMBS>, y_lsb: Choice) -> Self {
        let y2 = x.cb() + BNFp::from_word(BN::CURVE_B);
        let mut y = y2.sqrt();
        assert_eq!(y.sq(), y2);
        y = BNFp::conditional_select(&y, &(-y), y.is_odd() ^ y_lsb);
        Self { x, y, z: BNFp::one() }
    }

    /// Determine if given projective coordinates <i>X</i>, <i>Y</i>, and <i>Z</i>
    /// specify a point on a BN curve <i>E/<b>F</b><sub>p</sub>: Y&sup2;Z = X&sup3; + bZ&sup3;</i>.
    #[inline]
    pub fn is_point(x: BNFp<BN, LIMBS>, y: BNFp<BN, LIMBS>, z: BNFp<BN, LIMBS>) -> Choice {
        // projective curve equation: Y^2*Z = X^3 + b*Z^3
        (y.sq()*z).ct_eq(&(x.cb() + BNFp::from_word(BN::CURVE_B) * z.cb()))
    }

    /// Create a normalized point on a BN curve <i>E/<b>F</b><sub>p</sub>: Y&sup2;Z = X&sup3; + bZ&sup3;</i>
    /// from given affine coordinates <i>x</i> and <i>y</i>.
    #[inline]
    fn from_affine(x: BNFp<BN, LIMBS>, y: BNFp<BN, LIMBS>) -> Self {
        assert!(bool::from(Self::is_point(x, y, BNFp::one())));
        Self { x, y, z: BNFp::one() }
    }

    /// Create a point on a BN curve <i>E/<b>F</b><sub>p</sub>: Y&sup2;Z = X&sup3; + bZ&sup3;</i>
    /// from given projective coordinates <i>X</i>, <i>Y</i>, and <i>Z</i>.
    #[inline]
    pub(crate) fn from_proj(x: BNFp<BN, LIMBS>, y: BNFp<BN, LIMBS>, z: BNFp<BN, LIMBS>) -> Self {
        // projective curve equation: Y^2*Z = X^3 + b*Z^3
        assert!(bool::from(Self::is_point(x, y, z)));
        Self { x, y, z }
    }

    /// Create an instance of the default generator of <i>n</i>-torsion <i>G&#x2081; := (-1, 1)</i>
    /// on a BN curve <i>E/<b>F</b><sub>p</sub>: Y&sup2;Z = X&sup3; + bZ&sup3;</i>.
    #[inline]
    pub fn default_generator() -> Self {
        Self::new(-BNFp::one(), Choice::from(1))
    }

    /// Hash input data into a point on the (base field) <i>n</i>-torsion group
    /// <i><b>G</b>&#x2081;</i> &#x2254; <i>E</i>&lbrack;<i>n</i>&rbrack;(<b>F</b><sub><i>p</i></sub>)
    /// of a BLS24 curve <i>E</i>/<b>F</b><sub><i>p</i></sub>:
    /// <i>Y&sup2;Z</i> = <i>X&sup3;</i> + <i>bZ&sup3;</i> with SHAKE-128.
    #[inline]
    pub fn shake128(data: &[u8]) -> Self {
        Self::point_factory(BNFp::shake128(data))
    }

    /// Hash input data into a point on the (base field) <i>n</i>-torsion group
    /// <i><b>G</b>&#x2081;</i> &#x2254; <i>E</i>&lbrack;<i>n</i>&rbrack;(<b>F</b><sub><i>p</i></sub>)
    /// of a BLS24 curve <i>E</i>/<b>F</b><sub><i>p</i></sub>:
    /// <i>Y&sup2;Z</i> = <i>X&sup3;</i> + <i>bZ&sup3;</i> with SHAKE-256.
    #[inline]
    pub fn shake256(data: &[u8]) -> Self {
        Self::point_factory(BNFp::shake256(data))
    }

    /// Compute a normalized (i.e. affine) point equivalent to this
    /// on a BN curve <i>E/<b>F</b><sub>p</sub>: Y&sup2;Z = X&sup3; + bZ&sup3;</i>.
    #[inline]
    pub(crate) fn normalize(&self) -> Self {
        let ch = self.z.is_zero();
        let inv = BNFp::conditional_select(&self.z, &self.y, ch).inv();
        Self {
            x: self.x*inv,
            y: self.y*inv,
            z: BNFp::conditional_select(&BNFp::one(), &BNFp::zero(), ch),
        }
    }

    /// Compute <i>&lbrack;2&#x1D57;&rbrack;P</i> for a BN curve point
    /// <i>P &in; E/<b>F</b><sub>p</sub>: Y&sup2;Z = X&sup3; + bZ&sup3;</i>
    /// (i.e. double <i>t</i> times) via complete elliptic point doubling.
    #[inline]
    pub fn double(&self, t: usize) -> Self {
        let mut d = self.clone();
        d.double_self(t);
        d
    }

    /// Compute <i>&lbrack;2&#x1D57;&rbrack;P</i> for a BN curve point
    /// <i>P &in; E/<b>F</b><sub>p</sub>: Y&sup2;Z = X&sup3; + bZ&sup3;</i>
    /// (i.e. double <i>t</i> times) via complete elliptic point doubling.
    ///
    /// Reference:
    ///
    /// *; Joost Renes, Craig Costello, Lejla Batina:
    /// <a href="https://link.springer.com/content/pdf/10.1007/978-3-662-49890-3_16">
    /// "Complete addition formulas for prime order elliptic curves"</a>
    /// (Algorithm 9), Eurocrypt 2016, LNCS 9665 (part I), pp. 403--428, Springer, 2016.
    #[inline]
    pub(crate) fn double_self(&mut self, t: usize) {
        let mut x = self.x;
        let mut y = self.y;
        let mut z = self.z;

        let mut t0: BNFp<BN, LIMBS>;
        let mut t1: BNFp<BN, LIMBS>;
        let mut t2: BNFp<BN, LIMBS>;
        let mut x3: BNFp<BN, LIMBS>;
        let mut y3: BNFp<BN, LIMBS>;
        let mut z3: BNFp<BN, LIMBS>;

        for _ in 0..t {
            t0 = y.sq();
            z3 = t0+t0;
            z3 = z3+z3;

            z3 = z3+z3;
            t1 = y*z;
            t2 = z*z;

            t2 = (3*BN::CURVE_B)*t2;
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

    /// Map a field element <i>t &in; <b>F</b><sub>p</sub></i> to a point on this BN curve
    /// using the isochronous Shallue-van de Woestijne method.
    ///
    /// Reference:
    ///
    /// *; Andrew Shallue, Christiaan E. van de Woestijne:
    /// "Construction of rational points on elliptic curves over finite fields."
    /// In: Hess, F., Pauli, S., Pohst, M. E. (eds.), <i>Algorithmic Number Theory -- ANTS-VII</i>,
    /// Lecture Notes in Computer Science, vol. 4076, pp. 510--524, 2006.
    /// Springer, Berlin Heidelberg, 2006.
    /// https://doi.org/10.1007/11792086_36
    #[inline]
    pub fn point_factory(t: BNFp<BN, LIMBS>) -> BNPoint<BN, LIMBS> {
        let one = BNFp::one();
        let b = BNFp::from_word(BN::CURVE_B);
        let sqrt_m3 = BNFp::from_words(BN::SQRT_NEG_3.try_into().unwrap());
        let num = sqrt_m3*t;  // sqrt(-3)*t
        let den = one + b + t.sq();  // 1 + b + t^2
        // Montgomery's trick to use a single inversion, (num*den)^-1, to compute
        // the inverse of num = den*(num*den)^-1 and the inverse of den = num*(num*den)^-1:
        let monty = (num*den).inv();

        let w = num.sq()*monty;  // sqrt(-3)*t/(1 + b + t^2)
        let inv_w = den.sq()*monty;
        let svdw = BNFp::from_words(BN::SVDW.try_into().unwrap());  // (-1 + sqrt(-3))/2

        // candidate x-coordinates:
        let x0 = svdw - t*w;  // (-1 + sqrt(-3))/2 - t*w
        let x1 = -(one + x0); // -1 - x_0
        let x2 = one + inv_w.sq(); // 1 + 1/w^2

        // quadratic characters of the corresponding curve equation RHS:
        let q0 = (x0.cb() + b).legendre();  // legendre((x0^3 + b), p)
        assert_ne!(q0, 0);  // no point of order 2 exists on a curve of (large) prime order
        let q1 = (x1.cb() + b).legendre();  // legendre((x1^3 + b), p)
        assert_ne!(q1, 0);  // no point of order 2 exists on a curve of (large) prime order

        // constant-time sequential search for the proper choice of x:
        let mut xc = x2;
        xc = BNFp::conditional_select(&xc, &x1, q1.ct_eq(&1));
        xc = BNFp::conditional_select(&xc, &x0, q0.ct_eq(&1));
        let leg = t.legendre();

        // point construction:
        BNPoint::new(xc, leg.ct_ne(&0) & leg.ct_ne(&1))
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

impl<BN: BNParam, const LIMBS: usize> Add for BNPoint<BN, LIMBS> {
    type Output = Self;

    /// Complete elliptic point addition
    /// for a BN curve <i>E/<b>F</b><sub>p</sub>: Y&sup2;Z = X&sup3; + bZ&sup3;</i>.
    ///
    /// Reference: Joost Renes, Craig Costello, Lejla Batina:
    /// <a href="https://link.springer.com/content/pdf/10.1007/978-3-662-49890-3_16">
    /// "Complete addition formulas for prime order elliptic curves"</a>
    /// (Algorithm 7), Eurocrypt 2016, LNCS 9665 (part I), pp. 403--428, Springer, 2016.
    fn add(self, other: Self) -> Self::Output {
        let mut point = self;
        point += other;
        point
    }
}

impl<BN: BNParam, const LIMBS: usize> AddAssign for BNPoint<BN, LIMBS> {

    /// Complete elliptic point addition
    /// for a BN curve <i>E/<b>F</b><sub>p</sub>: Y&sup2;Z = X&sup3; + bZ&sup3;</i>.
    ///
    /// Reference: Joost Renes, Craig Costello, Lejla Batina:
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

        let mut t0: BNFp<BN, LIMBS>;
        let mut t1: BNFp<BN, LIMBS>;
        let mut t2: BNFp<BN, LIMBS>;
        let mut t3: BNFp<BN, LIMBS>;
        let mut t4: BNFp<BN, LIMBS>;
        let mut x3: BNFp<BN, LIMBS>;
        let mut y3: BNFp<BN, LIMBS>;
        let mut z3: BNFp<BN, LIMBS>;

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
        t2 = (3*BN::CURVE_B)*t2;

        z3 = t1 + t2;
        t1 = t1 - t2;
        y3 = (3*BN::CURVE_B)*y3;

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

impl<BN: BNParam, const LIMBS: usize> Clone for BNPoint<BN, LIMBS> {
    fn clone(&self) -> Self {
        Self {
            x: self.x.clone(),
            y: self.y.clone(),
            z: self.z.clone(),
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> Copy for BNPoint<BN, LIMBS> {}

impl<BN: BNParam, const LIMBS: usize> ConditionallySelectable for BNPoint<BN, LIMBS> {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        let x = BNFp::conditional_select(&a.x, &b.x, choice);
        let y = BNFp::conditional_select(&a.y, &b.y, choice);
        let z = BNFp::conditional_select(&a.z, &b.z, choice);
        Self { x, y, z }
    }
}

impl<BN: BNParam, const LIMBS: usize> ConstantTimeEq for BNPoint<BN, LIMBS> {
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

impl<BN: BNParam, const LIMBS: usize> Debug for BNPoint<BN, LIMBS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self, f)
    }
}

impl<BN: BNParam, const LIMBS: usize> Display for BNPoint<BN, LIMBS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let normal = self.normalize();
        //*
        // signed format:
        let p: Uint<LIMBS> = Uint::from_words(BN::MODULUS.try_into().unwrap());
        let half_p= p.shr(1);
        let x = if normal.x.to_uint() <= half_p {
            normal.x.to_string()
        } else {
            "-".to_string() + (-normal.x).to_string().as_str()
        };
        let y = if normal.y.to_uint() <= half_p {
            normal.y.to_string()
        } else {
            "-".to_string() + (-normal.y).to_string().as_str()
        };
        let z = if normal.z.to_uint() <= half_p {
            normal.z.to_string()
        } else {
            "-".to_string() + (-normal.z).to_string().as_str()
        };
        // */
        /*
        let x = normal.x.to_string();
        let y = normal.y.to_string();
        let z = normal.z.to_string();
        // */
        write!(f, "[{} : {} : {}]", x, y, z)
    }
}

impl<BN: BNParam, const LIMBS: usize> Mul<BNPoint<BN, LIMBS>> for Uint<LIMBS> {
    type Output = BNPoint<BN, LIMBS>;

    fn mul(self, point: BNPoint<BN, LIMBS>) -> Self::Output {
        let mut v = point;
        v *= self;
        v
    }
}

impl<BN: BNParam, const LIMBS: usize> Mul<BNPoint<BN, LIMBS>> for BNZn<BN, LIMBS> {
    type Output = BNPoint<BN, LIMBS>;

    fn mul(self, point: BNPoint<BN, LIMBS>) -> Self::Output {
        let mut v = point;
        v *= self.to_uint();
        v
    }
}

impl<BN: BNParam, const LIMBS: usize> MulAssign<Uint<LIMBS>> for BNPoint<BN, LIMBS> {

    /// Multiply a scalar (mod n) and a point via fixed-window multiplication.
    ///
    /// Reference:
    ///
    /// *; Alfred J. Menezes, Paul C. van Oorschot, Scott A. Vanstone,
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

impl<BN: BNParam, const LIMBS: usize> Neg for BNPoint<BN, LIMBS> {
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

impl<BN: BNParam, const LIMBS: usize> PartialEq<Self> for BNPoint<BN, LIMBS> {
    fn eq(&self, pair: &Self) -> bool {
        self.ct_eq(&pair).into()
    }

    fn ne(&self, pair: &Self) -> bool {
        self.ct_ne(&pair).into()
    }
}

impl<BN: BNParam, const LIMBS: usize> Random for BNPoint<BN, LIMBS> {
    /// Pick a uniform point from the <i>n</i>-torsion of the BN curve
    /// <i>E/<b>F</b><sub>p</sub>: Y&sup2;Z = X&sup3; + bZ&sup3;</i>.
    fn random<R: Rng + ?Sized>(rng: &mut R) -> Self {
        Self::point_factory(BNFp::random(rng))
    }

    /// Try to pick a uniform point from the <i>n</i>-torsion of the BN curve
    /// <i>E/<b>F</b><sub>p</sub>: Y&sup2;Z = X&sup3; + bZ&sup3;</i>.
    fn try_random<R: TryRngCore + ?Sized>(rng: &mut R) -> Result<Self, <R as TryRngCore>::Error> where R: TryRngCore {
        match BNFp::try_random(rng) {
            Ok(val) => Ok(Self::point_factory(val)),
            Err(e) => Err(e),
        }
    }
}

impl<BN: BNParam, const LIMBS: usize> Sub for BNPoint<BN, LIMBS> {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        let mut point = self;
        point -= other;
        point
    }
}

impl<BN: BNParam, const LIMBS: usize> SubAssign for BNPoint<BN, LIMBS> {
    fn sub_assign(&mut self, pair: Self) {
        self.add_assign(pair.neg())
    }
}

impl<BN: BNParam, const LIMBS: usize> Zero for BNPoint<BN, LIMBS> {
    /// Create an instance of the neutral element ("point at infinity") on a BN curve
    /// <i>E/<b>F</b><sub>p</sub>: Y&sup2;Z = X&sup3; + bZ&sup3;</i>
    /// in projective coordinates, hence <i>&lbrack;0 : 1 : 0&rbrack;</i>.
    fn zero() -> Self {
        Self { x: BNFp::zero(), y: BNFp::one(), z: BNFp::zero() }
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
    fn BNPoint_test<BN: BNParam, const LIMBS: usize>() {
        //let mut rng: SmallRng = SmallRng::from_seed([0; 32]);
        let mut rng = rand::rng();
        let n: Uint<LIMBS> = Uint::from_words(BN::ORDER.try_into().unwrap());

        println!();
        println!("Performing {} BN{:03}Point test(s)...", TESTS, 64*LIMBS - 2);
        let now = SystemTime::now();

        // neutral element:
        let O1: BNPoint<BN, LIMBS> = BNPoint::zero();
        //println!("O1 = {} is zero ? {}", O1, bool::from(O1.is_zero()));
        assert!(bool::from(O1.is_zero()));

        // default generator (-1, 1):
        let G1: BNPoint<BN, LIMBS> = BNPoint::new(-BNFp::one(), Choice::from(1));
        //println!("G1 = {}", G1);
        //println!("[n]G1 = {}", n*G1);
        assert!(bool::from((n*G1).is_zero()));

        for _t in 0..TESTS {
            //println!("======== {}", _t);

            // hashing to G_1:
            let P1: BNPoint<BN, LIMBS> = BNPoint::point_factory(BNFp::random(&mut rng));
            //println!("P1 = {}", P1);
            let P2: BNPoint<BN, LIMBS> = BNPoint::point_factory(BNFp::random(&mut rng));
            //println!("P2 = {}", P2);
            let P3: BNPoint<BN, LIMBS> = BNPoint::point_factory(BNFp::random(&mut rng));
            //println!("P3 = {}", P3);

            // point construction:
            assert_eq!(P1, BNPoint::from_proj(P1.x, P1.y, P1.z));
            let P1N = P1.normalize();
            assert_eq!(P1, BNPoint::from_affine(P1N.x, P1N.y));
            assert_eq!(P2, BNPoint::from_proj(P2.x, P2.y, P2.z));
            let P2N = P2.normalize();
            assert_eq!(P2, BNPoint::from_affine(P2N.x, P2N.y));
            assert_eq!(P3, BNPoint::from_proj(P3.x, P3.y, P3.z));
            let P3N = P3.normalize();
            assert_eq!(P3, BNPoint::from_affine(P3N.x, P3N.y));

            // point order:
            //println!("[n]P1 = O1 ? {}", bool::from((n*P1).is_zero()));
            assert!(bool::from((n*P1).is_zero()));
            //println!("[n]P2 = O1 ? {}", bool::from((n*P2).is_zero()));
            assert!(bool::from((n*P2).is_zero()));
            //println!("[n]P3 = O1 ? {}", bool::from((n*P3).is_zero()));
            assert!(bool::from((n*P3).is_zero()));

            // opposite point:
            //println!("P1 + (-P1) = O1 ? {}", bool::from((P1 + (-P1)).is_zero()));
            assert!(bool::from((P1 + (-P1)).is_zero()));
            //println!("P2 + (-P2) = O1 ? {}", bool::from((P2 + (-P2)).is_zero()));
            assert!(bool::from((P2 + (-P2)).is_zero()));
            //println!("P3 + (-P3) = O1 ? {}", bool::from((P3 + (-P3)).is_zero()));
            assert!(bool::from((P3 + (-P3)).is_zero()));

            // point doubling:
            //println!("[2]P1 = P1 + P1 ? {}", P1.double(1) == P1 + P1);
            assert_eq!(P1.double(1), P1 + P1);
            //println!("[2]P2 = P2 + P2 ? {}", P2.double(1) == P2 + P2);
            assert_eq!(P2.double(1), P2 + P2);
            //println!("[2]P3 = P3 + P3 ? {}", P3.double(1) == P3 + P3);
            assert_eq!(P3.double(1), P3 + P3);

            // commutativity:
            //println!("P1 + P2 = P2 + P1 ? {}", P1 + P2 == P2 + P1);
            assert_eq!(P1 + P2, P2 + P1);
            //println!("P1 + P3 = P3 + P1 ? {}", P1 + P3 == P3 + P1);
            assert_eq!(P1 + P3, P3 + P1);
            //println!("P2 + P3 = P3 + P2 ? {}", P2 + P3 == P3 + P2);
            assert_eq!(P2 + P3, P3 + P2);

            // associativity:
            //println!("(P1 + P2) + P3 = P1 + (P2 + P3) ? {}", (P1 + P2) + P3 == P1 + (P2 + P3));
            assert_eq!((P1 + P2) + P3, P1 + (P2 + P3));
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
    fn BN062Point_test() {
        const LIMBS: usize = BN062Param::LIMBS;
        BNPoint_test::<BN062Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN126Point_test() {
        const LIMBS: usize = BN126Param::LIMBS;
        BNPoint_test::<BN126Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN190Point_test() {
        const LIMBS: usize = BN190Param::LIMBS;
        BNPoint_test::<BN190Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN254Point_test() {
        const LIMBS: usize = BN254Param::LIMBS;
        BNPoint_test::<BN254Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN318Point_test() {
        const LIMBS: usize = BN318Param::LIMBS;
        BNPoint_test::<BN318Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN382Point_test() {
        const LIMBS: usize = BN382Param::LIMBS;
        BNPoint_test::<BN382Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN446Point_test() {
        const LIMBS: usize = BN446Param::LIMBS;
        BNPoint_test::<BN446Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN510Point_test() {
        const LIMBS: usize = BN510Param::LIMBS;
        BNPoint_test::<BN510Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN574Point_test() {
        const LIMBS: usize = BN574Param::LIMBS;
        BNPoint_test::<BN574Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN638Point_test() {
        const LIMBS: usize = BN638Param::LIMBS;
        BNPoint_test::<BN638Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN702Point_test() {
        const LIMBS: usize = BN702Param::LIMBS;
        BNPoint_test::<BN702Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN766Point_test() {
        const LIMBS: usize = BN766Param::LIMBS;
        BNPoint_test::<BN766Param, LIMBS>();
    }

}
