#[cfg(not(any(target_pointer_width = "64")))]
compile_error!("this crate requires 64-bit limbs");

use crate::bnfp::BNFp;
use crate::bnfp2::BNFp2;
use crate::bnfp12::BNFp12;
use crate::bnparam::BNParam;
use crate::bnpoint::BNPoint;
use crate::bnpoint2::BNPoint2;
use crate::traits::{BNField, One};
use crypto_bigint::subtle::{ConditionallySelectable};
use crypto_bigint::{Uint, Zero};
use std::marker::PhantomData;

#[allow(non_snake_case)]
pub struct BNPairing<BN: BNParam, const LIMBS: usize>(
    #[doc(hidden)]
    pub PhantomData<BN>,
);

/*
// the Litany of All Saints:
pub type BN062Pairing = BNPairing<BN062Param, 1>;
pub type BN126Pairing = BNPairing<BN126Param, 2>;
pub type BN190Pairing = BNPairing<BN190Param, 3>;
pub type BN254Pairing = BNPairing<BN254Param, 4>;
pub type BN318Pairing = BNPairing<BN318Param, 5>;
pub type BN382Pairing = BNPairing<BN382Param, 6>;
pub type BN446Pairing = BNPairing<BN446Param, 7>;
pub type BN510Pairing = BNPairing<BN510Param, 8>;
pub type BN574Pairing = BNPairing<BN574Param, 9>;
pub type BN638Pairing = BNPairing<BN638Param, 10>;
pub type BN702Pairing = BNPairing<BN702Param, 11>;
pub type BN766Pairing = BNPairing<BN766Param, 12>;
// */

impl<BN: BNParam, const LIMBS: usize> BNPairing<BN, LIMBS> {

    /// The Tate pairing for BN curves: <i>a<sub>n</sub>(P, Q) = f<sub>n,P</sub>(Q)<sup>(p&#x1D4F;-1)/n</sup></i>
    ///
    /// References:
    ///
    /// *; Victor Miller:
    /// "The Weil Pairing, and Its Efficient Calculation."
    /// Journal of Cryptology, vol. 17, pp. 235--261 (2004).
    /// https://doi.org/10.1007/s00145-004-0315-8
    ///
    /// *; Paulo S. L. M. Barreto, Hae Y. Kim, Ben Lynn, Mike Scott:
    /// "Efficient Algorithms for Pairing-Based Cryptosystems."
    /// In: Yung, M. (eds) Advances in Cryptology — CRYPTO 2002. CRYPTO 2002.
    /// Lecture Notes in Computer Science, vol. 2442, pp. 354–369. Springer, 2002.
    /// https://doi.org/10.1007/3-540-45708-9_23
    ///
    /// *; Craig Costello, Tanja Lange, Michael Naehrig:
    /// "Faster Pairing Computations on Curves with High-Degree Twists."
    /// In: Nguyen, P. Q., Pointcheval, D. (eds), Public Key Cryptography -- PKC 2010.
    /// Lecture Notes in Computer Science, vol. 6056, pp. 224--242. Springer, 2010.
    /// https://doi.org/10.1007/978-3-642-13013-7_14
    ///
    /// *; Mike Scott, Naomi Benger, Manuel Charlemagne, Luís J. Domínguez-Pérez, Ezekiel J. Kachisa:
    ///"On the Final Exponentiation for Calculating Pairings on Ordinary Elliptic Curves."
    /// In: Shacham, H., Waters, B. (eds), Pairing-Based Cryptography -- Pairing 2009.
    /// Lecture Notes in Computer Science, vol. 5671, pp. 78--88. Springer, 2009.
    /// https://doi.org/10.1007/978-3-642-03298-1_6
    #[allow(non_snake_case)]
    #[inline]
    pub fn tate(P: &BNPoint<BN, LIMBS>, Q: &BNPoint2<BN, LIMBS>) -> BNFp12<BN, LIMBS> {
        let QN = Q.normalize();

        /*
        // check that Q = (xQ', yQ') in E'(F_{p^2}) => (xQ'*z^2, yQ'*z^3) in E(F_{p^12}):
        let XQ = BNFp12::from([BNFp2::zero(), BNFp2::zero(), Q.x, BNFp2::zero(), BNFp2::zero(), BNFp2::zero()]);
        let YQ = BNFp12::from([BNFp2::zero(), BNFp2::zero(), BNFp2::zero(), Q.y, BNFp2::zero(), BNFp2::zero()]);
        let ZQ = BNFp12::from_base(Q.z);
        assert_eq!(YQ.sq()*ZQ, XQ.cb() + BN::CURVE_B*ZQ.cb());  // E(F_{p^12}) curve equation
        // */

        let PN = P.normalize();
        let s: Uint<LIMBS> = Uint::from_words(BN::ORDER.try_into().unwrap()) - Uint::ONE;
        let s_bits = (64*LIMBS - 2) as u32;
        assert_eq!(s.bits(), s_bits);
        let mut f: BNFp12<BN, LIMBS> = BNFp12::one();
        let mut X1 = PN.x;
        let mut Y1 = PN.y;
        let mut Z1 = PN.z;

        for j in (0..s_bits-1).rev() {
            // Costello-Lange-Naehrig double-and-line formula:

            let A = X1.sq();
            let B = Y1.sq();
            let C = Z1.sq();
            let D = (3*BN::CURVE_B)*C;  // 3*b*C
            let E = (X1 + Y1).sq() - A - B;
            let F = (Y1 + Z1).sq() - B - C;
            let G = 3u64*D;

            // double the point, U = [2]U:
            X1 = E*(B - G);
            Y1 = (B + G).sq() - (12u64*D.sq());
            Z1 = 4u64*B*F;

            // "untwist" the point Q from E' back to E to evaluate the line function
            // g_{DBL,U}(Q) = 3*X1^2*xQ - 2*Y1*Z1*yQ + 3b*Z1^2 - Y1^2:
            let L_10 = 3u64*A;  // 3*X1^2
            let L_01 = -F;  // -2*Y1*Z1
            let L_00 = D - B;  // 3b*Z1^2 - Y1^2
            f = f.sq().mul_023(BNFp2::from_base(L_00), L_10* QN.x, L_01* QN.y);  // accumulate line into running pairing value

            if bool::from(s.bit(j)) {
                // Costello-Lange-Naehrig add-and-line formula:

                // "untwist" the point Q from E' back to E to evaluate the line function
                // g_{ADD,U+P}(Q) = (Y1*Z2 - Z1*Y2)*(X2 - xP) - (X1*Z2 - Z1*X2)*Y2 + (X1*Z2 - Z1*X2)*yP:
                let A = X1* PN.z - Z1* PN.x;
                let B = Y1* PN.z - Z1* PN.y;
                let L_10 = -B;
                let L_01 = A;
                let L_00 = B* PN.x - A* PN.y;
                f = f.mul_023(BNFp2::from_base(L_00), L_10* QN.x, L_01* QN.y);  // accumulate line into running pairing value

                if j > 0 {
                    // add points U = U + Q (skip this when the pairing calculation is complete):
                    let mut C = A.sq();
                    X1 *= C;
                    C *= A;
                    let D = B.sq()*Z1 + C - X1 - X1;
                    Y1 = B*(X1 - D) - Y1*C;
                    X1 = A*D;
                    Z1 *= C;
                }
            }
        }
        f = f.final_exp();  // f = f^((p^12 - 1)/n)
        f = BNFp12::conditional_select(&f, &BNFp12::one(), f.is_zero());
        assert!(bool::from(f.pow_n().is_one()));
        f
    }

    /// The Ate pairing for BN curves: <i>a<sub>n</sub>(Q, P) = f<sub>n,Q</sub>(P)<sup>(p&#x1D4F;-1)/n</sup></i>
    ///
    /// Reference:
    ///
    /// *; Hess, F., Smart, N., Vercauteren, F.:
    /// "The Eta pairing revisited." IACR Cryptology ePrint Archive,
    /// Report 2006/110, (2006) http://eprint.iacr.org/2006/110
    #[allow(non_snake_case)]
    #[inline]
    pub fn ate(Q: &BNPoint2<BN, LIMBS>, P: &BNPoint<BN, LIMBS>) -> BNFp12<BN, LIMBS> {
        let QN = Q.normalize();

        /*
        // check that Q = (xQ', yQ') in E'(F_{p^2}) => (xQ'*z^2, yQ'*z^3) in E(F_{p^12}):
        let XQ = BNFp12::from([BNFp2::zero(), BNFp2::zero(), Q.x, BNFp2::zero(), BNFp2::zero(), BNFp2::zero()]);
        let YQ = BNFp12::from([BNFp2::zero(), BNFp2::zero(), BNFp2::zero(), Q.y, BNFp2::zero(), BNFp2::zero()]);
        let ZQ = BNFp12::from_base(Q.z);
        assert_eq!(YQ.sq()*ZQ, XQ.cb() + BN::CURVE_B*ZQ.cb());  // E(F_{p^12}) curve equation
        // */

        let PN = P.normalize();
        let p: Uint<LIMBS> = Uint::from_words(BN::MODULUS.try_into().unwrap());  // p
        let n: Uint<LIMBS> = Uint::from_words(BN::ORDER.try_into().unwrap());  // n
        let mut s: Uint<LIMBS> = Uint::from_words(BN::U.try_into().unwrap());  // u
        s = Uint::<LIMBS>::from_word(6)*s*s;  // s = 6*u^2 = t - 1
        assert_eq!(s + Uint::ONE, p + Uint::ONE - n);
        let s_bits = (32*LIMBS - 1) as u32;
        assert_eq!(s.bits(), s_bits);
        let mut f: BNFp12<BN, LIMBS> = BNFp12::one();
        let mut X1 = QN.x;
        let mut Y1 = QN.y;
        let mut Z1 = QN.z;

        for j in (0..s_bits-1).rev() {
            // Costello-Lange-Naehrig double-and-line formula:

            let A = X1.sq();
            let B = Y1.sq();
            let C = Z1.sq();
            let D = (3*BN::CURVE_B)*C.div_xi();  // 3*b'*C
            let E = (X1 + Y1).sq() - A - B;
            let F = (Y1 + Z1).sq() - B - C;
            let G = 3*D;

            // double the point, U = [2]U:
            X1 = E*(B - G);
            Y1 = (B + G).sq() - (12*D.sq());
            Z1 = 4*B*F;

            /*
            // check that U = (xU', yU') in E'(F_{p^2}) => (xU'*z^2, yU'*z^3) in E(F_{p^12}):
            let XU = BNFp12::from([BNFp2::zero(), BNFp2::zero(), X1, BNFp2::zero(), BNFp2::zero(), BNFp2::zero()]);
            let YU = BNFp12::from([BNFp2::zero(), BNFp2::zero(), BNFp2::zero(), Y1, BNFp2::zero(), BNFp2::zero()]);
            let ZU = BNFp12::from_base(Z1);
            assert_eq!(YU.sq()*ZU, XU.cb() + BN::CURVE_B*ZU.cb());  // E(F_{p^12}) curve equation
            // */

            // "untwist" the point [X1 : Y1 : Z1] from E' back to E to evaluate the line function.
            // g_{DBL,U}(P) = 3*X1^2*xP - 2*Y1*Z1*yP + 3b*Z1^2 - Y1^2
            // = yP*(-2*Y1'*Z1') + xP*(3*X1'^2)*z + (3b*Z1'^2 - Y1'^2)*z^3
            let L_10 = 3*A;  // 3*X1'^2
            let L_01 = -F;  // -2*Y1'*Z1'
            let L_00 = D - B;  // 3b*Z1'^2 - Y1'^2
            f = f.sq().mul_013(PN.y*L_01, PN.x*L_10, L_00);  // accumulate line into running pairing value

            if bool::from(s.bit(j)) {
                // Costello-Lange-Naehrig add-and-line formula:

                /*
                // check that U = (xU', yU') in E'(F_{p^2}) => (xU'*z^2, yU'*z^3) in E(F_{p^12}):
                let XU = BNFp12::from([BNFp2::zero(), BNFp2::zero(), X1, BNFp2::zero(), BNFp2::zero(), BNFp2::zero()]);
                let YU = BNFp12::from([BNFp2::zero(), BNFp2::zero(), BNFp2::zero(), Y1, BNFp2::zero(), BNFp2::zero()]);
                let ZU = BNFp12::from_base(Z1);
                assert_eq!(YU.sq()*ZU, XU.cb() + BN::CURVE_B*ZU.cb());  // E(F_{p^12}) curve equation
                // */

                // "untwist" the points [Xj : Yj : Zj] from E' back to E to evaluate the line function.
                // g_{ADD,U+Q}(P) = (Y1*Z2 - Z1*Y2)*(X2 - xP) - (X1*Z2 - Z1*X2)*Y2 + (X1*Z2 - Z1*X2)*yP
                // = A*yP - B*xP*z + (B*X2' - A*Y2')*z^3
                // = yP*L_01 + xP*L_10*z + L_00*z^3
                let A = X1* QN.z - Z1* QN.x;
                let B = Y1* QN.z - Z1* QN.y;
                let L_10 = -B;
                let L_01 = A;
                let L_00 = B* QN.x - A* QN.y;
                f = f.mul_013(PN.y*L_01, PN.x*L_10, L_00);  // accumulate line into running pairing value

                if j > 0 {
                    // add points U = U + Q (skip this when the pairing calculation is complete):
                    let mut C = A.sq();
                    X1 *= C;
                    C *= A;
                    let D = B.sq() * Z1 + C - 2 * X1;
                    Y1 = B * (X1 - D) - Y1 * C;
                    X1 = A * D;
                    Z1 *= C;
                }
            }
        }
        // now T = [t - 1]Q and f = f_{t - 1,Q}
        f = f.final_exp();  // f = f^((p^12 - 1)/n)
        f = BNFp12::conditional_select(&f, &BNFp12::one(), f.is_zero());
        assert!(bool::from(f.pow_n().is_one()));
        f
    }

    /// The Optimal pairing for BN curves:
    /// <i>e<sub>opt</i></sub></i>(<i>P</i>, <i>Q</i>) &#x2254;
    /// <i>f<sub>opt</sub></i><sup>(<i>p&sup1;&#xFEFF;&sup2; - 1</i>)/<i>n</i></sup>  &nbsp;where<br>
    /// <i>f<sub>opt</sub></i> &#x2254;
    /// <i>f<sub>6u+2,Q</sub></i>(<i>P</i>)&times;<i>&ell;<sub>Q3,-Q2</sub></i>(<i>P</i>)&times;&ell;<i><sub>-Q2+Q3,Q1</sub></i>(<i>P</i>)&times;&ell;<i><sub>Q1-Q2+Q3,&lbrack;6u+2&rbrack;Q</sub></i>(<i>P</i>).
    ///
    /// This is typically substantially faster that the Tate or Ate pairing,
    /// and should be preferred for actual use in most applications.
    ///
    /// References:
    ///
    /// * Frederik Vercauteren: "Optimal pairings."
    /// IEEE Transactions on Information Theory, vol. 56, no. 1, pp. 455--461.
    /// IEEE, 2010. https://doi.org/10.1109/TIT.2009.2034881
    ///
    /// * Craig Costello, Tanja Lange, Michael Naehrig:
    /// "Faster Pairing Computations on Curves with High-Degree Twists."
    /// In: Nguyen, P. Q., Pointcheval, D. (eds), Public Key Cryptography -- PKC 2010.
    /// Lecture Notes in Computer Science, vol. 6056, pp. 224--242. Springer, 2010.
    /// https://doi.org/10.1007/978-3-642-13013-7_14
    ///
    /// * Mike Scott, Naomi Benger, Manuel Charlemagne, Luís J. Domínguez-Pérez, Ezekiel J. Kachisa:
    ///"On the Final Exponentiation for Calculating Pairings on Ordinary Elliptic Curves."
    /// In: Shacham, H., Waters, B. (eds), Pairing-Based Cryptography -- Pairing 2009.
    /// Lecture Notes in Computer Science, vol. 5671, pp. 78--88. Springer, 2009.
    /// https://doi.org/10.1007/978-3-642-03298-1_6
    #[allow(non_snake_case)]
    #[inline]
    pub fn opt(Q: &BNPoint2<BN, LIMBS>, P: &BNPoint<BN, LIMBS>) -> BNFp12<BN, LIMBS> {
        let QN = Q.normalize();
        let PN = P.normalize();
        let omega: Uint<LIMBS> = Uint::from_words(BN::OMEGA.try_into().unwrap());
        let omega_bits = (16*LIMBS + 1) as u32;  // bit length of optimal pairing order |6*u + 2|

        let mut f: BNFp12<BN, LIMBS> = BNFp12::one();
        let mut X1 = QN.x;
        let mut Y1 = QN.y;
        let mut Z1 = QN.z;

        for j in (0..omega_bits-1).rev() {
            //println!("======== {}: {}", j, bool::from(opt_ord.bit(j)) as u8);
            // Costello-Lange-Naehrig double-and-line formula:
            let A = X1.sq();
            let B = Y1.sq();
            let C = Z1.sq();
            let D = (3*BN::CURVE_B)*C.div_xi();  // 3*b'*C
            let E = (X1 + Y1).sq() - A - B;
            let F = (Y1 + Z1).sq() - B - C;
            let G = 3*D;
            // double the point, U = [2]U:
            X1 = E*(B - G);
            Y1 = (B + G).sq() - (12*D.sq());
            Z1 = 4*B*F;

            /*
            // check that U = (xU', yU') in E'(F_{p^2}) => (xU'*z^2, yU'*z^3) in E(F_{p^12}):
            let XU = BNFp12::from([BNFp2::zero(), BNFp2::zero(), X1, BNFp2::zero(), BNFp2::zero(), BNFp2::zero()]);
            let YU = BNFp12::from([BNFp2::zero(), BNFp2::zero(), BNFp2::zero(), Y1, BNFp2::zero(), BNFp2::zero()]);
            let ZU = BNFp12::from_base(Z1);
            assert_eq!(YU.sq()*ZU, XU.cb() + BN::CURVE_B*ZU.cb());  // E(F_{p^12}) curve equation
            // */

            // "untwist" the point [X1 : Y1 : Z1] from E' back to E to evaluate the line function.
            // g_{DBL,U}(P) = 3*X1^2*xP - 2*Y1*Z1*yP + 3b*Z1^2 - Y1^2
            // = yP*(-2*Y1'*Z1') + xP*(3*X1'^2)*z + (3b*Z1'^2 - Y1'^2)*z^3
            let L_10 = 3*A;  // 3*X1'^2
            let L_01 = -F;  // -2*Y1'*Z1'
            let L_00 = D - B;  // 3b*Z1'^2 - Y1'^2
            //println!("L_00 = {}, L_10 = {}, L_01 = {}", L_00, L_10, L_01);
            f = f.sq().mul_013(PN.y*L_01, PN.x*L_10, L_00);  // accumulate line into running pairing value
            //println!("f = {}", f);

            if bool::from(omega.bit(j)) {
                // Costello-Lange-Naehrig add-and-line formula:

                /*
                // check that U = (xU', yU') in E'(F_{p^2}) => (xU'*z^2, yU'*z^3) in E(F_{p^12}):
                let XU = BNFp12::from([BNFp2::zero(), BNFp2::zero(), X1, BNFp2::zero(), BNFp2::zero(), BNFp2::zero()]);
                let YU = BNFp12::from([BNFp2::zero(), BNFp2::zero(), BNFp2::zero(), Y1, BNFp2::zero(), BNFp2::zero()]);
                let ZU = BNFp12::from_base(Z1);
                assert_eq!(YU.sq()*ZU, XU.cb() + BN::CURVE_B*ZU.cb());  // E(F_{p^12}) curve equation
                // */

                // "untwist" the points [Xj : Yj : Zj] from E' back to E to evaluate the line function.
                // g_{ADD,U+Q}(P) = (Y1*Z2 - Z1*Y2)*(X2 - xP) - (X1*Z2 - Z1*X2)*Y2 + (X1*Z2 - Z1*X2)*yP
                // = A*yP - B*xP*z + (B*X2' - A*Y2')*z^3
                // = yP*L_01 + xP*L_10*z + L_00*z^3
                let A = X1* QN.z - Z1* QN.x;
                let B = Y1* QN.z - Z1* QN.y;
                let L_10 = -B;
                let L_01 = A;
                let L_00 = B* QN.x - A* QN.y;
                //println!("L_00 = {}, L_10 = {}, L_01 = {}", L_00, L_10, L_01);
                f = f.mul_013(PN.y*L_01, PN.x*L_10, L_00);  // accumulate line into running pairing value
                //println!("f = {}", f);

                if j > 0 {
                    // add points U = U + Q (skip this when the pairing calculation is complete):
                    let mut C = A.sq();
                    X1 *= C;
                    C *= A;
                    let D = B.sq() * Z1 + C - 2 * X1;
                    Y1 = B * (X1 - D) - Y1 * C;
                    X1 = A * D;
                    Z1 *= C;
                }
            }
        }
        // now T = [|6u+2|]Q and f = f_{|6u+2|,Q}
        f = f.conj2(3);  // Aranha's trick: replace inversion by conjugation to get f = f_{6u+2,Q}.
        //let T = BNPoint2::from_proj(X1, -Y1, Z1);
        // now T = [6u+2]Q and f = f_{6u+2,Q} (since u < 0 by choice)

        let Q1 = QN.psi(1);
        let Q2 = QN.psi(2);
        let Q3 = QN.psi(3);

        // [X1 : Y1 : Z1] = -Q2:
        X1 = Q2.x;
        Y1 = -Q2.y;
        Z1 = Q2.z;
        assert!(bool::from(BNPoint2::is_point(X1, Y1, Z1)));

        // Costello-Lange-Naehrig add-and-line formula:

        // "untwist" the points [Xj : Yj : Zj] from E' back to E to evaluate the line function.
        // g_{ADD,-Q2,Q3}(P) = (Y1*Z2 - Z1*Y2)*(X2 - xP) - (X1*Z2 - Z1*X2)*Y2 + (X1*Z2 - Z1*X2)*yP
        // = A*yP - B*xP*z + (B*X2' - A*Y2')*z^3
        // = yP*L_01 + xP*L_10*z + L_00*z^3
        let A = X1*Q3.z - Z1*Q3.x;
        let B = Y1*Q3.z - Z1*Q3.y;
        let L_10 = -B;
        let L_01 = A;
        let L_00 = B*Q3.x - A*Q3.y;
        f = f.mul_013(PN.y*L_01, PN.x*L_10, L_00);  // accumulate line into running pairing value

        // add points U = -Q2 + Q3:
        let mut C = A.sq();
        X1 *= C;
        C *= A;
        let D = B.sq()*Z1 + C - 2*X1;
        Y1 = B*(X1 - D) - Y1*C;
        X1 = A*D;
        Z1 *= C;
        //println!("-Q2 + Q3  = {}", -Q2 + Q3);
        //println!("-Q2 + Q3  ? {}", BNPoint2::from_proj(X1, Y1, Z1));
        assert!(bool::from(BNPoint2::is_point(X1, Y1, Z1)));
        assert_eq!(BNPoint2::from_proj(X1, Y1, Z1), -Q2 + Q3);

        // "untwist" the points [Xj : Yj : Zj] from E' back to E to evaluate the line function.
        // g_{ADD,-Q2+Q3,Q1}(P) = (Y1*Z2 - Z1*Y2)*(X2 - xP) - (X1*Z2 - Z1*X2)*Y2 + (X1*Z2 - Z1*X2)*yP
        // = A*yP - B*xP*z + (B*X2' - A*Y2')*z^3
        // = yP*L_01 + xP*L_10*z + L_00*z^3
        let A = X1*Q1.z - Z1*Q1.x;
        let B = Y1*Q1.z - Z1*Q1.y;
        let L_10 = -B;
        let L_01 = A;
        let L_00 = B*Q1.x - A*Q1.y;
        f = f.mul_013(PN.y*L_01, PN.x*L_10, L_00);  // accumulate line into running pairing value

        // NB: the third line involved in the optimal pairing calculation intersects
        // the point at infinity and hence only contributes a value in a proper subfield,
        // which is promptly erased by the final exponentiation and can thus be omitted.

        f = f.final_exp();  // f = f^((p^12 - 1)/n)
        f = BNFp12::conditional_select(&f, &BNFp12::one(), f.is_zero());
        f
    }

    /// Creates a list of precomputed triples of <b>F</b><sub><i>p&sup2;</i></sub> elements from
    /// a point `Q` &in; <b>G</b><i>&#x2082;</i>, to be used later by BNPairing::eval(.)
    /// when `Q` is involved in several optimal pairing computations with different
    /// arguments from group <b>G</b><i>&#x2081;</i>.
    ///
    /// Example:
    ///
    /// &nbsp;&nbsp;&nbsp;&nbsp;let triples = BNPairing::precomp(&Q);<br>
    /// &nbsp;&nbsp;&nbsp;&nbsp;let g_1 = BNPairing::eval(&P_1, &triples);  // e(P_1, Q)<br>
    /// &nbsp;&nbsp;&nbsp;&nbsp;// ...<br>
    /// &nbsp;&nbsp;&nbsp;&nbsp;let g_m = BNPairing::eval(&P_m, &triples);  // e(P_m, Q)<br>
    #[allow(non_snake_case)]
    #[inline]
    pub fn precomp(Q: &BNPoint2<BN, LIMBS>) -> Vec<BNFp2<BN, LIMBS>> {
        let mut Q_triples = Vec::<BNFp2<BN, LIMBS>>::with_capacity(3*BN::TRIPLES as usize);
        let QN = Q.normalize();
        let omega: Uint<LIMBS> = Uint::from_words(BN::OMEGA.try_into().unwrap());
        let omega_bits = (16*LIMBS + 1) as u32;  // bit length of optimal pairing order |6*u + 2|

        let mut X1 = QN.x;
        let mut Y1 = QN.y;
        let mut Z1 = QN.z;

        for j in (0..omega_bits-1).rev() {
            // Costello-Lange-Naehrig double-and-line formula:
            let A = X1.sq();
            let B = Y1.sq();
            let C = Z1.sq();
            let D = (3*BN::CURVE_B)*C.div_xi();  // 3*b'*C
            let E = (X1 + Y1).sq() - A - B;
            let F = (Y1 + Z1).sq() - B - C;
            let G = 3*D;
            // double the point, U = [2]U:
            X1 = E*(B - G);
            Y1 = (B + G).sq() - (12*D.sq());
            Z1 = 4*B*F;
            // "untwist" the point [X1 : Y1 : Z1] from E' back to E to evaluate the line function.
            // g_{DBL,U}(P) = 3*X1^2*xP - 2*Y1*Z1*yP + 3b*Z1^2 - Y1^2
            // = yP*(-2*Y1'*Z1') + xP*(3*X1'^2)*z + (3b*Z1'^2 - Y1'^2)*z^3
            let L_10 = 3*A;  // 3*X1'^2
            let L_01 = -F;  // -2*Y1'*Z1'
            let L_00 = D - B;  // 3b*Z1'^2 - Y1'^2
            //println!("L_00 = {}, L_10 = {}, L_01 = {}", L_00, L_10, L_01);
            Q_triples.push(L_00);
            Q_triples.push(L_10);
            Q_triples.push(L_01);

            if bool::from(omega.bit(j)) {
                // Costello-Lange-Naehrig add-and-line formula:
                // "untwist" the points [Xj : Yj : Zj] from E' back to E to evaluate the line function.
                // g_{ADD,U+Q}(P) = (Y1*Z2 - Z1*Y2)*(X2 - xP) - (X1*Z2 - Z1*X2)*Y2 + (X1*Z2 - Z1*X2)*yP
                // = A*yP - B*xP*z + (B*X2' - A*Y2')*z^3
                // = yP*L_01 + xP*L_10*z + L_00*z^3
                let A = X1* QN.z - Z1* QN.x;
                let B = Y1* QN.z - Z1* QN.y;
                let L_10 = -B;
                let L_01 = A;
                let L_00 = B* QN.x - A* QN.y;
                //println!("L_00 = {}, L_10 = {}, L_01 = {}", L_00, L_10, L_01);
                Q_triples.push(L_00);
                Q_triples.push(L_10);
                Q_triples.push(L_01);
                if j > 0 {
                    // add points U = U + Q (skip this when the pairing calculation is complete):
                    let mut C = A.sq();
                    X1 *= C;
                    C *= A;
                    let D = B.sq() * Z1 + C - 2 * X1;
                    Y1 = B * (X1 - D) - Y1 * C;
                    X1 = A * D;
                    Z1 *= C;
                }
            }
        }
        // now T = [|6u+2|]Q and f = f_{|6u+2|,Q}
        // let T = BNPoint2::from_proj(X1, -Y1, Z1);
        // now T = [6u+2]Q and f = f_{6u+2,Q} (since u < 0 by choice)

        let Q1 = QN.psi(1);
        let Q2 = QN.psi(2);
        let Q3 = QN.psi(3);
        // [X1 : Y1 : Z1] = -Q2:
        X1 = Q2.x;
        Y1 = -Q2.y;
        Z1 = Q2.z;
        assert!(bool::from(BNPoint2::is_point(X1, Y1, Z1)));

        // Costello-Lange-Naehrig add-and-line formula:
        // "untwist" the points [Xj : Yj : Zj] from E' back to E to evaluate the line function.
        // g_{ADD,-Q2,Q3}(P) = (Y1*Z2 - Z1*Y2)*(X2 - xP) - (X1*Z2 - Z1*X2)*Y2 + (X1*Z2 - Z1*X2)*yP
        // = A*yP - B*xP*z + (B*X2' - A*Y2')*z^3
        // = yP*L_01 + xP*L_10*z + L_00*z^3
        let A = X1*Q3.z - Z1*Q3.x;
        let B = Y1*Q3.z - Z1*Q3.y;
        let L_10 = -B;
        let L_01 = A;
        let L_00 = B*Q3.x - A*Q3.y;
        Q_triples.push(L_00);
        Q_triples.push(L_10);
        Q_triples.push(L_01);
        // add points U = -Q2 + Q3:
        let mut C = A.sq();
        X1 *= C;
        C *= A;
        let D = B.sq()*Z1 + C - 2*X1;
        Y1 = B*(X1 - D) - Y1*C;
        X1 = A*D;
        Z1 *= C;
        // "untwist" the points [Xj : Yj : Zj] from E' back to E to evaluate the line function.
        // g_{ADD,-Q2+Q3,Q1}(P) = (Y1*Z2 - Z1*Y2)*(X2 - xP) - (X1*Z2 - Z1*X2)*Y2 + (X1*Z2 - Z1*X2)*yP
        // = A*yP - B*xP*z + (B*X2' - A*Y2')*z^3
        // = yP*L_01 + xP*L_10*z + L_00*z^3
        let A = X1*Q1.z - Z1*Q1.x;
        let B = Y1*Q1.z - Z1*Q1.y;
        let L_10 = -B;
        let L_01 = A;
        let L_00 = B*Q1.x - A*Q1.y;
        Q_triples.push(L_00);
        Q_triples.push(L_10);
        Q_triples.push(L_01);

        // NB: the third line involved in the optimal pairing calculation intersects
        // the point at infinity and hence only contributes a value in a proper subfield,
        // which is promptly erased by the final exponentiation and can thus be omitted.
        assert_eq!(Q_triples.len(), 3*BN::TRIPLES as usize);
        Q_triples
    }

    /// Evaluates an optimal pairing in expedited fashion, from a point `P` &in; <b>G</b><i>&#x2081;</i>
    /// and a list of precomputed `triples` of <b>F</b><sub><i>p&sup2;</i></sub> elements previously
    /// computed with BNPairing::precomp(.) from a common point <i>Q</i> &in; <b>G</b><i>&#x2082;</i>.
    ///
    /// Example:
    ///
    /// &nbsp;&nbsp;&nbsp;&nbsp;let Q_triples = BNPairing::precomp(&Q);<br>
    /// &nbsp;&nbsp;&nbsp;&nbsp;let g_1 = BNPairing::eval(&Q_triples, &P_1);  // = e_opt(Q, P_1)<br>
    /// &nbsp;&nbsp;&nbsp;&nbsp;// ...<br>
    /// &nbsp;&nbsp;&nbsp;&nbsp;let g_m = BNPairing::eval(&Q_triples, &P_m);  // = e_opt(Q, P_m)<br>
    #[allow(non_snake_case)]
    #[inline]
    pub fn eval(Q_triples: &Vec<BNFp2<BN, LIMBS>>, P: &BNPoint<BN, LIMBS>) -> BNFp12<BN, LIMBS> {
        assert_eq!(Q_triples.len(), 3*BN::TRIPLES as usize);
        let PN = P.normalize();
        let mut f: BNFp12<BN, LIMBS> = BNFp12::one();
        let omega: Uint<LIMBS> = Uint::from_words(BN::OMEGA.try_into().unwrap());
        let omega_bits = (16*LIMBS + 1) as u32;  // bit length of optimal pairing order |6*u + 2|
        //let mut triple = [BNFp2::zero(); 3*BN::TRIPLES];  // (L_00, L_10, L_01)
        let mut pre = 0;  // individual precomputed value
        for j in (0..omega_bits-1).rev() {
            let L_00 = Q_triples[pre]; pre += 1;
            let L_10 = Q_triples[pre]; pre += 1;
            let L_01 = Q_triples[pre]; pre += 1;
            //println!("L_00 = {}, L_10 = {}, L_01 = {}", L_00, L_10, L_01);
            f = f.sq().mul_013(PN.y*L_01, PN.x*L_10, L_00);  // accumulate line into running pairing value
            //println!("f = {}", f);
            if bool::from(omega.bit(j)) {
                let L_00 = Q_triples[pre]; pre += 1;
                let L_10 = Q_triples[pre]; pre += 1;
                let L_01 = Q_triples[pre]; pre += 1;
                //println!("L_00 = {}, L_10 = {}, L_01 = {}", L_00, L_10, L_01);
                f = f.mul_013(PN.y*L_01, PN.x*L_10, L_00);  // accumulate line into running pairing value
                //println!("f = {}", f);
            }
        }
        f = f.conj2(3);  // Aranha's trick: replace inversion by conjugation to get f = f_{6u+2,Q}.
        //println!("f = {}", f);
        let L_00 = Q_triples[pre]; pre += 1;
        let L_10 = Q_triples[pre]; pre += 1;
        let L_01 = Q_triples[pre]; pre += 1;
        //println!("L_00 = {}, L_10 = {}, L_01 = {}", L_00, L_10, L_01);
        f = f.mul_013(PN.y*L_01, PN.x*L_10, L_00);  // accumulate line into running pairing value
        //println!("f = {}", f);
        let L_00 = Q_triples[pre]; pre += 1;
        let L_10 = Q_triples[pre]; pre += 1;
        let L_01 = Q_triples[pre]; pre += 1;
        //println!("L_00 = {}, L_10 = {}, L_01 = {}", L_00, L_10, L_01);
        f = f.mul_013(PN.y*L_01, PN.x*L_10, L_00);  // accumulate line into running pairing value
        //println!("f = {}", f);
        assert_eq!(pre, 3*BN::TRIPLES as usize);
        f = f.final_exp();  // f = f^((p^12 - 1)/n)
        f = BNFp12::conditional_select(&f, &BNFp12::one(), f.is_zero());
        f
    }
}


#[cfg(test)]
mod tests {
    use crate::bnparam::{BN062Param, BN126Param, BN190Param, BN254Param, BN318Param, BN382Param, BN446Param, BN510Param, BN574Param, BN638Param, BN702Param, BN766Param};
    use crypto_bigint::Random;
    use std::time::SystemTime;
    use super::*;

    const TESTS: usize = 1;

    /// General BNPairing test template.
    #[allow(non_snake_case)]
    fn BNPairing_test<BN: BNParam, const LIMBS: usize>() {
        //let mut rng: SmallRng = SmallRng::from_seed([0; 32]);
        let mut rng = rand::rng();
        let n: Uint<LIMBS> = Uint::from_words(BN::ORDER.try_into().unwrap());
        println!();
        println!("Performing {} BN{:03}Pairing test(s)...", TESTS, 64*LIMBS - 2);
        let now = SystemTime::now();

        // default generators:
        let O1: BNPoint<BN, LIMBS> = BNPoint::zero();
        let G1: BNPoint<BN, LIMBS> = BNPoint::default_generator();
        //println!("**** G1 = {}", G1);
        assert!(bool::from(!G1.is_zero() & (n*G1).is_zero()));
        let O2: BNPoint2<BN, LIMBS> = BNPoint2::zero();
        let G2: BNPoint2<BN, LIMBS> = BNPoint2::default_generator();
        //println!("**** G2 = {}", G2);
        assert!(bool::from(!G2.is_zero() & (n*G2).is_zero()));

        //println!();
        //println!("    Tate pairing....");

        // default generators and infinity:
        let g1 = BNPairing::tate(&O1, &G2);
        //println!("**** t(O1, G2) = {}", g1);
        assert!(bool::from(g1.is_one()));
        let g2 = BNPairing::tate(&G1, &O2);
        //println!("**** t(G1, O2) = {}", g2);
        assert!(bool::from(g2.is_one()));
        let g0 = BNPairing::tate(&G1, &G2);
        //println!("**** t(G1, G2) = {}", g0);
        //println!("**** t(G1, G2)^n = {}", g0.pow_n());
        assert!(bool::from(!g0.is_one() & g0.pow_n().is_one()));
        for _t in 0..TESTS {
            let k = Uint::random(&mut rng);
            let a = BNPairing::tate(&G1, &(k*G2));
            let b = BNPairing::tate(&(k*G1), &G2);
            let c = g0.pow(&k);
            //println!("eq? {}", a == c && b == c);
            assert!(bool::from(!a.is_one() & a.pow_n().is_one()));
            assert!(bool::from(!b.is_one() & b.pow_n().is_one()));
            assert!(bool::from(!c.is_one() & c.pow_n().is_one()));
            assert_eq!(a, c);
            assert_eq!(b, c);

            let P1: BNPoint<BN, LIMBS> = BNPoint::point_factory(BNFp::random(&mut rng));
            //println!("P1 = {}", P1);
            assert!(bool::from(!P1.is_zero() & (n*P1).is_zero()));
            let P2: BNPoint<BN, LIMBS> = BNPoint::point_factory(BNFp::random(&mut rng));
            //println!("P2 = {}", P2);
            assert!(bool::from(!P2.is_zero() & (n*P2).is_zero()));
            let Q1: BNPoint2<BN, LIMBS> = BNPoint2::point_factory(BNFp2::random(&mut rng)).elim_cof();
            //println!("Q1' = {}", Q1);
            assert!(bool::from(!Q1.is_zero() & (n*Q1).is_zero()));
            let Q2: BNPoint2<BN, LIMBS> = BNPoint2::point_factory(BNFp2::random(&mut rng)).elim_cof();
            //println!("Q2' = {}", Q2);
            assert!(bool::from(!Q2.is_zero() & (n*Q2).is_zero()));

            let g = BNPairing::tate(&P1, &Q1);

            // linearity in the 1st argument:
            let gs = BNPairing::tate(&(P1 + P2), &Q1);
            //println!("**** g = t(P1 + P2, Q1')       = {}", gs);
            assert!(bool::from(!gs.is_one() & gs.pow_n().is_one()));
            let gp = g*BNPairing::tate(&P2, &Q1);
            //println!("**** g ? t(P1, Q1')*t(P2, Q1') = {}", gp);
            //println!("**** match ? {}", gp == gs);
            assert!(bool::from(!gp.is_one() & gp.pow_n().is_one()));
            assert_eq!(gp, gs);

            // linearity in the 2nd argument:
            let gs = BNPairing::tate(&P1, &(Q1 + Q2));
            //println!("**** g = t(P1, Q1' + Q2')      = {}", gs);
            assert!(bool::from(!gs.is_one() & gs.pow_n().is_one()));
            let gp = g*BNPairing::tate(&P1, &Q2);
            //println!("**** g ? t(P1, Q1')*t(P1, Q2') = {}", gp);
            //println!("**** match ? {}", gp == gs);
            assert!(bool::from(!gp.is_one() & gp.pow_n().is_one()));
            assert_eq!(gp, gs);

            let a = BNPairing::tate(&P1, &(k*Q1));
            let b = BNPairing::tate(&(k*P1), &Q1);
            let c = g.pow(&k);
            //println!("eq? {}", a == c && b == c);
            assert!(bool::from(!a.is_one() & a.pow_n().is_one()));
            assert!(bool::from(!b.is_one() & b.pow_n().is_one()));
            assert!(bool::from(!c.is_one() & c.pow_n().is_one()));
            assert!(bool::from(!g.is_one() & g.pow_n().is_one()));
            assert_eq!(a, c);
            assert_eq!(b, c);
        }

        //println!();
        //println!("    Ate pairing...");

        // default generators and infinity:
        let g1 = BNPairing::ate(&G2, &O1);
        //println!("**** a(G2, O1) = {}", g1);
        assert!(bool::from(g1.is_one()));
        let g2 = BNPairing::ate(&O2, &G1);
        //println!("**** a(O2, G1) = {}", g2);
        assert!(bool::from(g2.is_one()));
        let g0 = BNPairing::ate(&G2, &G1);
        //println!("**** a(G2, G1) = {}", g0);
        //println!("**** a(G2, G1)^n = {}", g0.pow_n());
        assert!(bool::from(!g0.is_one() & g0.pow_n().is_one()));
        for _t in 0..TESTS {
            let k = Uint::random(&mut rng);
            let a = BNPairing::ate(&(k*G2), &G1);
            let b = BNPairing::ate(&G2, &(k*G1));
            let c = g0.pow(&k);
            //println!("eq? {}", a == c && b == c);
            assert!(bool::from(!a.is_one() & a.pow_n().is_one()));
            assert!(bool::from(!b.is_one() & b.pow_n().is_one()));
            assert!(bool::from(!c.is_one() & c.pow_n().is_one()));
            assert_eq!(a, c);
            assert_eq!(b, c);

            let P1 = BNPoint::point_factory(BNFp::random(&mut rng));
            //println!("P1 = {}", P1);
            assert!(bool::from(!P1.is_zero() & (n*P1).is_zero()));
            let P2 = BNPoint::point_factory(BNFp::random(&mut rng));
            //println!("P2 = {}", P2);
            assert!(bool::from(!P2.is_zero() & (n*P2).is_zero()));
            let Q1 = BNPoint2::point_factory(BNFp2::random(&mut rng)).elim_cof();
            //println!("Q1' = {}", Q1);
            assert!(bool::from(!Q1.is_zero() & (n*Q1).is_zero()));
            let Q2 = BNPoint2::point_factory(BNFp2::random(&mut rng)).elim_cof();
            //println!("Q2' = {}", Q2);
            assert!(bool::from(!Q2.is_zero() & (n*Q2).is_zero()));

            let g: BNFp12<BN, LIMBS> = BNPairing::ate(&Q1, &P1);

            // linearity in the 1st argument:
            let gs: BNFp12<BN, LIMBS> = BNPairing::ate(&(Q1 + Q2), &P1);
            //println!("**** g = a(Q1' + Q2', P1)      = {}", gs);
            assert!(bool::from(!gs.is_one() & gs.pow_n().is_one()));
            let gp = g*BNPairing::ate(&Q2, &P1);
            //println!("**** g ? a(Q1', P1)*a(Q2', P1) = {}", gp);
            //println!("**** match ? {}", gp == gs);
            assert!(bool::from(!gp.is_one() & gp.pow_n().is_one()));
            assert_eq!(gp, gs);

            // linearity in the 2nd argument:
            let gs: BNFp12<BN, LIMBS> = BNPairing::ate(&Q1, &(P1 + P2));
            //println!("**** g = a(Q1', P1 + P2)       = {}", gs);
            assert!(bool::from(!gs.is_one() & gs.pow_n().is_one()));
            let gp = g*BNPairing::ate(&Q1, &P2);
            //println!("**** g ? a(Q1', P1)*a(Q1', P2) = {}", gp);
            //println!("**** match ? {}", gp == gs);
            assert!(bool::from(!gp.is_one() & gp.pow_n().is_one()));
            assert_eq!(gp, gs);

            let a = BNPairing::ate(&(k*Q1), &P1);
            let b = BNPairing::ate(&Q1, &(k*P1));
            let c = g.pow(&k);
            //println!("eq? {}", a == c && b == c);
            assert!(bool::from(!a.is_one() & a.pow_n().is_one()));
            assert!(bool::from(!b.is_one() & b.pow_n().is_one()));
            assert!(bool::from(!c.is_one() & c.pow_n().is_one()));
            assert!(bool::from(!g.is_one() & g.pow_n().is_one()));
            assert_eq!(a, c);
            assert_eq!(b, c);
        }

        //println!();
        //println!("    Optimal pairing...");

        // default generators and infinity:
        let g1 = BNPairing::opt(&G2, &O1);
        //println!("**** o(G2, O1) = {}", g1);
        assert!(bool::from(g1.is_one()));
        let g2 = BNPairing::opt(&O2, &G1);
        //println!("**** o(O2, G1) = {}", g2);
        assert!(bool::from(g2.is_one()));
        let g0 = BNPairing::opt(&G2, &G1);
        //println!("**** o(G2, G1) = {}", g0);
        //println!("**** o(G2, G1)^n = {}", g0.pow_n());
        assert!(bool::from(!g0.is_one() & g0.pow_n().is_one()));

        // random generators:
        for _t in 0..TESTS {
            let k = Uint::random(&mut rng);
            let a = BNPairing::opt(&(k*G2), &G1);
            let b = BNPairing::opt(&G2, &(k*G1));
            let c = g0.pow(&k);
            //println!("eq? {}", a == c && b == c);
            assert!(bool::from(!a.is_one() & a.pow_n().is_one()));
            assert!(bool::from(!b.is_one() & b.pow_n().is_one()));
            assert!(bool::from(!c.is_one() & c.pow_n().is_one()));
            assert_eq!(a, c);
            assert_eq!(b, c);

            let P1 = BNPoint::point_factory(BNFp::random(&mut rng));
            //println!("P1 = {}", P1);
            assert!(bool::from(!P1.is_zero() & (n*P1).is_zero()));
            let P2 = BNPoint::point_factory(BNFp::random(&mut rng));
            //println!("P2 = {}", P2);
            assert!(bool::from(!P2.is_zero() & (n*P2).is_zero()));
            let Q1 = BNPoint2::point_factory(BNFp2::random(&mut rng)).elim_cof();
            //println!("Q1' = {}", Q1);
            assert!(bool::from(!Q1.is_zero() & (n*Q1).is_zero()));
            let Q2 = BNPoint2::point_factory(BNFp2::random(&mut rng)).elim_cof();
            //println!("Q2' = {}", Q2);
            assert!(bool::from(!Q2.is_zero() & (n*Q2).is_zero()));

            let g: BNFp12<BN, LIMBS> = BNPairing::opt(&Q1, &P1);

            // linearity in the 1st argument:
            let gs = BNPairing::opt(&(Q1 + Q2), &P1);
            //println!("**** g = o(Q1' + Q2', P1)      = {}", gs);
            assert!(bool::from(!gs.is_one() & gs.pow_n().is_one()));
            let gp = g*BNPairing::opt(&Q2, &P1);
            //println!("**** g ? o(Q1', P1)*o(Q2', P1) = {}", gp);
            //println!("**** match ? {}", gp == gs);
            assert!(bool::from(!gp.is_one() & gp.pow_n().is_one()));
            assert_eq!(gp, gs);

            // linearity in the 2nd argument:
            let gs = BNPairing::opt(&Q1, &(P1 + P2));
            //println!("**** g = o(Q1', P1 + P2)       = {}", gs);
            assert!(bool::from(!gs.is_one() & gs.pow_n().is_one()));
            let gp = g*BNPairing::opt(&Q1, &P2);
            //println!("**** g ? o(Q1', P1)*o(Q1', P2) = {}", gp);
            //println!("**** match ? {}", gp == gs);
            assert!(bool::from(!gp.is_one() & gp.pow_n().is_one()));
            assert_eq!(gp, gs);

            let a = BNPairing::opt(&(k*Q1), &P1);
            let b = BNPairing::opt(&Q1, &(k*P1));
            let c = g.pow(&k);
            //println!("eq? {}", a == c && b == c);
            assert!(bool::from(!a.is_one() & a.pow_n().is_one()));
            assert!(bool::from(!b.is_one() & b.pow_n().is_one()));
            assert!(bool::from(!c.is_one() & c.pow_n().is_one()));
            assert!(bool::from(!g.is_one() & g.pow_n().is_one()));
            assert_eq!(a, c);
            assert_eq!(b, c);

            // precomputation:
            let Q1_triples = BNPairing::precomp(&Q1);
            assert_eq!(g, BNPairing::eval(&Q1_triples, &P1));
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
    fn BN62Pairing_test() {
        const LIMBS: usize = BN062Param::LIMBS;
        BNPairing_test::<BN062Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN126Pairing_test() {
        const LIMBS: usize = BN126Param::LIMBS;
        BNPairing_test::<BN126Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN190Pairing_test() {
        const LIMBS: usize = BN190Param::LIMBS;
        BNPairing_test::<BN190Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN254Pairing_test() {
        const LIMBS: usize = BN254Param::LIMBS;
        BNPairing_test::<BN254Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN318Pairing_test() {
        const LIMBS: usize = BN318Param::LIMBS;
        BNPairing_test::<BN318Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN382Pairing_test() {
        const LIMBS: usize = BN382Param::LIMBS;
        BNPairing_test::<BN382Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN446Pairing_test() {
        const LIMBS: usize = BN446Param::LIMBS;
        BNPairing_test::<BN446Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN510Pairing_test() {
        const LIMBS: usize = BN510Param::LIMBS;
        BNPairing_test::<BN510Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN574Pairing_test() {
        const LIMBS: usize = BN574Param::LIMBS;
        BNPairing_test::<BN574Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN638Pairing_test() {
        const LIMBS: usize = BN638Param::LIMBS;
        BNPairing_test::<BN638Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN702Pairing_test() {
        const LIMBS: usize = BN702Param::LIMBS;
        BNPairing_test::<BN702Param, LIMBS>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn BN766Pairing_test() {
        const LIMBS: usize = BN766Param::LIMBS;
        BNPairing_test::<BN766Param, LIMBS>();
    }

}
