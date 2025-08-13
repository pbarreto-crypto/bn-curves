//! An executable tool to prepare the bnparams.rs file needed by the bn-curves crate.

use std::ops::Div;
use crypto_bigint::{Integer, NonZero, Uint, Zero};
use crypto_bigint::subtle::ConditionallySelectable;

const LIMBS: usize = 16;  // maximum supported size (1024 bits)

/// Left-pad a hex string with zeroes to complete the length required
/// to interpret it as spelling out a proper Uint value.
fn from_be_hex(hex: &str) -> Uint<LIMBS> {
    assert_eq!(hex.as_bytes()[0], '-' as u8);  // implementation choice: only negative BN labels
    let padded_hex = "0".repeat((LIMBS << 4) - hex.len() + 1) + hex[1..hex.len()].trim();
    Uint::from_be_hex(padded_hex.as_str())
}

/// Compute <i>r</i> := <i>u&#x02E3;</i> mod <i>p</i>.
fn pow_mod_p(u: Uint<LIMBS>, x: Uint<LIMBS>, p: Uint<LIMBS>) -> Uint<LIMBS> {
    let nzp: NonZero<Uint<LIMBS>> = NonZero::new(p).unwrap();
    // the exponent is presumed fixed and public, hence the square-and-multiply method suffices:
    let mut r = Uint::ONE;
    let w = x.as_words();
    for i in (0..LIMBS << 6).rev() {
        r = r.mul_mod_vartime(&r, &nzp);
        if ((w[i >> 6] >> (i & 63)) & 1) == 1 {
            r = r.mul_mod_vartime(&u, &nzp);
        }
    }
    r
}

/// Compute <i>r</i> = &radic;<i>u</i> = <i>u</i><sup>(<i>q</i> + 1)/4</sup> mod <i>q</i>,
/// which satisfies <i>r&sup2;</i> mod <i>q</i> = <i>u</i>
/// if <i>u</i> is a quadratic residue mod <i>q</i> and <i>q</i> &equiv; 3 (mod 4).
fn sqrt(u: Uint<LIMBS>, p: Uint<LIMBS>) -> Uint<LIMBS> {
    pow_mod_p(u, (p + Uint::ONE).shr(2), p) // sqrt exponent: (p + 1)/4
}

/// Compute the number of '1'-bits (i.e. the Hamming weight) of `u`.
fn popcnt(u: Uint<LIMBS>) -> u32 {
    let w = u.as_words();
    let mut c: u64 = 0;
    for i in 0..w.len() {  // count the number of '1'-bits in 64-bit chunks
        let mut x = w[i];  // 64 lsb
        x -= (x >> 1) & 0x5555555555555555;  // put count of each 2 bits into those 2 bits
        x = (x & 0x3333333333333333) + ((x >> 2) & 0x3333333333333333);  // put count of each 4 bits into those 4 bits
        x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0f;  // put count of each 8 bits into those 8 bits
        x += x >>  8;  // put count of each 16 bits into their lowest 8 bits
        x += x >> 16;  // put count of each 32 bits into their lowest 8 bits
        x += x >> 32;  // put count of each 64 bits into their lowest 8 bits
        c += x & 0x7f;  // 64-bit population count fits 7 bits (NB: *not* 6 bits, since 64 itself is valid)
    }
    assert!(c < 0x100000000);  // must fit 32 bits
    c as u32
}

fn bn() {
    let n1: Uint<LIMBS> = Uint::ONE;
    let n2: Uint<LIMBS> = Uint::from_u64(2);
    let n4: Uint<LIMBS> = Uint::from_u64(4);
    let n5: Uint<LIMBS> = Uint::from_u64(5);
    let n6: Uint<LIMBS> = Uint::from_u64(6);
    let n9: Uint<LIMBS> = Uint::from_u64(9);
    let n24: Uint<LIMBS> = Uint::from_u64(24);
    let us: [&str; 12] = [  // implementation choice: only negative BN labels
        "-4369",  // for debugging only!
        "-44820001",  // for debugging only!
        "-402120000001",  // for debugging only!
        "-4080000000000001",
        "-40800000200000000401",
        "-400011000000000000000001",
        "-4000000000010040000000000001",
        "-48004000000000000000000000200001",
        "-480000008010000000000000000000000001",
        "-4810000000000000000000000000000020000001",
        "-41000000000000000000000000000020000000002001",
        "-480000004000000000000000000000000000000000000801"  // seriously, who'd need or think of using anything larger than this?
    ];

    println!("//! This crate implements elliptic curve arithmetic and bilinear pairings for Barreto-Naehrig (BN) curves.");
    println!("//! It was created to commemorate the 20th anniversary of the discovery of those curves in 2005.");
    println!("//!");
    println!("//! A BN curve is specified by an integer parameter <i>u</i> &#8712; &Zopf; such that the value");
    println!("//! <i>p</i> &#x2254; <i>36u&#x2074; + 36u&sup3; + 24u&sup2; + 6u + 1</i> is prime, defining a finite field");
    println!("//! <b>F</b><sub><i>p</i></sub>.");
    println!("//!");
    println!("//! The additional constraint <i>p &equiv; 3 (mod 4)</i> is typical, since it enables specifying");
    println!("//! the quadratic extension <b>F</b><sub><i>p&sup2;</i></sub> = <b>F</b><sub><i>p</i></sub>&lbrack;<i>i</i>&rbrack;/&lt;<i>i&sup2; + 1</i>&gt;");
    println!("//! and the tower-friendly extension fields");
    println!("//! <b>F</b><sub><i>p&#x2074;</i></sub> = <b>F</b><sub><i>p&sup2;</i></sub>&lbrack;<i>&sigma;</i>&rbrack;/&lt;<i>&sigma;&sup2; - &xi;</i>&gt;,");
    println!("//! <b>F</b><sub><i>p&#x2076;</i></sub> = <b>F</b><sub><i>p&sup2;</i></sub>&lbrack;<i>&tau;</i>&rbrack;/&lt;<i>&tau;&sup3; - &xi;</i>&gt;,");
    println!("//! and <b>F</b><sub><i>p&sup1;&#xFEFF;&sup2;</i></sub> = <b>F</b><sub><i>p&sup2;</i></sub>&lbrack;<i>z</i>&rbrack;/&lt;<i>z&#x2076; - &xi;</i>&gt;,");
    println!("//! where <i>&xi;</i> = <i>1 + i</i>.");
    println!("//!");
    println!("//! The BN curve equation is <i>E</i>/<b>F</b><sub><i>p</i></sub> : <i>Y&sup2;Z</i> = <i>X&sup3; + bZ&sup3;</i>,");
    println!("//! whose number of points is");
    println!("//! <i>n</i> &#x2254; <i>#E</i>(<b>F</b><sub><i>p</i></sub>) = <i>36u&#x2074; + 36u&sup3; + 18u&sup2; + 6u + 1</i>,");
    println!("//! which is usually required (with a careful choice of the curve parameter <i>u</i>) to be prime.");
    println!("//! The underlying finite field and the number of points are thus related as");
    println!("//! <i>n = p + 1 - t</i> where <i>t</i> &#x2254; <i>6u&sup2; + 1</i> is the trace of the Frobenius endomorphism");
    println!("//! on the curve.");
    println!("//! Incidentally, the curve order satisfies <i>n &equiv; 5 (mod 8)</i>.");
    println!("//!");
    println!("//! The default quadratic twist of the curve is <i>E'</i>/<b>F</b><sub><i>p&sup2;</i></sub> : <i>Y'&sup2;Z'</i> = <i>X'&sup3; + b'Z'&sup3;</i>");
    println!("//! with <i>b'</i> &#x2254; <i>b/&xi;</i>, whose number of points is <i>n'</i> &#x2254; <i>#E'</i>(<b>F</b><sub><i>p&sup2;</i></sub>) = <i>h'n</i>");
    println!("//! where <i>h'</i> &#x2254; <i>p - 1 + t</i> is called the cofactor of the curve twist.");
    println!("//!");
    println!("//! All supported curves were selected so that the BN curve parameter is a negative number");
    println!("//! (so that field inversion can be replaced by conjugation at the final exponentiation of a pairing)");
    println!("//! with absolute value of small Hamming weight (typically 5 or less),");
    println!("//! <i>ceil(lg(p)) = 64&times;LIMBS - 2</i> for 64-bit limbs,");
    println!("//! and the curve equation coefficients are always <i>b</i> = <i>2</i> and <i>b'</i> = <i>1 - i</i>.");
    println!("//!");
    println!("//! With this choice, a suitable generator of <i>n</i>-torsion on <i>E</i>/<b>F</b><sub><i>p</i></sub>");
    println!("//! is the point <i>G</i> &#x2254; &lbrack;<i>-1</i> : <i>1</i> : <i>1</i>&rbrack;,");
    println!("//! and a suitable generator of <i>n</i>-torsion on <i>E'</i>/<b>F</b><sub><i>p&sup2;</i></sub>");
    println!("//! is the point <i>G'</i> &#x2254; &lbrack;<i>h'</i>&rbrack;<i>G&#x2080;'</i> where <i>G&#x2080;'</i> &#x2254; &lbrack;-<i>i</i> : <i>1</i> : <i>1</i>&rbrack;.");
    println!("//! The maximum supported size is LIMBS = 12.");
    println!("//!");
    println!("//! All feasible care has been taken to make sure the arithmetic algorithms adopted in this crate");
    println!("//! are isochronous (\"constant-time\") and efficient.");
    println!("//! Yet, the no-warranty clause of the MIT license is in full force for this whole crate.");
    println!("//!");
    println!("//! References:");
    println!("//!");
    println!("//! * Paulo S. L. M. Barreto, Michael Naehrig:");
    println!("//! \"Pairing-Friendly Elliptic Curves of Prime Order.\"");
    println!("//! In: Preneel, B., Tavares, S. (eds). <i>Selected Areas in Cryptography -- SAC 2005</i>.");
    println!("//! Lecture Notes in Computer Science, vol. 3897, pp. 319--331.");
    println!("//! Springer, Berlin, Heidelberg. 2005. https://doi.org/10.1007/11693383_22");
    println!("//!");
    println!("//! * Geovandro C. C. F. Pereira, Marcos A. Simplicio Jr., Michael Naehrig, Paulo S. L. M. Barreto:");
    println!("//! \"A Family of Implementation-Friendly BN Elliptic Curves.\"");
    println!("//! <i>Journal of Systems and Software</i>, vol. 84, no. 8, pp. 1319--1326.");
    println!("//! Elsevier, 2011. https://doi.org/10.1016/j.jss.2011.03.083");
    println!("//!");
    println!("//! NB: This file was, and future versions should always be, created automatically by the `bnparamgen` tool.");
    println!();
    println!("use crypto_bigint::Word;");
    println!();
    println!("pub trait BNParam {{");
    println!("    const U: &'static [Word];                 // the BN curve selector, in absolute value");
    println!("    const LIMBS: usize;                       // number of limbs required to represent a base field element");
    println!("    const MODULUS: &'static [Word];           // base finite field modulus p = 36*u^4 + 36*u^3 + 24*u^2 - 6*u + 1");
    println!("    const NEG_INV_MOD: &'static [Word];       // -1/p mod 2^(64*LIMBS)");
    println!("    const MONTY_P: &'static [Word];           // (2^(64*LIMBS))^2 mod p");
    println!("    const ORDER: &'static [Word];             // cryptographic group order n = 36*u^4 - 36*u^3 + 18*u^2 - 6*u + 1");
    println!("    const NEG_INV_ORD: &'static [Word];       // -1/n mod 2^(64*LIMBS)");
    println!("    const MONTY_N: &'static [Word];           // (2^(64*LIMBS))^2 mod n");
    println!("    const SQRT_NEG_3: &'static [Word];        // sqrt(-3) mod p");
    println!("    const SVDW: &'static [Word];              // (-1 + sqrt(-3))/2 mod p, the Shallue & van de Woestijne constant");
    //println!("    const TWIST_COFACTOR: &'static [Word];    // cofactor of the curve twist h = 36*u^4 - 36*u^3 + 30*u^2 - 6*u + 1");  // unnecessary, since this cofactor is removed by other means than scalar multiplication.
    println!("    const ZETA: &'static [Word];              // primitive cube root ζ = -(18*u^3 - 18*u^2 + 9*u - 1) of unity, in absolute value");
    println!("    const THETA: &'static [Word];             // (-1/4)^((p + 5)/24)");
    println!("    const OMEGA: &'static [Word];             // order of optimal pairing, |6*u + 2|");
    println!("    const TRIPLES: Word;                      // number of precomputed optimal pairing triples");
    //println!("    const BY_ITER: Word;                      // Bernstein-Yang inversion iterations, m");
    //println!("    const BY_SCALE: &'static [Word];          // Bernstein-Yang inversion scale factor, ((p + 1)/2)^m mod p");
    println!("    const CURVE_B: Word = 2;                  // curve equation coefficient");
    println!("    const FIELD_XI_RE: Word = 1;              // extension fields: F_{{p^2}}[z]/<z^e - ξ> for e = 2, 3, 6");
    println!("    const FIELD_XI_IM: Word = 1;");
    println!("}}");
    println!();
    for limbs in 1..=us.len() {
        let u: Uint<LIMBS> = from_be_hex(us[limbs - 1]);
        let u_w = u.to_words();
        // p- = 36*u^4 - 36*u^3 + 24*u^2 - 6*u + 1 = (((u - 1)*6*u + 4)*u - 1)*6*u + 1
        let p: Uint<LIMBS> = (((u - n1)*n6*u + n4)*u - n1)*n6*u + n1;
        //println!("******** |p| = 4*|u| + 2 ? {}", bool::from(p.bits().ct_eq(&(4*u.bits() + 2))));
        let nzp: NonZero<Uint<LIMBS>> = NonZero::new(p).unwrap();
        let p_w = p.to_words();

        let neg_inv_p = Uint::<LIMBS>::ONE.shl((64*limbs) as u32) - p.invert_mod2k((64*limbs) as u32).unwrap();
        let neg_inv_p_w = neg_inv_p.to_words();

        let mut monty = Uint::<LIMBS>::ONE.shl((64*limbs) as u32).rem(&nzp);
        monty = monty.mul_mod_vartime(&monty, &nzp);
        let monty_w = monty.to_words();

        // t = 6*u^2 + 1
        let t: Uint<LIMBS> = n6*u*u + n1;
        let omega: Uint<LIMBS> = n6*u - n2;  // |6u+2| (NB: u < 0 by choice)
        let omega_w = omega.to_words();
        let n: Uint<LIMBS> = p + n1 - t;
        let n_w = n.to_words();

        let nzn: NonZero<Uint<LIMBS>> = NonZero::new(n).unwrap();

        let neg_inv_n = Uint::<LIMBS>::ONE.shl((64*limbs) as u32) - n.invert_mod2k((64*limbs) as u32).unwrap();
        let neg_inv_n_w = neg_inv_n.to_words();

        let mut monty_n = Uint::<LIMBS>::ONE.shl((64*limbs) as u32).rem(&nzn);
        monty_n = monty_n.mul_mod_vartime(&monty_n, &nzn);
        let monty_n_w = monty_n.to_words();

        //let h: Uint<LIMBS> = p - n1 + t;
        //let h_w = h.to_words();
        /*
         * The two primitive cube roots of unity are
         * 18*u^3 - 18*u^2 + 9*u - 2 mod p and -(18*u^3 - 18*u^2 + 9*u - 1) mod p.
         * The default one will be that which facilitates a uniform implementation
         * of conjugate computation across all supported curves, namely,
         * the one such that
         * v^(p^2) = v_0 + (zeta + 1)*v_1*z + zeta*v_2*z^2 - v_3*z^3 - (zeta + 1)*v_4*z^4 - zeta*v_5*z^5
         * for any v in the extension field F_{p^12} = F_{p^2}[z]/<z^6 + (1 + i).
         */
        // zeta = -(18*u^3 - 18*u^2 + 9*u - 1)
        // -(zeta + 1) = 18*u^3 - 18*u^2 + 9*u - 2
        //let zeta: Uint<LIMBS> = (u9*(u2*u*(u - u1) + u1)*u - u1).neg_mod(&p);  // larger sqrt(1)
        let zeta: Uint<LIMBS> = n9*(n2*u*(u - n1) + n1)*u - n2;
        assert_eq!(zeta.mul_mod_vartime(&zeta, &nzp).mul_mod_vartime(&zeta, &nzp), Uint::ONE);
        let zeta_w = zeta.to_words();

        let theta: Uint<LIMBS> = pow_mod_p(p - n4, (p - n1) - ((p + n5).div(n24)), p); // (-1/4)^((p+5)/24)
        let theta_w = theta.to_words();

        let sqrt_m3: Uint<LIMBS> = sqrt(Uint::from_word(3).neg_mod(&p), p);  // sqrt(-3) mod p
        let sqrt_m3_w = sqrt_m3.to_words();
        let svdw: Uint<LIMBS> = Uint::conditional_select(&(sqrt_m3 - n1), &(sqrt_m3 - n1 + p),
                                                         (sqrt_m3 - n1).is_odd()) >> 1;  // (-1 + sqrt(-3))/2
        let svdw_w = svdw.to_words();

        /*
        let by_iter: usize = (45907*(64*limbs - 2) + 26313)/19929;  // (49*(64*limbs - 2) + 57)/17;
        let by_scale: Uint<LIMBS> = pow_mod_p((p + n1) >> 1, Uint::from_word(by_iter as Word), p);  // ((p + 1)/2)^m mod p
        let by_scale_w = by_scale.to_words();
        // */

        println!();
        println!("pub struct BN{:03}Param;", 64*limbs - 2);
        println!();
        println!("impl BNParam for BN{:03}Param {{", 64*limbs - 2);

        assert_eq!(u.bits() as usize, 16*limbs - 1);
        println!("    const U: &'static [Word] = &[  // the BN curve selector in absolute value");
        print!("       ");
        /* big integer words for u */
        for i in 0..limbs {
            print!(" 0x{:016X},", u_w[i]);
        }
        for i in limbs..LIMBS {
            assert!(bool::from(u_w[i].is_zero()));
        }
        println!();
        println!("        // u = -{}", u.to_string_radix_vartime(10));
        println!("    ];");

        println!("    const LIMBS: usize = {};", limbs);
        println!("    const MODULUS: &'static [Word] = &[  // base finite field modulus");
        print!("       ");
        for i in 0..limbs {
            print!(" 0x{:X},", p_w[i]);
        }
        for i in limbs..LIMBS {
            assert!(bool::from(p_w[i].is_zero()));
        }
        println!();
        println!("        // p = {}: {} bits", p.to_string_radix_vartime(10), p.bits());
        println!("    ];");

        println!("    const NEG_INV_MOD: &'static [Word] = &[  // -1/p mod 2^(64*LIMBS)");
        print!("       ");
        for i in 0..limbs {
            print!(" 0x{:X},", neg_inv_p_w[i]);
        }
        for i in limbs..LIMBS {
            assert!(bool::from(neg_inv_p_w[i].is_zero()));
        }
        println!();
        println!("    ];");

        println!("    const MONTY_P: &'static [Word] = &[  // (2^(64*LIMBS))^2 mod p");
        print!("       ");
        for i in 0..limbs {
            print!(" 0x{:X},", monty_w[i]);
        }
        for i in limbs..LIMBS {
            assert!(bool::from(monty_w[i].is_zero()));
        }
        println!();
        println!("    ];");

        println!("    const ORDER: &'static [Word] = &[  // cryptographic group order");
        print!("       ");
        for i in 0..limbs {
            print!(" 0x{:X},", n_w[i]);
        }
        for i in limbs..LIMBS {
            assert!(bool::from(n_w[i].is_zero()));
        }
        println!();
        println!("        // n = {}: {} bits", n.to_string_radix_vartime(10), n.bits());
        println!("    ];");

        println!("    const NEG_INV_ORD: &'static [Word] = &[  // -1/n mod 2^(64*LIMBS)");
        print!("       ");
        for i in 0..limbs {
            print!(" 0x{:X},", neg_inv_n_w[i]);
        }
        for i in limbs..LIMBS {
            assert!(bool::from(neg_inv_n_w[i].is_zero()));
        }
        println!();
        println!("    ];");

        println!("    const MONTY_N: &'static [Word] = &[  // (2^(64*LIMBS))^2 mod n");
        print!("       ");
        for i in 0..limbs {
            print!(" 0x{:X},", monty_n_w[i]);
        }
        for i in limbs..LIMBS {
            assert!(bool::from(monty_n_w[i].is_zero()));
        }
        println!();
        println!("    ];");

        println!("    const SQRT_NEG_3: &'static [Word] = &[  // sqrt(-3) mod p");
        print!("       ");
        for i in 0..limbs {
            print!(" 0x{:X},", sqrt_m3_w[i]);
        }
        for i in limbs..LIMBS {
            assert!(bool::from(sqrt_m3_w[i].is_zero()));
        }
        println!();
        println!("    ];");

        println!("    const SVDW: &'static [Word] = &[  // (-1 + sqrt(-3))/2 mod p");
        print!("       ");
        for i in 0..limbs {
            print!(" 0x{:X},", svdw_w[i]);
        }
        for i in limbs..LIMBS {
            assert!(bool::from(svdw_w[i].is_zero()));
        }
        println!();
        println!("    ];");

        /*
        println!("    const TWIST_COFACTOR: &'static [Word] = &[");
        print!("       ");
        for i in 0..limbs {
            print!(" 0x{:X},", h_w[i]);
        }
        for i in limbs..LIMBS {
            assert!(bool::from(h_w[i].is_zero()));
        }
        println!();
        println!("        // h' = {}", h.to_string_radix_vartime(10));
        println!("    ];");
        // */

        assert_eq!(zeta.bits() as usize, 48*limbs - 1);
        println!("    const ZETA: &'static [Word] = &[  // primitive cube root of unity, in absolute value");
        print!("       ");
        /* big integer words for zeta */
        for i in 0..limbs {
            print!(" 0x{:016X},", zeta_w[i]);
        }
        for i in limbs..LIMBS {
            assert!(bool::from(zeta_w[i].is_zero()));
        }
        println!();
        println!("        // ζ = {} mod p", zeta.to_string_radix_vartime(10));
        //println!("        //  {}", zeta.to_string_radix_vartime(10));
        println!("    ];");

        println!("    const THETA: &'static [Word] = &[  // (-1/4)^((p+5)/24)");
        print!("       ");
        /* big integer words for theta */
        for i in 0..limbs {
            print!(" 0x{:016X},", theta_w[i]);
        }
        for i in limbs..LIMBS {
            assert!(bool::from(theta_w[i].is_zero()));
        }
        println!();
        println!("        // θ = {} mod p", theta.to_string_radix_vartime(10));
        println!("    ];");

        assert_eq!(omega.bits() as usize, 16*limbs + 1);
        println!("    const OMEGA: &'static [Word] = &[  // order of optimal pairing");
        print!("       ");
        /* big integer words for omega */
        for i in 0..limbs {
            print!(" 0x{:016X},", omega_w[i]);
        }
        for i in limbs..LIMBS {
            assert!(bool::from(omega_w[i].is_zero()));
        }
        println!();
        println!("        // ω = |6u + 2| = {}", omega.to_string_radix_vartime(10));
        println!("    ];");

        let ntriples = omega.bits() + popcnt(omega);
        println!("    const TRIPLES: Word = {};  // number of precomputed optimal pairing triples", ntriples);

        /*
        println!("    const BY_ITER: Word = {};  // Bernstein-Yang inversion iterations", by_iter);
        println!("    const BY_SCALE: &'static [Word] = &[  // Bernstein-Yang inversion scale factor");
        print!("       ");
        /* big integer words for omega */
        for i in 0..limbs {
            print!(" 0x{:016X},", by_scale_w[i]);
        }
        for i in limbs..LIMBS {
            assert!(bool::from(by_scale_w[i].is_zero()));
        }
        println!();
        println!("        // e = ((p + 1)/2)^m mod p = {}", by_scale.to_string_radix_vartime(10));
        println!("    ];");
        // */

        println!("}}");
    }
}

fn main() {
    bn();
}
