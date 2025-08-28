//! This crate implements elliptic curve arithmetic and bilinear pairings for Barreto-Naehrig (BN) curves.
//! It was created to commemorate the 20th anniversary of the discovery of those curves in 2005.
//!
//! A BN curve is specified by an integer parameter <i>u</i> &#8712; &Zopf; such that the value
//! <i>p</i> &#x2254; <i>36u&#x2074; + 36u&sup3; + 24u&sup2; + 6u + 1</i> is prime, defining a finite field
//! <b>F</b><sub><i>p</i></sub>.
//!
//! The additional constraint <i>p &equiv; 3 (mod 4)</i> is typical, since it enables specifying
//! the quadratic extension <b>F</b><sub><i>p&sup2;</i></sub> = <b>F</b><sub><i>p</i></sub>&lbrack;<i>i</i>&rbrack;/&lt;<i>i&sup2; + 1</i>&gt;
//! and the tower-friendly extension fields
//! <b>F</b><sub><i>p&#x2074;</i></sub> = <b>F</b><sub><i>p&sup2;</i></sub>&lbrack;<i>&sigma;</i>&rbrack;/&lt;<i>&sigma;&sup2; - &xi;</i>&gt;,
//! <b>F</b><sub><i>p&#x2076;</i></sub> = <b>F</b><sub><i>p&sup2;</i></sub>&lbrack;<i>&tau;</i>&rbrack;/&lt;<i>&tau;&sup3; - &xi;</i>&gt;,
//! and <b>F</b><sub><i>p&sup1;&#xFEFF;&sup2;</i></sub> = <b>F</b><sub><i>p&sup2;</i></sub>&lbrack;<i>z</i>&rbrack;/&lt;<i>z&#x2076; - &xi;</i>&gt;,
//! where <i>&xi;</i> = <i>1 + i</i>.
//!
//! The BN curve equation is <i>E</i>/<b>F</b><sub><i>p</i></sub> : <i>Y&sup2;Z</i> = <i>X&sup3; + bZ&sup3;</i>,
//! whose number of points over <b>F</b><sub><i>p</i></sub> is
//! <i>n</i> &#x2254; <i>#E</i>(<b>F</b><sub><i>p</i></sub>) = <i>36u&#x2074; + 36u&sup3; + 18u&sup2; + 6u + 1</i>,
//! which is usually required (with a careful choice of the curve parameter <i>u</i>) to be prime.
//! The underlying finite field and the number of points are thus related as
//! <i>n = p + 1 - t</i> where <i>t</i> &#x2254; <i>6u&sup2; + 1</i> is the trace of the Frobenius endomorphism
//! on the curve.
//! Incidentally, the curve order satisfies <i>n &equiv; 5 (mod 8)</i>.
//!
//! The default quadratic twist of the curve is <i>E'</i>/<b>F</b><sub><i>p&sup2;</i></sub> : <i>Y'&sup2;Z'</i> = <i>X'&sup3; + b'Z'&sup3;</i>
//! with <i>b'</i> &#x2254; <i>b/&xi;</i>, whose number of points is <i>n'</i> &#x2254; <i>#E'</i>(<b>F</b><sub><i>p&sup2;</i></sub>) = <i>h'n</i>
//! where <i>h'</i> &#x2254; <i>p - 1 + t</i> is called the cofactor of the <i>n</i>-torsion on the curve twist.
//!
//! All supported curves were selected so that the BN curve parameter is a negative number
//! (so that field inversion can be replaced by conjugation at the final exponentiation of a pairing)
//! with absolute value of small Hamming weight (typically 5 or less),
//! <i>ceil(lg(p)) = 64&times;LIMBS - 2</i> for 64-bit limbs,
//! and the curve equation coefficients are always <i>b</i> = <i>2</i> and <i>b'</i> = <i>1 - i</i>.
//!
//! With this choice, a suitable generator of <i>n</i>-torsion on <i>E</i>/<b>F</b><sub><i>p</i></sub>
//! is the point <i>G</i> &#x2254; &lbrack;<i>-1</i> : <i>1</i> : <i>1</i>&rbrack;,
//! and a suitable generator of <i>n</i>-torsion on <i>E'</i>/<b>F</b><sub><i>p&sup2;</i></sub>
//! is the point <i>G'</i> &#x2254; &lbrack;<i>h'</i>&rbrack;<i>G&#x2080;'</i> where <i>G&#x2080;'</i> &#x2254; &lbrack;-<i>i</i> : <i>1</i> : <i>1</i>&rbrack;.
//! The maximum supported size is LIMBS = 12.
//!
//! All feasible care has been taken to make sure the arithmetic algorithms adopted in this crate
//! are isochronous ("constant-time") and efficient.
//! Yet, the no-warranty clause of the MIT license is in full force for this whole crate.
//!
//! References:
//!
//! * Paulo S. L. M. Barreto, Michael Naehrig:
//! "Pairing-Friendly Elliptic Curves of Prime Order."
//! In: Preneel, B., Tavares, S. (eds). <i>Selected Areas in Cryptography -- SAC 2005</i>.
//! Lecture Notes in Computer Science, vol. 3897, pp. 319--331.
//! Springer, Berlin, Heidelberg. 2005. https://doi.org/10.1007/11693383_22
//!
//! * Geovandro C. C. F. Pereira, Marcos A. Simplicio Jr., Michael Naehrig, Paulo S. L. M. Barreto:
//! "A Family of Implementation-Friendly BN Elliptic Curves."
//! <i>Journal of Systems and Software</i>, vol. 84, no. 8, pp. 1319--1326.
//! Elsevier, 2011. https://doi.org/10.1016/j.jss.2011.03.083
//!
//! NB: This file was, and future versions should always be, created automatically by the `bnparamgen` tool.

use crypto_bigint::Word;

pub trait BNParam {
    const U: &'static [Word];                 // the BN curve selector, in absolute value
    const LIMBS: usize;                       // number of limbs required to represent a base field element
    const MODULUS: &'static [Word];           // base finite field modulus p = 36*u^4 + 36*u^3 + 24*u^2 - 6*u + 1
    const NEG_INV_MOD: &'static [Word];       // -1/p mod 2^(64*LIMBS)
    const MONTY_P: &'static [Word];           // (2^(64*LIMBS))^2 mod p
    const ORDER: &'static [Word];             // cryptographic group order n = 36*u^4 - 36*u^3 + 18*u^2 - 6*u + 1
    const NEG_INV_ORD: &'static [Word];       // -1/n mod 2^(64*LIMBS)
    const MONTY_N: &'static [Word];           // (2^(64*LIMBS))^2 mod n
    const SQRT_NEG_3: &'static [Word];        // sqrt(-3) mod p
    const SVDW: &'static [Word];              // (-1 + sqrt(-3))/2 mod p, the Shallue & van de Woestijne constant
    const ZETA: &'static [Word];              // primitive cube root ζ = -(18*u^3 - 18*u^2 + 9*u - 1) of unity, in absolute value
    const THETA: &'static [Word];             // (-1/4)^((p + 5)/24)
    const OMEGA: &'static [Word];             // order of optimal pairing, |6*u + 2|
    const TRIPLES: Word;                      // number of precomputed optimal pairing triples
    const CURVE_B: Word = 2;                  // curve equation coefficient
    const FIELD_XI_RE: Word = 1;              // extension fields: F_{p^2}[z]/<z^e - ξ> for e = 2, 3, 6
    const FIELD_XI_IM: Word = 1;
}


pub struct BN062Param;

impl BNParam for BN062Param {
    const U: &'static [Word] = &[  // the BN curve selector in absolute value
        0x0000000000004369,
        // u = -17257
    ];
    const LIMBS: usize = 1;
    const MODULUS: &'static [Word] = &[  // base finite field modulus
        0x2C4E3CD0D14F0AC3,
        // p = 3192556053414742723: 62 bits
    ];
    const NEG_INV_MOD: &'static [Word] = &[  // -1/p mod 2^(64*LIMBS)
        0xDB8AD7BBB2FD8A15,
    ];
    const MONTY_P: &'static [Word] = &[  // (2^(64*LIMBS))^2 mod p
        0xDE55803DB05C038,
    ];
    const ORDER: &'static [Word] = &[  // cryptographic group order
        0x2C4E3CD066CE445D,
        // n = 3192556051627918429: 62 bits
    ];
    const NEG_INV_ORD: &'static [Word] = &[  // -1/n mod 2^(64*LIMBS)
        0x88FDF683C27E500B,
    ];
    const MONTY_N: &'static [Word] = &[  // (2^(64*LIMBS))^2 mod n
        0x1C24D8F4049D30AB,
    ];
    const SQRT_NEG_3: &'static [Word] = &[  // sqrt(-3) mod p
        0x2C4D948EFFDA88C4,
    ];
    const SVDW: &'static [Word] = &[  // (-1 + sqrt(-3))/2 mod p
        0x2C4DE8AFE894C9C3,
    ];
    const ZETA: &'static [Word] = &[  // primitive cube root of unity, in absolute value
        0x00005420E8BA40FF,
        // ζ = 92500320207103 mod p
    ];
    const THETA: &'static [Word] = &[  // (-1/4)^((p+5)/24)
        0x0706C7478E24B945,
        // θ = 506311118267136325 mod p
    ];
    const OMEGA: &'static [Word] = &[  // order of optimal pairing
        0x0000000000019474,
        // ω = |6u + 2| = 103540
    ];
    const TRIPLES: Word = 25;  // number of precomputed optimal pairing triples
}

pub struct BN126Param;

impl BNParam for BN126Param {
    const U: &'static [Word] = &[  // the BN curve selector in absolute value
        0x0000000044820001, 0x0000000000000000,
        // u = -1149370369
    ];
    const LIMBS: usize = 2;
    const MODULUS: &'static [Word] = &[  // base finite field modulus
        0x3F5E4A24DF9C0013, 0x2F43EEE6B3695A66,
        // p = 62826445182901107724146846794103128083: 126 bits
    ];
    const NEG_INV_MOD: &'static [Word] = &[  // -1/p mod 2^(64*LIMBS)
        0xB9FEE1E4AAD035E5, 0xD8FE23566120ACCF,
    ];
    const MONTY_P: &'static [Word] = &[  // (2^(64*LIMBS))^2 mod p
        0x8FDF6EF1F4090A17, 0x1635B2CFD9DA7EF5,
    ];
    const ORDER: &'static [Word] = &[  // cryptographic group order
        0xD15E5E09A984000D, 0x2F43EEE6B3695A65,
        // n = 62826445182901107716220533323291951117: 126 bits
    ];
    const NEG_INV_ORD: &'static [Word] = &[  // -1/n mod 2^(64*LIMBS)
        0xB1EC226696F7B13B, 0x2E4855D55B551732,
    ];
    const MONTY_N: &'static [Word] = &[  // (2^(64*LIMBS))^2 mod n
        0xC01B926C09B7EBC0, 0x2613C51AE72E5B19,
    ];
    const SQRT_NEG_3: &'static [Word] = &[  // sqrt(-3) mod p
        0x7E3F38F66C300004, 0x2F43EEE602CA5257,
    ];
    const SVDW: &'static [Word] = &[  // (-1 + sqrt(-3))/2 mod p
        0xDECEC18DA5E6000B, 0x2F43EEE65B19D65E,
    ];
    const ZETA: &'static [Word] = &[  // primitive cube root of unity, in absolute value
        0x608F889739B60007, 0x00000000584F8407,
        // ζ = 27330809492488799194117963783 mod p
    ];
    const THETA: &'static [Word] = &[  // (-1/4)^((p+5)/24)
        0xF9FF583D7CFD4106, 0x1823917A5121C688,
        // θ = 32086152929224174052061845181391782150 mod p
    ];
    const OMEGA: &'static [Word] = &[  // order of optimal pairing
        0x000000019B0C0004, 0x0000000000000000,
        // ω = |6u + 2| = 6896222212
    ];
    const TRIPLES: Word = 42;  // number of precomputed optimal pairing triples
}

pub struct BN190Param;

impl BNParam for BN190Param {
    const U: &'static [Word] = &[  // the BN curve selector in absolute value
        0x0000402120000001, 0x0000000000000000, 0x0000000000000000,
        // u = -70511014969345
    ];
    const LIMBS: usize = 3;
    const MODULUS: &'static [Word] = &[  // base finite field modulus
        0x10138A17C0000013, 0xCDAA69E40E8C75C7, 0x244AC1F10FE053FA,
        // p = 889877785600686104533830233493087202422604793875909312531: 190 bits
    ];
    const NEG_INV_MOD: &'static [Word] = &[  // -1/p mod 2^(64*LIMBS)
        0x2B8614F2979435E5, 0xBE12481DDD063F8C, 0x453F3253D277C95C,
    ];
    const MONTY_P: &'static [Word] = &[  // (2^(64*LIMBS))^2 mod p
        0xD0B5EB9319DF6C9, 0xE37D55E42AF76A15, 0x1D4ED66E1AFD74DB,
    ];
    const ORDER: &'static [Word] = &[  // cryptographic group order
        0x7810888A4000000D, 0xCDAA69E3AE28FC0F, 0x244AC1F10FE053FA,
        // n = 889877785600686104533830233463256383030561625848170938381: 190 bits
    ];
    const NEG_INV_ORD: &'static [Word] = &[  // -1/n mod 2^(64*LIMBS)
        0x1571B5117B13B13B, 0x444F031964A805C8, 0x5294CFA1CBB0835A,
    ];
    const MONTY_N: &'static [Word] = &[  // (2^(64*LIMBS))^2 mod n
        0x30DC5A0E2C800770, 0x6ED951C9DD168E3D, 0xC7F382A8D97F45E,
    ];
    const SQRT_NEG_3: &'static [Word] = &[  // sqrt(-3) mod p
        0xF006031B00000004, 0xC1DC469647E2C12B, 0x244AC1F10FDFC31A,
    ];
    const SVDW: &'static [Word] = &[  // (-1 + sqrt(-3))/2 mod p
        0x800CC6996000000B, 0xC7C3583D2B379B79, 0x244AC1F10FE00B8A,
    ];
    const ZETA: &'static [Word] = &[  // primitive cube root of unity, in absolute value
        0x9006C37E60000007, 0x05E711A6E354DA4D, 0x0000000000004870,
        // ζ = 6310204058100459306506716670758343090896903 mod p
    ];
    const THETA: &'static [Word] = &[  // (-1/4)^((p+5)/24)
        0x469AF4CD2D3FD6D0, 0xFFA410953DC37020, 0x0DC89DC343BB6E7C,
        // θ = 337974292814237622327766490133188492735112688768315807440 mod p
    ];
    const OMEGA: &'static [Word] = &[  // order of optimal pairing
        0x000180C6C0000004, 0x0000000000000000, 0x0000000000000000,
        // ω = |6u + 2| = 423066089816068
    ];
    const TRIPLES: Word = 58;  // number of precomputed optimal pairing triples
}

pub struct BN254Param;

impl BNParam for BN254Param {
    const U: &'static [Word] = &[  // the BN curve selector in absolute value
        0x4080000000000001, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
        // u = -4647714815446351873
    ];
    const LIMBS: usize = 4;
    const MODULUS: &'static [Word] = &[  // base finite field modulus
        0xA700000000000013, 0x6121000000000013, 0xBA344D8000000008, 0x2523648240000001,
        // p = 16798108731015832284940804142231733909889187121439069848933715426072753864723: 254 bits
    ];
    const NEG_INV_MOD: &'static [Word] = &[  // -1/p mod 2^(64*LIMBS)
        0x8435E50D79435E5, 0x6E371BA81104F6C8, 0x92022379C45B843C, 0xB65373CCBA60808C,
    ];
    const MONTY_P: &'static [Word] = &[  // (2^(64*LIMBS))^2 mod p
        0xB3E886745370473D, 0x55EFBF6E8C1CC3F1, 0x281E3A1B7F86954F, 0x1B0A32FDF6403A3D,
    ];
    const ORDER: &'static [Word] = &[  // cryptographic group order
        0xA10000000000000D, 0xFF9F800000000010, 0xBA344D8000000007, 0x2523648240000001,
        // n = 16798108731015832284940804142231733909759579603404752749028378864165570215949: 254 bits
    ];
    const NEG_INV_ORD: &'static [Word] = &[  // -1/n mod 2^(64*LIMBS)
        0xEA3B13B13B13B13B, 0x4B35EE94731FCF86, 0x42217FC31DF24016, 0xF3D5266BA9BBA566,
    ];
    const MONTY_N: &'static [Word] = &[  // (2^(64*LIMBS))^2 mod n
        0xDF8596B6F40AA7A1, 0xE0885092E2231EC3, 0xC300765B575D5A78, 0x24E8B3BC325F9035,
    ];
    const SQRT_NEG_3: &'static [Word] = &[  // sqrt(-3) mod p
        0xC00000000000004, 0xCF0F000000000006, 0x26CD890000000003, 0x2523648240000001,
    ];
    const SVDW: &'static [Word] = &[  // (-1 + sqrt(-3))/2 mod p
        0xD98000000000000B, 0x181800000000000C, 0x7080EB4000000006, 0x2523648240000001,
    ];
    const ZETA: &'static [Word] = &[  // primitive cube root of unity, in absolute value
        0xCD80000000000007, 0x4909000000000006, 0x49B3624000000002, 0x0000000000000000,
        // ζ = 1807136345283977465813277102364620289631804529403213381639 mod p
    ];
    const THETA: &'static [Word] = &[  // (-1/4)^((p+5)/24)
        0x859975AB54B5EF9B, 0xCB1BAEA0B017046E, 0xC2B0D5792CD135AC, 0x19F3DB6884CDCA43,
        // θ = 11738679351593087254194652674723591313161026180079295257327058927925828382619 mod p
    ];
    const OMEGA: &'static [Word] = &[  // order of optimal pairing
        0x8300000000000004, 0x0000000000000001, 0x0000000000000000, 0x0000000000000000,
        // ω = |6u + 2| = 27886288892678111236
    ];
    const TRIPLES: Word = 70;  // number of precomputed optimal pairing triples
}

pub struct BN318Param;

impl BNParam for BN318Param {
    const U: &'static [Word] = &[  // the BN curve selector in absolute value
        0x0000200000000401, 0x0000000000004080, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
        // u = -304592638180276488373249
    ];
    const LIMBS: usize = 5;
    const MODULUS: &'static [Word] = &[  // base finite field modulus
        0x8409E41B08413813, 0x50BF2B5D3A282988, 0x29EA7C35A71B37AA, 0x4010FE7C6D5CC82A, 0x2523648289B36240,
        // p = 309870412826571072545785855492780873515488975169480683468371291763507840367575994024316436035603: 318 bits
    ];
    const NEG_INV_MOD: &'static [Word] = &[  // -1/p mod 2^(64*LIMBS)
        0x4938437C6AACADE5, 0x7B96E8C7B0EDE444, 0xEFBFE36641C45E10, 0xFDA833931631A6CD, 0x3E74ABE4BFC2A771,
    ];
    const MONTY_P: &'static [Word] = &[  // (2^(64*LIMBS))^2 mod p
        0xCB414550A0290D0F, 0xE8F195C8F5302C3F, 0x7D96F275A3A6DC14, 0x42F53ACEFC6FFB9, 0x209EFE19B36785E2,
    ];
    const ORDER: &'static [Word] = &[  // cryptographic group order
        0x7E08641B07E1080D, 0xEFFF2B5D160D2388, 0x29EA7C354599B7A9, 0x4010FE7C6D5CC82A, 0x2523648289B36240,
        // n = 309870412826571072545785855492780873515488975168924023416969566805357031795524508933046403139597: 318 bits
    ];
    const NEG_INV_ORD: &'static [Word] = &[  // -1/n mod 2^(64*LIMBS)
        0x279E97FF5969793B, 0x9295AA7F925FB477, 0x2CF855D07CC959EB, 0x1B6F57FB8A4A1678, 0x8676BC7505129C3D,
    ];
    const MONTY_N: &'static [Word] = &[  // (2^(64*LIMBS))^2 mod n
        0x5CD5AAA94DD22D2E, 0xE9BF7FEF81350540, 0xC7DA00D20AEB8D1F, 0xFF5DC746D58374CF, 0x88138925E79C61,
    ];
    const SQRT_NEG_3: &'static [Word] = &[  // sqrt(-3) mod p
        0x3C03241203C06004, 0xC7BF22E828FA8DB0, 0xC9E9F3ECA9090A6F, 0x40106B15A8DBECC6, 0x2523648289B36240,
    ];
    const SVDW: &'static [Word] = &[  // (-1 + sqrt(-3))/2 mod p
        0x600684168600CC0B, 0xC3F2722B1915B9C, 0x79EA38112812210D, 0x4010B4C90B1C5A78, 0x2523648289B36240,
    ];
    const ZETA: &'static [Word] = &[  // primitive cube root of unity, in absolute value
        0x2403600482406C07, 0x4480043A8896CDEC, 0xB00044247F09169D, 0x000049B362406DB1, 0x0000000000000000,
        // ζ = 508663660878059166113907264771422090031659326445264037675986924284701703 mod p
    ];
    const THETA: &'static [Word] = &[  // (-1/4)^((p+5)/24)
        0xEC1404A33922B879, 0x39F4F8E17E5E5FFB, 0x0E575687CA4256D2, 0xF291D20FEB634EFC, 0x11DDD09B259C8A86,
        // θ = 149072406942302338993478572968733513730391239242806130469796674039322986310208100495302517241977 mod p
    ];
    const OMEGA: &'static [Word] = &[  // order of optimal pairing
        0x0000C00000001804, 0x0000000000018300, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
        // ω = |6u + 2| = 1827555829081658930239492
    ];
    const TRIPLES: Word = 90;  // number of precomputed optimal pairing triples
}

pub struct BN382Param;

impl BNParam for BN382Param {
    const U: &'static [Word] = &[  // the BN curve selector in absolute value
        0x0000000000000001, 0x0000000040001100, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
        // u = -19807120908796293182354620417
    ];
    const LIMBS: usize = 6;
    const MODULUS: &'static [Word] = &[  // base finite field modulus
        0x13, 0x1380052E00, 0x4004620095040000, 0x5B710818AC000008, 0xE42DE125B0015840, 0x240026400F3D82B2,
        // p = 5540996953667913971058039301942914304734176495422447785045292539108217242186829586959562222833658991069414454984723: 382 bits
    ];
    const NEG_INV_MOD: &'static [Word] = &[  // -1/p mod 2^(64*LIMBS)
        0x79435E50D79435E5, 0x8827B640AFDE30D, 0x861567FE0E908DD4, 0x9C7031B652D43848, 0xEF8597D0478E604F, 0x3582C27A42FDCD8D,
    ];
    const MONTY_P: &'static [Word] = &[  // (2^(64*LIMBS))^2 mod p
        0x69AD4AB90DB04BC, 0xE80C0A3EDDDD6274, 0xC9E6B470CE70B141, 0x65605B2172BA3FCF, 0xB6995178418E89C9, 0x79948F5FBE4C744,
    ];
    const ORDER: &'static [Word] = &[  // cryptographic group order
        0xD, 0x1080046200, 0xE0042F008E3E0000, 0x5B710818AC000007, 0xE42DE125B0015840, 0x240026400F3D82B2,
        // n = 5540996953667913971058039301942914304734176495422447785042938606876043190415948413757785063597439175372845535461389: 382 bits
    ];
    const NEG_INV_ORD: &'static [Word] = &[  // -1/n mod 2^(64*LIMBS)
        0xB13B13B13B13B13B, 0xF25DEACC8B5CD13, 0x13B4EB1D200B9C06, 0xAA244F7AB280DFB9, 0xC08335F875845D22, 0x2D6C0021AD7A0A8D,
    ];
    const MONTY_N: &'static [Word] = &[  // (2^(64*LIMBS))^2 mod n
        0x67BC961D1EDC52C8, 0x22A0C57E745163E3, 0x66220C6DAB643A11, 0x8D5F0EA4F5122BDF, 0x8434A18FE9D020BA, 0x22DC13812E451EC5,
    ];
    const SQRT_NEG_3: &'static [Word] = &[  // sqrt(-3) mod p
        0x4, 0x600019800, 0xC001FE0043BC0000, 0x3CF60565C8000003, 0xE42DE1252000E580, 0x240026400F3D82B2,
    ];
    const SVDW: &'static [Word] = &[  // (-1 + sqrt(-3))/2 mod p
        0xB, 0xCC0036300, 0x330006C600000, 0x4C3386BF3A000006, 0xE42DE12568011EE0, 0x240026400F3D82B2,
    ];
    const ZETA: &'static [Word] = &[  // primitive cube root of unity, in absolute value
        0x0000000000000007, 0x00000006C001CB00, 0x4001320028A40000, 0x0F3D815972000002, 0x0000000048003960, 0x0000000000000000,
        // ζ = 139873861001352573942899706595100245922119508633787793781335834047889629007110865944583 mod p
    ];
    const THETA: &'static [Word] = &[  // (-1/4)^((p+5)/24)
        0x6603054DCCAEFAB3, 0x8A75CBF442F9193A, 0xAAB86C79C7FCC84E, 0xC34B845C57D62362, 0x0F15954A37B15704, 0x10F8BEE840937D43,
        // θ = 2612178012541387507470319031443728527449558961211446874787096172694142248882595024265534124196778010927025884166835 mod p
    ];
    const OMEGA: &'static [Word] = &[  // order of optimal pairing
        0x0000000000000004, 0x0000000180006600, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
        // ω = |6u + 2| = 118842725452777759094127722500
    ];
    const TRIPLES: Word = 104;  // number of precomputed optimal pairing triples
}

pub struct BN446Param;

impl BNParam for BN446Param {
    const U: &'static [Word] = &[  // the BN curve selector in absolute value
        0x0040000000000001, 0x0000400000000001, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
        // u = -1298074214633725371891096301338625
    ];
    const LIMBS: usize = 7;
    const MODULUS: &'static [Word] = &[  // base finite field modulus
        0x1380000000000013, 0x421BC0000000004E, 0x5156523000000084, 0x245EAACD7400006C, 0x241B1B05A00024, 0xD86C28800, 0x2400000000024090,
        // p = 102211695604075534719613248433473542060037253657367246082774695803908643108158009550075756863430499611136405278723403576762516197343251: 446 bits
    ];
    const NEG_INV_MOD: &'static [Word] = &[  // -1/p mod 2^(64*LIMBS)
        0xC35E50D79435E5, 0xB0E9AA31A3CFC745, 0xEE2AE5CE18B53DD7, 0xD2CCA970525D198F, 0xF3C754B67F9BCEF6, 0x2D6E49FABA499912, 0xA4E6A39449100EAC,
    ];
    const MONTY_P: &'static [Word] = &[  // (2^(64*LIMBS))^2 mod p
        0xE26FA0B04A7F400A, 0xEC8DF54C75504D52, 0x75E8ACEEAA6E88B0, 0xBAA7137AE1D5FA30, 0x4BAF0A759734FF4C, 0xF5CACE4BB4B43382, 0x1A05DC7494424D1,
    ];
    const ORDER: &'static [Word] = &[  // cryptographic group order
        0x108000000000000D, 0x3F18600000000042, 0x515351700000007E, 0x245EAACD1400006C, 0x241B1B05A00024, 0xD86C28800, 0x2400000000024090,
        // n = 102211695604075534719613248433473542060037253657367246082774695803898533128157827772529234506049127247739101387916788811336714695999501: 446 bits
    ];
    const NEG_INV_ORD: &'static [Word] = &[  // -1/n mod 2^(64*LIMBS)
        0xDBB13B13B13B13B, 0x2E1B6731FCF86D11, 0xC6BEC51B424D234D, 0x1B1CE0249787AD55, 0x3AC020B3CD8652EF, 0x452E55E3927E7DC3, 0xAC5B624521068C24,
    ];
    const MONTY_N: &'static [Word] = &[  // (2^(64*LIMBS))^2 mod n
        0x34AF237294F155E6, 0xDAE61271CED1912A, 0x144EE8957078C4CA, 0xF32FE0F2D8A7A4C0, 0x82FEA7875F5AB6DF, 0x1024D7BA46D0F511, 0x180B87A71C2F0A2E,
    ];
    const SQRT_NEG_3: &'static [Word] = &[  // sqrt(-3) mod p
        0x600000000000004, 0x1E09C00000000018, 0x362B88A00000003C, 0x24439D4744000048, 0x241B1443F00024, 0xD86C1F800, 0x2400000000024090,
    ];
    const SVDW: &'static [Word] = &[  // (-1 + sqrt(-3))/2 mod p
        0xCC000000000000B, 0x3012C00000000033, 0x43C0ED6800000060, 0x2451240A5C00005A, 0x241B17A4C80024, 0xD86C24000, 0x2400000000024090,
    ];
    const ZETA: &'static [Word] = &[  // primitive cube root of unity, in absolute value
        0x06C0000000000007, 0x120900000000001B, 0x0D9564C800000024, 0x000D86C318000012, 0x0000000360D80000, 0x0000000000004800, 0x0000000000000000,
        // ζ = 39370513046095894743754800957392468149424668731888186914796648912261315659947183777723306046040047623 mod p
    ];
    const THETA: &'static [Word] = &[  // (-1/4)^((p+5)/24)
        0x41CFEADA080C2332, 0x948FAE675396864B, 0xDDC23888AB244E86, 0xF1D58DA5FF569B56, 0xBC534C389B8DD5B7, 0x36F095C0819CB8EE, 0x165C7B9BADE4D70D,
        // θ = 63488400386813011843049989556520715598557097950871684001516035517641511830739977305921302168918206997528601271773457180214538093208370 mod p
    ];
    const OMEGA: &'static [Word] = &[  // order of optimal pairing
        0x0180000000000004, 0x0001800000000006, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
        // ω = |6u + 2| = 7788445287802352231346577808031748
    ];
    const TRIPLES: Word = 120;  // number of precomputed optimal pairing triples
}

pub struct BN510Param;

impl BNParam for BN510Param {
    const U: &'static [Word] = &[  // the BN curve selector in absolute value
        0x0000000000200001, 0x4800400000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
        // u = -95705713770728576555981240964269211649
    ];
    const LIMBS: usize = 8;
    const MODULUS: &'static [Word] = &[  // base finite field modulus
        0x2100009C00013, 0xF013800002400036, 0x40136C814D480855, 0x739A900840000014, 0x44587CB45BBC, 0xC811688DB201B000, 0x2400000000668513, 0x39AB0D091160A200,
        // p = 3020327014009990438234080072655242602531850107178928540503237072443550689212631117007089764031988721392497568583687652635315169682718877302907784275165203: 510 bits
    ];
    const NEG_INV_MOD: &'static [Word] = &[  // -1/p mod 2^(64*LIMBS)
        0xABCC7C5D9B5435E5, 0x77EB05E52AF9A9, 0x92D19BCFEE819E18, 0x544B0ABCE11D817, 0xBAC7C6FC4B941639, 0xC73A63EC6417A437, 0xA2F81BB694813DF1, 0xDA575D9097C2877D,
    ];
    const MONTY_P: &'static [Word] = &[  // (2^(64*LIMBS))^2 mod p
        0x8FF9B35B594AD2F3, 0x710489408C0D6947, 0x287A063966FDD1A6, 0x82D87D6178A931A4, 0x321DF12CA4FD4C77, 0xB61365671746C689, 0x2C1CBC4C3A55B66B, 0x18D67A6DED8E4F79,
    ];
    const ORDER: &'static [Word] = &[  // cryptographic group order
        0x1F8000840000D, 0x9010800002400036, 0x40136C814CDC07F2, 0xFA19B807E0000014, 0x44587CB45BBB, 0xC811688DB201B000, 0x2400000000668513, 0x39AB0D091160A200,
        // n = 3020327014009990438234080072655242602531850107178928540503237072443550689212576159505199576279039402931204192055161927468147640391414785050582680531369997: 510 bits
    ];
    const NEG_INV_ORD: &'static [Word] = &[  // -1/n mod 2^(64*LIMBS)
        0x3B8AFDF6E953B13B, 0x338C339D72FEB6BB, 0x5D88679D267DEBB8, 0x95C618B4082A94C3, 0xEEFE4E4F27F7E469, 0xF4A088E31EF5FC32, 0xBFBF9DFD00D74CFF, 0x3E6EDA1B8DE99E1A,
    ];
    const MONTY_N: &'static [Word] = &[  // (2^(64*LIMBS))^2 mod n
        0xC94822768CFA9D9D, 0x5F2DE31D0698BC9C, 0x44BB50FA3DAA939B, 0x43CCFB96A60BA213, 0x70B8F00B119C4D6B, 0xA6CA0FF8B71B95A0, 0x938E89290BD0AA19, 0x10AECFC0FEB827CD,
    ];
    const SQRT_NEG_3: &'static [Word] = &[  // sqrt(-3) mod p
        0xF00003000004, 0xC006000002400024, 0x4012F300DC3803C6, 0xC0B87003C0000014, 0x44587BA2F9D0, 0xFB0745CBCC012000, 0x2400000000668512, 0x39AB0D091160A200,
    ];
    const SVDW: &'static [Word] = &[  // (-1 + sqrt(-3))/2 mod p
        0x180000660000B, 0x580CC0000240002D, 0x40132FC114C0060E, 0x9A29800600000014, 0x44587C2BAAC6, 0x618C572CBF016800, 0x2400000000668513, 0x39AB0D091160A200,
    ];
    const ZETA: &'static [Word] = &[  // primitive cube root of unity, in absolute value
        0x0000900003600007, 0x9806C00000000009, 0x00003CC038880247, 0xD971100240000000, 0x000000000088B0F5, 0x66851160F3004800, 0x0000000000000000, 0x0000000000000000,
        // ζ = 15779240836369751408338294519848835267635377088586513253757872694541139861299833685249526346237263725138661968183303 mod p
    ];
    const THETA: &'static [Word] = &[  // (-1/4)^((p+5)/24)
        0xB1806C932AED25F1, 0x96177604B97F4BBA, 0xCB6FB2BEDECAED02, 0xFC28603A9E5473CA, 0x5DE3141FBBB469CE, 0x07A57797B1F075FE, 0x17711CF6FAC6D962, 0x1DF877ADAA860EBF,
        // θ = 1569686439575957918055420066554113504507532781672677269599738150512726052028822916313922576585194963771487590529957552756296748532827457475741624791016945 mod p
    ];
    const OMEGA: &'static [Word] = &[  // order of optimal pairing
        0x0000000000C00004, 0xB001800000000000, 0x0000000000000001, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
        // ω = |6u + 2| = 574234282624371459335887445785615269892
    ];
    const TRIPLES: Word = 138;  // number of precomputed optimal pairing triples
}

pub struct BN574Param;

impl BNParam for BN574Param {
    const U: &'static [Word] = &[  // the BN curve selector in absolute value
        0x0000000000000001, 0x0000801000000000, 0x0000000000004800, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
        // u = -6272084589684153838424562807849096541372417
    ];
    const LIMBS: usize = 9;
    const MODULUS: &'static [Word] = &[  // base finite field modulus
        0x13, 0x2704E000000000, 0x15F000, 0x24A4002108408400, 0xA206C00A71000025, 0x1016CDB25B2D8510, 0xC9229D1C8030D21A, 0x4691711B11E63CC4, 0x39AA40019A434204,
        // p = 55712176898108630715646664073292062269992999589911255268390701003521370225170114374909798473048917383162688166005803493543059783663053445566477001360656977406425707738824723: 574 bits
    ];
    const NEG_INV_MOD: &'static [Word] = &[  // -1/p mod 2^(64*LIMBS)
        0x79435E50D79435E5, 0xD573B2B79435E50D, 0xAAE72E181C5DAADB, 0x2B196D77F0378DB7, 0xB003025784E029CD, 0x95FDEC62D039118B, 0xFAF0E2CFC7A406C4, 0xB02FBFC8CCBEEBCB, 0x3DD84BAAB5C50D6C,
    ];
    const MONTY_P: &'static [Word] = &[  // (2^(64*LIMBS))^2 mod p
        0xEF7A4CB77C262E, 0xCA84F4386EF5CDC2, 0xE5B9AF37D3363D0E, 0x1D95096FF9D5EC2D, 0xE362428F3FEC2124, 0x7E94E7177C7BA6FC, 0xCEC8D4217B360C05, 0x4322F70A4A23AC8F, 0x30A6E5281DCAC056,
    ];
    const ORDER: &'static [Word] = &[  // cryptographic group order
        0xD, 0x21042000000000, 0x129000, 0x746E001F87E07E00, 0xA206C009F7800023, 0x1016CDB25B2D8510, 0xC9229D1C8030D21A, 0x4691711B11E63CC4, 0x39AA40019A434204,
        // n = 55712176898108630715646664073292062269992999589911255268390701003521370225170114374909562438778316462520201502849841632526444576299598664378711809439110819574500760408293389: 574 bits
    ];
    const NEG_INV_ORD: &'static [Word] = &[  // -1/n mod 2^(64*LIMBS)
        0xB13B13B13B13B13B, 0x92EF885B13B13B13, 0x80C1E4BBD5961307, 0x7D6679A5F7D30833, 0xA1113301E20DCED3, 0x3A87F419033AA67B, 0x29A855E9B09A0CA4, 0xBC01C75C65A51C51, 0xD447C63E2658C17C,
    ];
    const MONTY_N: &'static [Word] = &[  // (2^(64*LIMBS))^2 mod n
        0x5483A50B1551AB96, 0xA79C392FF6018DF5, 0x792401ABEE168A90, 0xE2D52709EEA3FF99, 0x6394C82B5B74B2F2, 0x369E81132EDA0CB4, 0xA03CD8E4B857AA6C, 0x86746B5DCECA32BA, 0x217A0C405265FB89,
    ];
    const SQRT_NEG_3: &'static [Word] = &[  // sqrt(-3) mod p
        0x4, 0xC018000000000, 0x6C000, 0xE21C000F03C03C00, 0x6C048004BF000010, 0x600F33CC3CC90360, 0xC921D014802C8C11, 0x4691711B11E63CC4, 0x39AA40019A434204,
    ];
    const SVDW: &'static [Word] = &[  // (-1 + sqrt(-3))/2 mod p
        0xB, 0x19833000000000, 0xE5800, 0x360001806006000, 0x8705A0079800001B, 0xB81300BF4BFB4438, 0xC9223698802EAF15, 0x4691711B11E63CC4, 0x39AA40019A434204,
    ];
    const ZETA: &'static [Word] = &[  // primitive cube root of unity, in absolute value
        0x0000000000000007, 0x000D81B000000000, 0x0000000000079800, 0x2144000902402400, 0x1B012002D900000A, 0x5803CCF30F3240D8, 0x0000668400022304, 0x0000000000000000, 0x0000000000000000,
        // ζ = 4441280733820121649551821245324326230822795982800839172596972092860643811089551957033595832576598024143039909835386371557426200583 mod p
    ];
    const THETA: &'static [Word] = &[  // (-1/4)^((p+5)/24)
        0x8F80C7AB3DBBE795, 0xEFB24257C99700DC, 0x0C69716FCC97A1F9, 0xE3071EA7449020C6, 0x198B85C58DF35671, 0xFC2E189441DFA649, 0xF707BEC1FD400FDE, 0x6F83DB54E46A196D, 0x163AA608C26C4C22,
        // θ = 21476293880417812167638072229799268790153648813667373584936182998239222433460305986250559047259460762822367390702346220120056251984008759234898571067856313180244109682272149 mod p
    ];
    const OMEGA: &'static [Word] = &[  // order of optimal pairing
        0x0000000000000004, 0x0003006000000000, 0x000000000001B000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
        // ω = |6u + 2| = 37632507538104923030547376847094579248234500
    ];
    const TRIPLES: Word = 154;  // number of precomputed optimal pairing triples
}

pub struct BN638Param;

impl BNParam for BN638Param {
    const U: &'static [Word] = &[  // the BN curve selector in absolute value
        0x0000000020000001, 0x0000000000000000, 0x0000000048100000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
        // u = -411404147422492935715050930693816973062863585281
    ];
    const LIMBS: usize = 10;
    const MODULUS: &'static [Word] = &[  // base finite field modulus
        0x10000009C0000013, 0x240000036000002, 0x4A100015F4E00000, 0x144480016CD10009, 0x75A4840000000000, 0x44766363358CA88A, 0xC000000000000000, 0x66C8673388B26B26, 0x0, 0x39DD931888240000,
        // p = 1031281347894654488181235424486638828759349134375329900676904164927561106056626111175527406171397716689854946278575331785178645354038637139349030235613925974829763274806321795310693110136176659: 638 bits
    ];
    const NEG_INV_MOD: &'static [Word] = &[  // -1/p mod 2^(64*LIMBS)
        0xAE016B14979435E5, 0x968821CD95843C76, 0xCD45612C9257ED74, 0x7E48BD1138EA2146, 0x90ABA2C4D34669C6, 0x15015D95B7C01DC9, 0xEE610D29FF571C5A, 0x22EEE76581894B1C, 0x58F54B50E055CE9F, 0x16B9809208400D9C,
    ];
    const MONTY_P: &'static [Word] = &[  // (2^(64*LIMBS))^2 mod p
        0x81604B883BF65D0E, 0xFA354A78F3191E15, 0xFA2E0C8C1347BA4D, 0x663BD79A447C6F3F, 0xD4A87450A9DFC703, 0x1ED5644D5C089835, 0x5C7E534E700E9ADB, 0x679ED767BD9AEE59, 0x97BCDFCEEB117B77, 0x190B390BECB2A305,
    ];
    const ORDER: &'static [Word] = &[  // cryptographic group order
        0xF80000084000000D, 0x240000036000001, 0xDDF8001294200000, 0x144480016CD10008, 0xFBEE7E0000000000, 0x44766363358CA889, 0xC000000000000000, 0x66C8673388B26B26, 0x0, 0x39DD931888240000,
        // n = 1031281347894654488181235424486638828759349134375329900676904164927561106056626111175527406171396701169619847708770284267135826870409245012068329231717493146338862828226918995035610820777082893: 638 bits
    ];
    const NEG_INV_ORD: &'static [Word] = &[  // -1/n mod 2^(64*LIMBS)
        0xB3BD595F7B13B13B, 0x98D6812928108BD3, 0x5BE5D62005B2FDFF, 0xE5B220E59E0B153A, 0x47A25D01D3625CC2, 0x5349511DA1BA97B9, 0x5B95BC1AD237AD90, 0x8D5F60FCC33B4785, 0xD4F63953B78DAA43, 0x1E4FD2F899AA6244,
    ];
    const MONTY_N: &'static [Word] = &[  // (2^(64*LIMBS))^2 mod n
        0x5992FEF1C80D5FC4, 0x204E3428A70683FD, 0xDD0B26F6172C2526, 0x10389E31F3CC90F2, 0x8B6016921B9D5019, 0x8904B9C12A7AF1, 0x6B007716CF699585, 0xD0F5C0C8A263100, 0x379609183770F0B6, 0x3325F86ACF6AE6F9,
    ];
    const SQRT_NEG_3: &'static [Word] = &[  // sqrt(-3) mod p
        0xF000000300000004, 0x240000024000000, 0x38F00006C1800000, 0x14448000F3360004, 0xC11C3C0000000000, 0x4476636223B31B04, 0x8000000000000000, 0x66C86732BB219CC4, 0x0, 0x39DD931888240000,
    ];
    const SVDW: &'static [Word] = &[  // (-1 + sqrt(-3))/2 mod p
        0x800000066000000B, 0x24000002D000001, 0xC180000E5B300000, 0x1444800130038006, 0x9B60600000000000, 0x44766362AC9FE1C7, 0xA000000000000000, 0x66C8673321EA03F5, 0x0, 0x39DD931888240000,
    ];
    const ZETA: &'static [Word] = &[  // primitive cube root of unity, in absolute value
        0x9000000360000007, 0x0000000009000000, 0x8890000799B00000, 0x000000003CCD8002, 0xDA44240000000000, 0x0000000088ECC6C2, 0x2000000000000000, 0x0000000066C86731, 0x0000000000000000, 0x0000000000000000,
        // ζ = 1253367709533050090911091746066162806386078536927945238808055240866357394774838187084743178151460997910422599659956108765485360652794073144360967 mod p
    ];
    const THETA: &'static [Word] = &[  // (-1/4)^((p+5)/24)
        0x4E28DEFD7EB04A9D, 0x7F5F7E57AF324E59, 0xFE28A26DFCE9E826, 0xBD6314F24B1F657A, 0xAE9B7FBC026DA822, 0x44B0AF1A6B8311D6, 0x8EB97336AC399800, 0xBB66E60350BED6A5, 0x2A3ABF53F9E21ADB, 0x2DC1309EB7DA0EEE,
        // θ = 815440879232149068889601993245614121863882042810424716930720624952492482305909110522377562425688154862180498835681184269755740768438653692621072241339210911018020970679340367538232548750543517 mod p
    ];
    const OMEGA: &'static [Word] = &[  // order of optimal pairing
        0x00000000C0000004, 0x0000000000000000, 0x00000001B0600000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
        // ω = |6u + 2| = 2468424884534957614290305584162901838377181511684
    ];
    const TRIPLES: Word = 170;  // number of precomputed optimal pairing triples
}

pub struct BN702Param;

impl BNParam for BN702Param {
    const U: &'static [Word] = &[  // the BN curve selector in absolute value
        0x0020000000002001, 0x0000000000000000, 0x0000410000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
        // u = -24319387245186224558909315616398949456081916769869825
    ];
    const LIMBS: usize = 11;
    const MODULUS: &'static [Word] = &[  // base finite field modulus
        0xC0036021009C013, 0xA202100900A20420, 0x611CCE3600000D80, 0xDA92286114894918, 0x36D949100036, 0x37B5FC7102964800, 0x6000006F695C6880, 0x6C000000000037B3, 0x6D9200004B6F5691, 0x4B, 0x264DA42400000000,
        // p = 12592530561211592160750079978298900605683991331427733283069727097740714382864092555385948729565169037765112351487500944445063519497018512388973205568307063039313302670019434462850057458587813410088324664505516051: 702 bits
    ];
    const NEG_INV_MOD: &'static [Word] = &[  // -1/p mod 2^(64*LIMBS)
        0x8A89EAC34457F5E5, 0xA6DEE06F4751C1EB, 0xE6A557E0642ACB45, 0x681EC38A841C3478, 0xF22AD035F2F00819, 0x2EE680A493ECCF6B, 0xF58B0303059E131F, 0x65162FB87DB16AB7, 0x8AAE6581FA357FD9, 0xE8A08B01D1ABDB8F, 0xE7FE7A1874568228,
    ];
    const MONTY_P: &'static [Word] = &[  // (2^(64*LIMBS))^2 mod p
        0x660B6A1652A7DC3F, 0xEBFFD293202D540A, 0x53F883FB95620072, 0x4DAC63A3CE161627, 0x4D02C46D6AA140E7, 0x4FB57BC035BCBD7D, 0x1384F18E73531B2F, 0x1AF9B9C49A8743B1, 0xDB928CD3529FB2E2, 0x8E405630A53CA953, 0x233B0FF3EF7EDAAF,
    ];
    const ORDER: &'static [Word] = &[  // cryptographic group order
        0xA803601F808400D, 0xA201F80900A203F0, 0xFF99C23600000D80, 0xDA9227FF94894917, 0x36D949100036, 0x37B5FC709F904800, 0x6000006F695C6880, 0x6C000000000037B3, 0x6D9200004B6F5691, 0x4B, 0x264DA42400000000,
        // n = 12592530561211592160750079978298900605683991331427733283069727097740714382864092555385948729565169037765108802891925056486517417549405236760067427991422332313091589068087756807384715849799175512253110979832332301: 702 bits
    ];
    const NEG_INV_ORD: &'static [Word] = &[  // -1/n mod 2^(64*LIMBS)
        0xF08C2BE8E8C1F13B, 0x4B6C46F11B61BD2B, 0xA2FB1E2F75145DFB, 0xA393828A78764B8C, 0xB0B2329DC65968AE, 0x6CED521F0A85820E, 0xA89E862E2E2B3F1E, 0x21F2B187B45C51B7, 0x720143B26B1DB7C0, 0xB5CAA1650F802D42, 0x4C4064969ED58E3,
    ];
    const MONTY_N: &'static [Word] = &[  // (2^(64*LIMBS))^2 mod n
        0xF6B8726D5E3AA644, 0xFBC708ECC7F0A599, 0xC0697C5B6372D0FF, 0x71395A6B7765B28E, 0x4D4E104E63631D8F, 0xCCC8BA9FDD61C162, 0x293E728D35DDEBB6, 0xC086F382AB75982D, 0x2F289E7DE1D804F, 0x9E33DEF16302B6BD, 0xEC855BFB5CE3D40,
    ];
    const SQRT_NEG_3: &'static [Word] = &[  // sqrt(-3) mod p
        0x5402400F0030004, 0x6C00F009006C01E0, 0xCF0F182400000D80, 0xD9B6C3CF1488DB63, 0x36D8DB600036, 0x37B51D9EDE4E4800, 0x6000006F687D9B00, 0x48000000000037B3, 0x6D9200004B6EBFB6, 0x4B, 0x264DA42400000000,
    ];
    const SVDW: &'static [Word] = &[  // (-1 + sqrt(-3))/2 mod p
        0x8A02D018006600B, 0x8701800900870300, 0x1815F32D00000D80, 0xDA2476181489123E, 0x36D912380036, 0x37B58D07F0724800, 0x6000006F68ED01C0, 0xDA000000000037B3, 0x6D9200004B6F0B23, 0x4B, 0x264DA42400000000,
    ];
    const ZETA: &'static [Word] = &[  // primitive cube root of unity, in absolute value
        0x0360090090036007, 0x1B009000001B0120, 0x4906DB0900000000, 0x006DB249000036DA, 0x0000000036D80000, 0x00006F6912240000, 0x00000000006F66C0, 0x9200000000000000, 0x0000000000004B6D, 0x0000000000000000, 0x0000000000000000,
        // ζ = 258899009959721652783083199501488472434784819544536546309011819584026191005225192640385163762855198250653594309336114225459842627270043101051930138664325308423 mod p
    ];
    const THETA: &'static [Word] = &[  // (-1/4)^((p+5)/24)
        0xF9C538B896B77951, 0xC0740AFD47E4477E, 0xFD8C0A72295FFE99, 0xECBFECF16E199230, 0xB5037DCBE83691A7, 0xDAD487804D0D07F9, 0x7B286CF12E28E445, 0x19021FD271A2B0A2, 0x1F3B92DDDA12CE3D, 0xFEB336B257CB361A, 0x0A2922538EB9D300,
        // θ = 3340409862873443274596237320573315085135645766272643868074202307832208091312821575265950567802432905150294842069764483437487758832820905031016101513614547911371851554020382743187032719607107214226519531290327377 mod p
    ];
    const OMEGA: &'static [Word] = &[  // order of optimal pairing
        0x00C000000000C004, 0x0000000000000000, 0x0001860000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
        // ω = |6u + 2| = 145916323471117347353455893698393696736491500619218948
    ];
    const TRIPLES: Word = 186;  // number of precomputed optimal pairing triples
}

pub struct BN766Param;

impl BNParam for BN766Param {
    const U: &'static [Word] = &[  // the BN curve selector in absolute value
        0x0000000000000801, 0x0000000000000000, 0x4800000040000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
        // u = -1765434863442879374161541504828077387707858223669492844545
    ];
    const LIMBS: usize = 12;
    const MODULUS: &'static [Word] = &[  // base finite field modulus
        0x240D821027013, 0x0, 0x442101380000000, 0x5116CA525E, 0x4000000000000000, 0x78996C929360A208, 0x4464D12, 0xB2001201B0000000, 0x6718445E68403CC5, 0x24000000000019A3, 0x11600000A2000000, 0x39AA4000CD080001,
        // p = 349711001999499154676386624553441220610761508023560840045298324733086271833497305680781400771995747133755588212644613234856175917043854660858604188057934672334049638135332951429755390842940121758881785126832127589864525621329293331: 766 bits
    ];
    const NEG_INV_MOD: &'static [Word] = &[  // -1/p mod 2^(64*LIMBS)
        0xCDAF8043A0C525E5, 0xED5E9DA32E7C38DB, 0x1F701FECA852DA25, 0xB1DCCC56509F8596, 0xE9C4FFD651D24808, 0x56D6011E21691A28, 0x142DC05D035400D3, 0x9C925810E0ED2CAB, 0xA0D339C4D65F532C, 0x842CB2FA8B92B067, 0xD7F793ABD7A5A7CE, 0x7A19DF8ABB39C4CE,
    ];
    const MONTY_P: &'static [Word] = &[  // (2^(64*LIMBS))^2 mod p
        0xE1A66C324F546628, 0x1B9B39E585B59694, 0x99019B52C9CB1098, 0xFFE5F03E74F63F17, 0x333D4F00CF7A6BC2, 0x54D2C263C886FC37, 0x5A08B37C128E365D, 0x616F164271EEB2C2, 0x971D190CE3225860, 0x5902667FA15A310E, 0xF97E2F4724038FFC, 0x39193E63A38C3270,
    ];
    const ORDER: &'static [Word] = &[  // cryptographic group order
        0x240D81F82100D, 0x0, 0xA441F81080000000, 0x5116CA375A, 0xE000000000000000, 0xFF196C91BB60A207, 0x4464D11, 0xB2001201B0000000, 0x6718445E68403CC5, 0x24000000000019A3, 0x11600000A2000000, 0x39AA4000CD080001,
        // n = 349711001999499154676386624553441220610761508023560840045298324733086271833497305680781400771995747133755588212644594534294633559574992503124566502098173859390604317584805953182279653533410182587108813698625448198528723888111751181: 766 bits
    ];
    const NEG_INV_ORD: &'static [Word] = &[  // -1/n mod 2^(64*LIMBS)
        0x37FD7A4522FF413B, 0x36D9EE52B06452AF, 0x6FEAF464DE7E4E6A, 0x3500634424B16F48, 0x753CB754AD3A64E7, 0xDE93A88E7AE55834, 0xF61270196C86D3E5, 0x5576907F96A2FAF7, 0xC7DDD790A578D420, 0x1CD9F09FD8862CC1, 0x8DD7440E2B5C531, 0x956DFAEF7E1B459D,
    ];
    const MONTY_N: &'static [Word] = &[  // (2^(64*LIMBS))^2 mod n
        0xB56213166833C120, 0x55D2679633E5367D, 0x78B9F074DFC054EB, 0x5B69503983E7C641, 0x3FD43E6430FE3EC2, 0xDDF1D9748F48FECC, 0x23DFB4EE0FAA44B4, 0x9082E75E74B6C530, 0x5347F67A8359C6A5, 0x411604AD9ED98D4F, 0x3635D9D3E850D236, 0x1E5D9F750933844D,
    ];
    const SQRT_NEG_3: &'static [Word] = &[  // sqrt(-3) mod p
        0x240900F00C004, 0x0, 0xCD80F00600000000, 0x510F310E4E, 0xC000000000000000, 0xC698F30873606C03, 0x44608B4, 0xCC00120120000000, 0x9A10445C45803CC3, 0x24000000000019A2, 0x11600000A2000000, 0x39AA4000CD080001,
    ];
    const SVDW: &'static [Word] = &[  // (-1 + sqrt(-3))/2 mod p
        0x240B41801980B, 0x0, 0x68E1800CC0000000, 0x5112FDB056, 0x0, 0x9F992FCD83608706, 0x4462AE3, 0xBF00120168000000, 0x94445D56E03CC4, 0x24000000000019A3, 0x11600000A2000000, 0x39AA4000CD080001,
    ];
    const ZETA: &'static [Word] = &[  // primitive cube root of unity, in absolute value
        0x000000240900D807, 0x0000000000000000, 0x9B609006C0000000, 0x0000000003CCA207, 0x4000000000000000, 0xD9003CC510001B02, 0x000000000000222E, 0xF300000048000000, 0x6684000111600000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
        // ζ = 99043869938511059190116616665375868370544099398376015157593067138836353260557469567142341768170925789290377604142813303692853404556309896645382660936366386375485716588189703 mod p
    ];
    const THETA: &'static [Word] = &[  // (-1/4)^((p+5)/24)
        0x776B50417AE1271E, 0x34D15830C8B433F4, 0x02480677E05652DC, 0x1DF4DDBBA5C373A1, 0xF3EF7D5D2FFCC217, 0x81360A05723FD1F1, 0xAEA591048D30242C, 0x9155991C645B8C53, 0xA90BEC568F0790EA, 0xA40039C4E4633099, 0xD04FC3702168DB32, 0x2FC8E54C2B7B192C,
        // θ = 289791746298234983467746897597944544926834647467620723962444874479607077426201883735204832130722017138060189122233916309336627195198832704383025158744347933376967360935956782512736567920335125957974026117417446247854309682836481822 mod p
    ];
    const OMEGA: &'static [Word] = &[  // order of optimal pairing
        0x0000000000003004, 0x0000000000000000, 0xB000000180000000, 0x0000000000000001, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000,
        // ω = |6u + 2| = 10592609180657276244969249028968464326247149342016957067268
    ];
    const TRIPLES: Word = 202;  // number of precomputed optimal pairing triples
}
