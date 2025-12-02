use bn_curves::bnfp::BNFp;
use bn_curves::bnfp2::BNFp2;
use bn_curves::bnpairing::BNPairing;
use bn_curves::bnparam::{BNParam, BN062Param, BN126Param, BN190Param, BN254Param, BN318Param, BN382Param, BN446Param, BN510Param, BN574Param, BN638Param, BN702Param, BN766Param};
use bn_curves::bnpoint::BNPoint;
use bn_curves::bnpoint2::BNPoint2;
use crypto_bigint::{NonZero, Random, RandomMod, Uint, Zero};
use crypto_bigint::subtle::{Choice, ConstantTimeEq};
use rand::prelude::ThreadRng;
use std::marker::PhantomData;
use std::time::SystemTime;

/// The Boneh-Freeman-Katz-Waters NCS&#x2081; scheme for signing a linear subspace.
///
/// Reference:
///
/// * D. Boneh, D. Freeman, J. Katz, B. Waters,
/// "Signing a Linear Subspace: Signature Schemes for Network Coding."
/// LNCS 5443, pp. 68--87, 2009.
/// International Conference on Practice and Theory in Public Key Cryptography -- PKC 2009
/// https://doi.org/10.1007/978-3-642-00468-1_5
#[allow(non_camel_case_types)]
pub struct NCS1<BN: BNParam, const LIMBS: usize>(
    #[doc(hidden)]
    pub PhantomData<BN>,
);

impl<BN: BNParam, const LIMBS: usize> NCS1<BN, LIMBS> {
    /// Given a pairing friendly elliptic curve with groups
    /// <b>G</b><i>&#x2081;</i>, <b>G</b><i>&#x2082;</i> and <b>G</b><i><sub>T</sub></i>,
    /// choose generators <i>P</i> &in; <b>G</b><i>&#x2081;</i> and <i>Q</i> &in; <b>G</b><i>&#x2082;</i>.
    ///
    /// Choose a random value <i>sk</i> &#8668; &Zopf;<i>&#x2099;</i> where &Zopf;<i>&#x2099;</i>
    /// is the scalar field of the elliptic curve, and set <i>R</i> &larr; &lbrack;<i>sk</i>&rbrack;<i>Q</i>.
    ///
    /// Output the public key <i>pk</i> &#x2254; (<i>P, Q, R</i>) &in;
    /// <b>G</b><i>&#x2081;</i> &times; <b>G</b><i>&#x2082;</i> &times; <b>G</b><i>&#x2082;</i>
    /// and the secret key <i>sk</i>.
    #[allow(non_snake_case)]
    pub fn setup(rng: &mut ThreadRng)
                 -> ((BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNPoint2<BN, LIMBS>), Uint<LIMBS>) {
        /*
        // default generators:
        let P = BNPoint::gen();
        let Q = BNPoint2::gen();
        // */
        //*
        // individualized generators:
        let P = BNPoint::point_factory(BNFp::random(rng));
        let Q = BNPoint2::point_factory(BNFp2::random(rng)).elim_cof();
        // */
        let n: Uint<LIMBS> = Uint::from_words(BN::ORDER.try_into().unwrap());
        let sk = Uint::random_mod(rng, &NonZero::new(n).unwrap());
        let R = sk*Q;
        let pk = (P, Q, R);
        (pk, sk)
    }

    /// Given a secret key <i>sk</i>, the point <i>P &in; <b>G</b>&#x2081;</i> from the public key <i>pk</i>,
    /// an identifier <i>id</i>, an <i>index</i> corresponding to the row being signed, and a message <i>m</i>,
    /// output the signature as <i>&sigma; := &lbrack;sk&rbrack;(H(id, index) + &lbrack;m&rbrack;P)</i>,
    /// where <i>H(id, index)</i> hashes to the group <i><b>G</b>&#x2081;</i>.
    #[allow(non_snake_case)]
    pub fn sign(sk: Uint<LIMBS>, pk: (BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNPoint2<BN, LIMBS>),
                id: String, index: usize, m: Uint<LIMBS>) -> BNPoint<BN, LIMBS> {
        let P = pk.0;
        let data = [id.as_bytes(), index.to_string().as_bytes()].concat();
        let sigma = sk*(BNPoint::shake256(&*data) + m*P);
        sigma
    }

    /// Given a public key <i>pk = (P, Q, R)</i>,
    /// an identifier <i>id</i>, an <i>index</i> corresponding to the row being signed, a message <i>m</i>,
    /// and a signature <i>&sigma;</i>, calculate <i>left := e(&sigma;, Q)</i>
    /// and <i>right := e(H(id, index) + &lbrack;m&rbrack;P, R)</i>, and output
    /// <i>true</i> if <i>left = right</i>, or <i>false</i> otherwise.
    #[allow(non_snake_case)]
    pub fn verify(pk: (BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNPoint2<BN, LIMBS>),
                  id: String, index: usize, m: Uint<LIMBS>, sigma: BNPoint<BN, LIMBS>) -> Choice {
        let P = pk.0;
        let Q = pk.1;
        let R = pk.2;
        let data = [id.as_bytes(), index.to_string().as_bytes()].concat();
        let left = BNPairing::opt(&Q, &sigma);
        let right = BNPairing::opt(&R, &(BNPoint::shake256(&*data) + m*P));
        left.ct_eq(&right)
    }

    /// Given a vector of weights <i>(weight&#x1D62;)</i>
    /// and a vector of signatures <i>(&sigma;&#x1D62;)</i>, each of length <i>k</i>,
    /// calculate the aggregate signature
    /// <i>S := &Sigma;&#x1D62;&#x208C;&#x2080;&#x1D4F; &lbrack;w&#x1D62;&rbrack;&sigma;&#x1D62;</i>.
    #[allow(non_snake_case)]
    pub fn combine(weight: &[Uint<LIMBS>], sigma: &[BNPoint<BN, LIMBS>]) -> BNPoint<BN, LIMBS> {
        let mut S: BNPoint<BN, LIMBS> = BNPoint::zero();
        for i in 0..weight.len() {
            S += weight[i]*sigma[i];
        }
        S
    }

    /// Given a public key <i>pk = (P, Q, R)</i>, an identifier <i>id</i>,
    /// a vector of weights <i>(weight&#x1D62;)</i> of length <i>k</i>, a message <i>m</i>,
    /// and an aggregate_signature <i>S</i>, verify that the message corresponds
    /// to the weighted average of signed original messages by calculating
    /// <i>left := e(S, Q)</i> and
    /// <i>right := e(&Sigma;&#x1D62;&#x208C;&#x2080;&#x1D4F; &lbrack;w&#x1D62;&rbrack;&#x1D62;H(id, i) + &lbrack;m&rbrack;P, R)</i>,
    /// and output <i>true</i> if <i>left = right</i>, or <i>false</i> otherwise.
    #[allow(non_snake_case)]
    pub fn verify_aggregate(pk: (BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNPoint2<BN, LIMBS>),
                            id: String, weight: &[Uint<LIMBS>], m: Uint<LIMBS>, S: BNPoint<BN, LIMBS>) -> Choice {
        let P = pk.0;
        let Q = pk.1;
        let R = pk.2;
        let mut T: BNPoint<BN, LIMBS> = m*P;
        for i in 0..weight.len() {
            let data = [id.as_bytes(), i.to_string().as_bytes()].concat();
            T += weight[i]*BNPoint::shake256(&*data);
        }
        let left = BNPairing::opt(&Q, &S);
        let right = BNPairing::opt(&R, &T);
        left.ct_eq(&right)
    }
}

/// A simple driver for a few benchmarks on the BN bn_curves
#[allow(non_snake_case)]
fn main() {
    // choose a target parameter set:
    //type BN = BN062Param;
    //type BN = BN126Param;
    //type BN = BN190Param;
    //type BN = BN254Param;
    //type BN = BN318Param;
    type BN = BN382Param;
    //type BN = BN446Param;
    //type BN = BN510Param;
    //type BN = BN574Param;
    //type BN = BN638Param;
    //type BN = BN702Param;
    //type BN = BN766Param;

    const LIMBS: usize = BN::LIMBS;
    println!("Showcasing NCS1 over BN{:03}...", 64*LIMBS - 2);
    let mut rng = rand::rng();
    let now = SystemTime::now();

    // setup:
    let (pk, sk) = NCS1::<BN, LIMBS>::setup(&mut rng);
    println!("    pk: {:?}", pk);
    println!("    sk: {}", sk.to_string_radix_vartime(10));

    // sign:
    let sigma = NCS1::<BN, LIMBS>::sign(sk, pk, "id".to_string(), 0, Uint::from_word(31415926536));
    println!("    sign: {}", sigma);

    // verify:
    let ok = NCS1::<BN, LIMBS>::verify(pk, "id".to_string(), 0, Uint::from_word(31415926536), sigma);
    println!("    verify 1: {}  (should be true)", bool::from(ok));
    assert!(bool::from(ok));
    let ok = NCS1::<BN, LIMBS>::verify(pk, "id".to_string(), 0, Uint::from_word(27182818285), sigma);
    println!("    verify 0: {} (should be false)", bool::from(ok));
    assert!(!bool::from(ok));

    let w = [Uint::from_word(34), Uint::from_word(55)];
    let m = [Uint::from_word(27182818285), Uint::from_word(31415926536)];
    let tau0 = NCS1::<BN, LIMBS>::sign(sk, pk, "id".to_string(), 0, m[0]);
    let tau1 = NCS1::<BN, LIMBS>::sign(sk, pk, "id".to_string(), 1, m[1]);
    let S = NCS1::<BN, LIMBS>::combine(&w, &[tau0, tau1]);
    let M = w[0]*m[0] + w[1]*m[1];
    println!("    aggregate signature: {}", S);

    let ok = NCS1::<BN, LIMBS>::verify_aggregate(pk, "id".to_string(), &w, M, S);
    println!("    verify_aggregate 1: {}  (should be true)", bool::from(ok));
    assert!(bool::from(ok));
    let ok = NCS1::<BN, LIMBS>::verify_aggregate(pk, "id".to_string(), &w, Uint::ZERO, S);
    println!("    verify_aggregate 0: {} (should be false)", bool::from(ok));
    assert!(!bool::from(ok));

    match now.elapsed() {
        Ok(elapsed) => {
            println!("Total elapsed time: {} ms.", (elapsed.as_micros() as f64)/1000.0);
        }
        Err(e) => {
            println!("Error: {e:?}");
        }
    }
}
