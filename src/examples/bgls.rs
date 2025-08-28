#[cfg(not(any(target_pointer_width = "64")))]
compile_error!("this crate requires 64-bit limbs");

use bn_curves::bnfp::BNFp;
use bn_curves::bnfp2::BNFp2;
use bn_curves::bnfp12::BNFp12;
use bn_curves::bnpairing::BNPairing;
use bn_curves::bnparam::{BNParam, BN062Param, BN126Param, BN190Param, BN254Param, BN318Param, BN382Param, BN446Param, BN510Param, BN574Param, BN638Param, BN702Param, BN766Param};
use bn_curves::bnpoint::BNPoint;
use bn_curves::bnpoint2::BNPoint2;
use bn_curves::bnzn::BNZn;
use bn_curves::traits::One;
use crypto_bigint::{Random, Zero};
use crypto_bigint::subtle::{Choice, ConditionallySelectable, ConstantTimeEq};
use crypto_bigint::rand_core::RngCore;
use std::marker::PhantomData;
use std::time::SystemTime;

/// The Boneh-Gentry-Lynn-Shacham (BGLS) aggregate signature scheme over BN curves.
///
/// NB: The original description assumed Type 2 pairings, which Chatterjee and Menezes argue
/// to be just an inefficient form of Type 3 pairings.  Indeed, it is possible to adapt both
/// BGLS protocols (i.e. the aggregate signature scheme and the verifiably encrypted
/// signature scheme alike) and their security proofs under the q-SDH assumption to Type 3 pairings,
/// and this implementation follows this more natural and more efficient approach.
///
/// References:
///
/// * D. Boneh, C. Gentry, B. Lynn, H. Shacham,
/// "Aggregate and Verifiably Encrypted Signatures from Bilinear Maps."
/// Advances in Cryptology -- EUROCRYPT 2003, LNCS 2656, pp. 416--432, Springer, 2003.
/// https://doi.org/10.1007/11593447_28
///
/// * S. Chatterjee, A. Menezes,
/// "On cryptographic protocols employing asymmetric pairings -- The role of &Psi; revisited."
/// Discrete Applied Mathematics, vol. 159, no. 13, pp. 1311--1322, ScienceDirect, 2011.
/// https://doi.org/10.1016/j.dam.2011.04.021
#[allow(non_camel_case_types)]
pub struct BGLS<BN: BNParam, const LIMBS: usize>(
    #[doc(hidden)]
    pub PhantomData<BN>,
);

impl<BN: BNParam, const LIMBS: usize> BGLS<BN, LIMBS> {

    /// Given a pairing-friendly elliptic curve with groups
    /// <b>G</b><i>&#x2081;</i>, <b>G</b><i>&#x2082;</i> and <b>G</b><i><sub>T</sub></i>,
    /// choose and output public generators <i>P</i> &in; <b>G</b><i>&#x2081;</i>
    /// and <i>Q</i> &in; <b>G</b><i>&#x2082;</i>.
    #[allow(non_snake_case)]
    pub fn setup() -> (BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>) {
        /*
        // default generators:
        let P = BNPoint::default_generator();
        let Q = BNPoint2::default_generator();
        // */
        //*
        // pick individualized generators:
        let BGLS_ID = "BGLS ID".to_string().into_bytes().to_vec();  // or pick them randomly
        let P = BNPoint::point_factory(BNFp::shake256(&BGLS_ID));
        let Q = BNPoint2::point_factory(BNFp2::shake256(&BGLS_ID)).elim_cof();
        // */
        (P, Q)
    }

    /// A sample hash function <i>H</i> ∶ <b>G</b><i>&#x2082;</i> &times; {0,1}&ast; → <b>G</b><i>&#x2081;</i>.
    #[allow(non_snake_case)]
    pub fn H(V: &BNPoint2<BN, LIMBS>, m: &[u8]) -> BNPoint<BN, LIMBS> {
        let mut bytes: Vec<u8> = m.to_vec();
        let mut nonce: Vec<u8> = V.to_bytes();
        bytes.append(&mut nonce);
        let mut sep: Vec<u8> = "BGLS H".to_string().into_bytes().to_vec();  // domain separation string
        bytes.append(&mut sep);
        BNPoint::point_factory(BNFp::shake256(bytes.as_slice()))
    }

    /// For each user, pick a random <i>s</i> &#8668; &Zopf;<i>&#x2099;&ast;</i>
    /// and compute <i>V</i> &#x2254; &lbrack;<i>s</i>&rbrack;<i>Q</i>.
    /// The user's public key is <i>V</i> &in; <b>G</b><i>&#x2082;</i>
    /// and their private key is <i>s</i> &in; &Zopf;<i>&#x2099;&ast;</i>.
    #[allow(non_snake_case)]
    pub fn keygen<R: RngCore + ?Sized>(rng: &mut R, Q: &BNPoint2<BN, LIMBS>)
            -> (BNPoint2<BN, LIMBS>, BNZn<BN, LIMBS>) {
        let s = BNZn::random(rng);
        let V = s*(*Q);
        (V, s)
    }

    /// Given a user's key pair (<i>V</i>, <i>s</i>) and a message <i>m</i>,
    /// compute <i>M</i> &larr; <i>H</i>(<i>V</i>, <i>m</i>) and
    /// generate a BGLS signature <i>&sigma;</i> &larr; &lbrack;<i>s</i>&rbrack;<i>M</i>
    /// for <i>m</i> verifiable under <i>V</i>.
    #[allow(non_snake_case)]
    pub fn sign(V: &BNPoint2<BN, LIMBS>, s: &BNZn<BN, LIMBS>, m: &[u8]) -> BNPoint<BN, LIMBS> {
        // hash M ← H(V, m) ∈ G_1:
        let M = BGLS::H(&V, m);
        // compute the signature σ ← [s]M:
        let sigma = (*s)*M;
        sigma
    }

    /// Given a public key <i>V</i>, a message <i>m</i>, and a signature <i>&sigma;</i>,
    /// compute <i>M</i> &larr; <i>H</i>(<i>V</i>, <i>m</i>) and accept iff
    /// e(<i>&sigma;</i>, <i>Q</i>) = e(<i>M</i>, <i>V</i>).
    #[allow(non_snake_case)]
    pub fn verify(Q: &BNPoint2<BN, LIMBS>, V: &BNPoint2<BN, LIMBS>,
            m: &[u8], sigma: &BNPoint<BN, LIMBS>) -> Choice {
        // hash M ← H(V, m) ∈ G_1:
        let M = BGLS::H(&V, m);
        // accept iff e(σ, Q) = e(M, V)
        BNPairing::opt(Q, sigma).ct_eq(&BNPairing::opt(V, &M))
    }

    /// Let &lbrack;<i>&sigma;&#x1D62;</i> | <i>0&leq;i&lt;k</i>&rbrack; be a set of signatures created for
    /// corresponding messages &lbrack;<i>m&#x1D62;</i> | <i>0&leq;i&lt;k</i>&rbrack; and verifiable under
    /// matching public keys &lbrack;<i>V&#x1D62;</i> | <i>0&leq;i&lt;k</i>&rbrack;.
    /// Their aggregate signature is <i>&sigma;</i> &larr; &Sigma;<sub><i>0&leq;i&lt;k</i></sub>
    /// <i>&sigma;&#x1D62;</i> &in; <b>G</b><i>&#x2081;</i>.
    #[allow(non_snake_case)]
    pub fn aggregate(sigma: &[BNPoint<BN, LIMBS>]) -> BNPoint<BN, LIMBS> {
        let mut Sigma = BNPoint::zero();
        for sig in sigma {
            Sigma += *sig;
        }
        Sigma
    }

    /// Let &lbrack;<i>m&#x1D62;</i> | <i>0&leq;i&lt;k</i>&rbrack; be a set of messages
    /// signed into an aggregated signature <i>&Sigma;</i>, and let
    /// &lbrack;<i>V&#x1D62;</i> | <i>0&leq;i&lt;k</i>&rbrack; be a set of corresponding public keys.
    /// Compute <i>M&#x1D62;</i> &larr; <i>H</i>(<i>V&#x1D62;</i>, <i>m&#x1D62;</i>) for all <i>0&leq;i&lt;k</i>
    /// and accept iff e(<i>&Sigma;</i>, <i>Q</i>) =
    /// &Pi;<sub><i>0&leq;i&lt;k</i></sub> e(<i>M&#x1D62;</i>, <i>V&#x1D62;</i>).
    #[allow(non_snake_case)]
    pub fn verify_aggregate(Q: &BNPoint2<BN, LIMBS>, V: &[BNPoint2<BN, LIMBS>],
            Sigma: &BNPoint<BN, LIMBS>, m: &Vec<Vec<u8>>) -> Choice {
        if m.len() != V.len() {
            return Choice::from(0);  // impossible to verify lists of unequal lengths
        }
        let mut rhs = BNFp12::<BN, LIMBS>::one();
        for i in 0..m.len() {
            let Mi = BGLS::H(&V[i], &m[i]);
            let ei = BNPairing::opt(&V[i], &Mi);
            rhs *= ei;
        }
        BNPairing::opt(Q, Sigma).ct_eq(&rhs)
    }

    /// Given the public generators <i>P</i> &in; <b>G</b><i>&#x2081;</i> and
    /// <i>Q</i> &in; <b>G</b><i>&#x2082;</i>,
    /// pick a random <i>s<sub>adj</sub></i> &#8668; &Zopf;<i>&#x2099;&ast;</i>
    /// and compute <i>P<sub>adj</sub></i> &larr; &lbrack;<i>s<sub>adj</sub></i>&thinsp;&rbrack;<i>P</i>
    /// and <i>Q<sub>adj</sub></i> &larr; &lbrack;<i>s<sub>adj</sub></i>&thinsp;&rbrack;<i>Q</i>.
    /// The adjudicator's public keys are <i>P<sub>adj</sub></i> &in; <b>G</b><i>&#x2081;</i> and
    /// <i>Q<sub>adj</sub></i> &in; <b>G</b><i>&#x2082;</i>,
    /// and their private key is <i>s<sub>adj</sub></i> &in; &Zopf;<i>&#x2099;&ast;</i>.
    #[allow(non_snake_case)]
    pub fn ve_keygen<R: RngCore + ?Sized>(rng: &mut R,
            P: &BNPoint<BN, LIMBS>, Q: &BNPoint2<BN, LIMBS>)
            -> (BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNZn<BN, LIMBS>) {
        let s_adj = BNZn::random(rng);
        let P_adj = s_adj*(*P);
        let Q_adj = s_adj*(*Q);
        (P_adj, Q_adj, s_adj)
    }

    /// Given the public generators <i>P</i> &in; <b>G</b><i>&#x2081;</i> and
    /// <i>Q</i> &in; <b>G</b><i>&#x2082;</i>,
    /// validate the adjudicator's public keys <i>P<sub>adj</sub></i> &in; <b>G</b><i>&#x2081;</i>
    /// and <i>Q<sub>adj</sub></i> &in; <b>G</b><i>&#x2082;</i> for consistency by checking that
    /// e(<i>P<sub>adj</sub></i>&thinsp;, <i>Q</i>) = e(<i>P</i>, <i>Q<sub>adj</sub></i>&thinsp;).
    #[allow(non_snake_case)]
    pub fn ve_validate(P: &BNPoint<BN, LIMBS>, Q: &BNPoint2<BN, LIMBS>,
            P_adj: &BNPoint<BN, LIMBS>, Q_adj: &BNPoint2<BN, LIMBS>) -> Choice {
        BNPairing::opt(&Q_adj, &P).ct_eq(&BNPairing::opt(&Q, &P_adj))
    }

    /// Given the public generator <i>P</i> &in; <b>G</b><i>&#x2081;</i>,
    /// a user's key pair (<i>V</i>, <i>s</i>) &in; <b>G</b><i>&#x2082;</i> &times; &Zopf;<i>&#x2099;&ast;</i>,
    /// an adjudicator's public key <i>P<sub>adj</sub></i> &in; <b>G</b><i>&#x2081;</i>,
    /// and a message <i>m</i> &in; {0, 1}&ast;,
    /// compute <i>M</i> &larr; <i>H</i>(<i>V</i>, <i>m</i>) &in; <b>G</b><i>&#x2081;</i> and
    /// <i>&sigma;</i> &larr; &lbrack;<i>s</i>&rbrack;<i>M</i> &in; <b>G</b><i>&#x2081;</i>.
    /// Select <i>r</i> &#8668; &Zopf;<i>&#x2099;&ast;</i> at random, set
    /// <i>&mu;</i> &larr; &lbrack;<i>r</i>&rbrack;<i>P</i> &in; <b>G</b><i>&#x2081;</i> and
    /// <i>&sigma;<sub>adj</sub></i> &larr; &lbrack;<i>r</i>&rbrack;<i>P_adj</i> &in; <b>G</b><i>&#x2081;</i>,
    /// and aggregate <i>&omega;</i> &larr; <i>&sigma;</i> + <i>&sigma;<sub>adj</sub></i>
    /// &in; <b>G</b><i>&#x2081;</i>.  The verifiably encrypted signature is the pair
    /// (<i>&omega;</i>, <i>&mu;</i>) &in; <b>G</b><i>&#x2081;</i> &times; <b>G</b><i>&#x2081;</i>.
    #[allow(non_snake_case)]
    pub fn ve_sign<R: RngCore + ?Sized>(rng: &mut R,
            P: &BNPoint<BN, LIMBS>,
            V: &BNPoint2<BN, LIMBS>, s: &BNZn<BN, LIMBS>,
            P_adj: &BNPoint<BN, LIMBS>,
            m: &[u8])
            -> (BNPoint<BN, LIMBS>, BNPoint<BN, LIMBS>) {
        let M = BGLS::H(&V, m);
        let sigma = (*s)*M;
        let r = BNZn::random(rng);
        let mu = r*(*P);
        let sigma_adj = r*(*P_adj);
        let omega = sigma + sigma_adj;
        (omega, mu)
    }

    /// Given the public generator <i>Q</i> &in; <b>G</b><i>&#x2082;</i>,
    /// a user's public key <i>V</i> &in; <b>G</b><i>&#x2082;</i>,
    /// the adjudicator's public key <i>Q<sub>adj</sub></i> &in; <b>G</b><i>&#x2082;</i>,
    /// and a verifiably encrypted signature <i>&Sigma;</i> &#x2254;
    /// (<i>&omega;</i>, <i>&mu;</i>) &in; <b>G</b><i>&#x2081;</i> &times; <b>G</b><i>&#x2081;</i>
    /// on a message <i>m</i> &in; {0, 1}&ast;,
    /// compute <i>M</i> &larr; <i>H</i>(<i>V</i>, <i>m</i>) &in; <b>G</b><i>&#x2081;</i> and accept iff
    /// e(<i>&omega;</i>, <i>Q</i>) = e(<i>M</i>, <i>V</i>) &middot; e(<i>&mu;</i>, <i>Q<sub>adj</sub></i>&thinsp;).
    #[allow(non_snake_case)]
    pub fn ve_verify(Q: &BNPoint2<BN, LIMBS>, V: &BNPoint2<BN, LIMBS>, Q_adj: &BNPoint2<BN, LIMBS>,
            Sigma: &(BNPoint<BN, LIMBS>, BNPoint<BN, LIMBS>), m: &[u8]) -> Choice {
        let omega = &Sigma.0;
        let mu = &Sigma.1;
        let M = BGLS::H(&V, m);
        let rhs = BNPairing::opt(V, &M)*BNPairing::opt(Q_adj, &mu);
        BNPairing::opt(Q, &omega).ct_eq(&rhs)
    }

    /// Given the public generator <i>Q</i> &in; <b>G</b><i>&#x2082;</i>,
    /// a user's certified public key <i>V</i> &in; <b>G</b><i>&#x2082;</i>,
    /// the adjudicator’s public key <i>Q<sub>adj</sub></i> &in; <b>G</b><i>&#x2082;</i>
    /// and corresponding private key <i>s<sub>adj</sub></i> &in; &Zopf;<i>&#x2099;&ast;</i>,
    /// and a verifiably encrypted signature <i>&Sigma;</i> &#x2254;
    /// (<i>&omega;</i>, <i>&mu;</i>) &in; <b>G</b><i>&#x2081;</i> &times; <b>G</b><i>&#x2081;</i>
    /// on some message <i>m</i> &in; {0, 1}&ast;,
    /// ensure that the verifiably encrypted signature is valid, and if so,
    /// output the user's signature <i>&sigma;</i> &#x2254;
    /// <i>&omega;</i> - &lbrack;<i>s<sub>adj</sub></i>&thinsp;&rbrack;<i>&mu;</i>
    /// &in; <b>G</b><i>&#x2081;</i>.
    #[allow(non_snake_case)]
    pub fn ve_adjudicate(Q: &BNPoint2<BN, LIMBS>, V: &BNPoint2<BN, LIMBS>,
            Q_adj: &BNPoint2<BN, LIMBS>, s_adj: &BNZn<BN, LIMBS>,
            Sigma: &(BNPoint<BN, LIMBS>, BNPoint<BN, LIMBS>), m: &[u8],
            sigma: &mut BNPoint<BN, LIMBS>) -> Choice {
        let ok = BGLS::ve_verify(Q, V, Q_adj, Sigma, m);
        let omega = &Sigma.0;
        let mu = &Sigma.1;
        let adj = (*omega) - (*s_adj)*(*mu);
        sigma.conditional_assign(&adj, ok);
        ok
    }
}

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
    println!("Showcasing BGLS identity-based signatures over BN{:03}...", 64*LIMBS - 2);

    //let mut rng: SmallRng = SmallRng::from_seed([0; 32]);
    let mut rng = rand::rng();
    let now = SystemTime::now();

    // ---- BGLS aggregate signatures ----

    // setup:
    println!("setting up...");
    let (P, Q) = BGLS::<BN, LIMBS>::setup();
    //println!("    P: {:?}", P);
    //println!("    Q: {:?}", Q);

    // keygen:
    const KEYPAIRS: usize = 20;
    println!("generating {} key pair(s)...", KEYPAIRS);
    let mut V: Vec<BNPoint2<BN, LIMBS>> = Vec::with_capacity(KEYPAIRS);
    let mut s: Vec<BNZn<BN, LIMBS>> = Vec::with_capacity(KEYPAIRS);
    for _i in 0..KEYPAIRS {
        let pair = BGLS::<BN, LIMBS>::keygen(&mut rng, &Q);
        V.push(pair.0);
        //println!("    V_{}: {:?}", _i, V[_i]);
        s.push(pair.1);
        //println!("    s_{}: {:?}", _i, s[_i]);
    }

    // sign:
    println!("signing {} sample message(s)...", KEYPAIRS);
    let mut m: Vec<Vec<u8>> = Vec::with_capacity(KEYPAIRS);
    let mut sigma: Vec<BNPoint<BN, LIMBS>> = Vec::with_capacity(KEYPAIRS);
    for i in 0..KEYPAIRS {
        m.push(("sample message #".to_owned() + &i.to_string()).as_bytes().to_vec());
        //println!("    m_{}: {:?}", i, m[i]);
        sigma.push(BGLS::<BN, LIMBS>::sign(&V[i], &s[i], &m[i]));
        //println!("    sigma_{}: {:?}", i, sigma[i]);
    }

    // verify individually:
    println!("verifying {} signatures individually...", KEYPAIRS);
    let mut x: Vec<Vec<u8>> = Vec::with_capacity(KEYPAIRS);
    for i in 0..KEYPAIRS {
        x.push(("wrong message #".to_owned() + &i.to_string()).as_bytes().to_vec());
        let ok = BGLS::<BN, LIMBS>::verify(&Q, &V[i], &m[i], &sigma[i]);
        println!("    verify 1: {}  (should be true)", bool::from(ok));
        assert!(bool::from(ok));
        let ok = BGLS::<BN, LIMBS>::verify(&Q, &V[i], &x[i], &sigma[i]);
        println!("    verify 0: {} (should be false)", bool::from(ok));
        assert!(!bool::from(ok));
    }

    // aggregate:
    println!("aggregating {} signatures...", KEYPAIRS);
    let Sigma = BGLS::<BN, LIMBS>::aggregate(&sigma);
    //println!("    Sigma: {:?}", Sigma);

    // verify aggregate:
    println!("verifying aggregate...");
    let ok = BGLS::<BN, LIMBS>::verify_aggregate(&Q, &V, &Sigma, &m);
    println!("    verify 1: {}  (should be true)", bool::from(ok));
    assert!(bool::from(ok));
    let ok = BGLS::<BN, LIMBS>::verify_aggregate(&Q, &V, &Sigma, &x);
    println!("    verify 0: {} (should be false)", bool::from(ok));
    assert!(!bool::from(ok));

    // ---- BGLS verifiably encrypted signatures ----

    // generate the adjudicator's keys:
    println!("generating adjudicator's keys...");
    let (P_adj, Q_adj, s_adj) = BGLS::<BN, LIMBS>::ve_keygen(&mut rng, &P, &Q);
    //println!("    P_adj: {:?}", P_adj);
    //println!("    Q_adj: {:?}", Q_adj);
    println!("    s_adj: {:?}", s_adj);

    // validate the adjudicator's keys:
    println!("validating adjudicator's keys...");
    let ok = BGLS::ve_validate(&P, &Q, &P_adj, &Q_adj);
    println!("    validate: {}", bool::from(ok));
    assert!(bool::from(ok));

    // sign in verifiably encrypted fashion:
    println!("signing in verifiably encrypted fashion...");
    let Sigma = BGLS::ve_sign(&mut rng, &P,&V[0], &s[0], &P_adj, &m[0]);
    println!("    omega: {:?}", Sigma.0);
    println!("    mu: {:?}", Sigma.1);

    // verify encrypted signature:
    println!("verifying encrypted signature...");
    let ok = BGLS::ve_verify(&Q, &V[0], &Q_adj, &Sigma, &m[0]);
    println!("    verify 1: {}  (should be true)", bool::from(ok));
    assert!(bool::from(ok));
    let ok = BGLS::ve_verify(&Q, &V[0], &Q_adj, &Sigma, &x[0]);
    println!("    verify 0: {} (should be false)", bool::from(ok));
    assert!(!bool::from(ok));

    // adjudicate:
    println!("adjudicating...");
    let mut sigma = BNPoint::<BN, LIMBS>::zero();
    let ok = BGLS::ve_adjudicate(&Q, &V[0], &Q_adj, &s_adj, &Sigma, &m[0], &mut sigma);
    println!("    verify 1: {}  (should be true)", bool::from(ok));
    //println!("    sigma  1: {}", sigma);
    assert!(bool::from(ok));
    let ok = BGLS::verify(&Q, &V[0], &m[0], &sigma);
    println!("    verification of extracted signature: {} (should be true)", bool::from(ok));
    println!("    verify 1: {}  (should be true)", bool::from(ok));
    assert!(bool::from(ok));
    assert!(bool::from(!sigma.is_zero()));
    let mut sigma = BNPoint::<BN, LIMBS>::zero();
    let ok = BGLS::ve_adjudicate(&Q, &V[0], &Q_adj, &s_adj, &Sigma, &x[0], &mut sigma);
    println!("    verify 0: {} (should be false)", bool::from(ok));
    //println!("    sigma  0: {}", sigma);
    assert!(!bool::from(ok));
    assert!(bool::from(sigma.is_zero()));

    match now.elapsed() {
        Ok(elapsed) => {
            println!("Total elapsed time: {} ms.", (elapsed.as_micros() as f64)/1000.0);
        }
        Err(e) => {
            println!("Error: {e:?}");
        }
    }
}
