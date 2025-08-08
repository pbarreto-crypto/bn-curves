use bn_curves::bnfp::BNFp;
use bn_curves::bnfp2::BNFp2;
use bn_curves::bnpairing::BNPairing;
use bn_curves::bnparam::{BNParam, BN062Param, BN126Param, BN190Param, BN254Param, BN318Param, BN382Param, BN446Param, BN510Param, BN574Param, BN638Param, BN702Param, BN766Param};
use bn_curves::bnpoint::BNPoint;
use bn_curves::bnpoint2::BNPoint2;
use bn_curves::bnzn::BNZn;
use crypto_bigint::{Encoding, NonZero, Random, RandomMod, Uint, Word, Zero};
use crypto_bigint::subtle::{Choice, ConstantTimeEq};
use rand::prelude::{SmallRng, ThreadRng};
use sha3::Shake256;
use sha3::digest::ExtendableOutput;
use std::marker::PhantomData;
use std::ops::Rem;
use std::time::SystemTime;
use crypto_bigint::rand_core::{RngCore, SeedableRng};
use rand::rng;
use bn_curves::bnfp12::BNFp12;

/// The Barreto-Libert-McCullagh-Quisquater BLMQ identity-based signature scheme over BN curves.
///
/// NB: The original description assumed Type 2 pairings, which Chatterjee and Menezes argue
/// to be just an inefficient form of Type 3 pairings.  Indeed, it is possible to adapt both
/// the BLMQ protocols (i.e. the identity-based signature scheme and the signcryption scheme
/// alike) and their security proofs under the q-SDH assumption to Type 3 pairings, and this
/// implementation follows this more natural and more efficient approach.
///
/// References:
///
/// * P. S. L. M. Barreto, B. Libert, N. McCullagh, J.-J. Quisquater,
/// "Efficient and Provably-Secure Identity-Based Signatures and Signcryption from Bilinear Maps."
/// Advances in Cryptology -- ASIACRYPT 2009, LNCS 3788, pp. 515--532, Springer, 2005.
/// https://doi.org/10.1007/11593447_28
///
/// * S. Chatterjee, A. Menezes,
/// "On cryptographic protocols employing asymmetric pairings -- The role of &Psi; revisited."
/// Discrete Applied Mathematics, vol. 159, no. 13, pp. 1311--1322, ScienceDirect, 2011.
/// https://doi.org/10.1016/j.dam.2011.04.021
#[allow(non_camel_case_types)]
pub struct BLMQ<BN: BNParam, const LIMBS: usize>(
    #[doc(hidden)]
    pub PhantomData<BN>,
);

impl<BN: BNParam, const LIMBS: usize> BLMQ<BN, LIMBS> {
    /// Given a pairing friendly elliptic curve with groups
    /// <b>G</b><i>&#x2081;</i>, <b>G</b><i>&#x2082;</i> and <b>G</b><i><sub>T</sub></i>,
    /// choose generators <i>P</i> &in; <b>G</b><i>&#x2081;</i> and <i>Q</i> &in; <b>G</b><i>&#x2082;</i>,
    /// select a PKG secret key <i>sk</i> &#8668; &Zopf;<i>&#x2099;</i>, and compute
    /// (<i>P<sub>pub</sub></i> &#x2254; &lbrack;<i>sk</i>&rbrack;<i>P</i>,
    /// <i>Q<sub>pub</sub></i> &#x2254; &lbrack;<i>sk</i>&rbrack;<i>Q</i>,
    /// <i>g</i> &#x2254; e(<i>P</i>, <i>Q</i>)) &in;
    /// <b>G</b><i>&#x2081;</i> &times; <b>G</b><i>&#x2082;</i> &times; <b>F</b><sub><i>p&sup1;&#xFEFF;&sup2;</i></sub>.
    ///
    /// Output the system-wide PKG public key <i>pk</i> &#x2254; (<i>P, Q,
    /// P<sub>pub</sub>, Q<sub>pub</sub></i>, <i>g</i>) and the PKG secret key <i>sk</i>.
    #[allow(non_snake_case)]
    pub fn setup<R: RngCore + ?Sized>(rng: &mut R)
            -> ((BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNFp12<BN, LIMBS>),
                BNZn<BN, LIMBS>) {
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
        let sk = BNZn::random(rng);
        let Ppub = sk*P;
        let Qpub = sk*Q;
        let g = BNPairing::opt(&Q, &P);
        let pk = (P, Q, Ppub, Qpub, g);
        (pk, sk)
    }

    #[allow(non_snake_case)]
    pub fn H1(id: &String) -> BNZn<BN, LIMBS> {
        let mut bytes = id.as_bytes().to_vec();
        let mut sep = "BLMQ H_1".to_string().into_bytes().to_vec();  // domain separation string
        bytes.append(&mut sep);
        BNZn::shake256(bytes.as_slice())
    }

    #[allow(non_snake_case)]
    pub fn H2(m: &[u8], r: &BNFp12<BN, LIMBS>) -> BNZn<BN, LIMBS> {
        let mut bytes = m.to_vec();
        let mut nonce = r.to_bytes();
        bytes.append(&mut nonce);
        let mut sep = "BLMQ H_2".to_string().into_bytes().to_vec();  // domain separation string
        bytes.append(&mut sep);
        BNZn::shake256(bytes.as_slice())
    }

    /// Given an identity `id`, the PKG private key <i>sk</i> and its associated public key
    /// <i>pk</i> &#x2254; (<i>P, Q, P<sub>pub</sub>, Q<sub>pub</sub></i>),
    /// compute the corresponding private key <i>S</i><sub>`id`</sub> &#x2254;
    /// &lbrack;<i>1</i>/(<i>H&#x2081;</i>(`id`) + <i>sk</i>)&rbrack;<i>P</i>
    /// &in; <b>G</b><i>&#x2081;</i>.
    #[allow(non_snake_case)]
    pub fn keygen(sk: BNZn<BN, LIMBS>,
            pk: (BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNFp12<BN, LIMBS>),
            id: String) -> BNPoint<BN, LIMBS> {
        let P = pk.0;
        let S_ID = (BLMQ::<BN, LIMBS>::H1(&id) + sk).inv()*P;
        S_ID
    }

    /// Given a signing key <i>S<sub>ID</sub></i>,
    /// the PKG public key <i>pk</i> &#x2254; (<i>P, Q, P<sub>pub</sub>, Q<sub>pub</sub></i>, <i>g</i>),
    /// and a message <i>m</i>,
    /// output a BLMQ signature <i>&sigma;</i> for <i>m</i> under <i>S<sub>ID</sub></i>.
    #[allow(non_snake_case)]
    pub fn sign<R: RngCore + ?Sized>(rng: &mut R,
            S_ID: BNPoint<BN, LIMBS>,
            pk: (BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNFp12<BN, LIMBS>),
            m: &[u8]) -> (BNZn<BN, LIMBS>, BNPoint<BN, LIMBS>) {
        // pick a random x from Z_n^* and compute r ← g^x:
        let g = pk.4;
        let x = BNZn::random(rng);
        let r = g.pow(&x.to_uint());
        // set h ← H_2(m,r) ∈ Z_n^*:
        let h = BLMQ::H2(m, &r);
        // compute S ← [x+h]S_ID:
        let S = (x + h)*S_ID;
        // the signature is σ ∶= (h,S):
        (h, S)
    }

    /// Given the PKG public key <i>pk</i> &#x2254; (<i>P, Q, P<sub>pub</sub>, Q<sub>pub</sub></i>, <i>g</i>),
    /// the signer's identity, a message <i>m</i>, and a signature <i>&sigma;</i> &#x2254; (<i>h</i>, <i>S</i>),
    /// output <i>true</i> iff the signature verifies, or <i>false</i> otherwise.
    #[allow(non_snake_case)]
    pub fn verify(pk: (BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNFp12<BN, LIMBS>),
            id: String, m: &[u8], sigma: (BNZn<BN, LIMBS>, BNPoint<BN, LIMBS>)) -> Choice {
        // accept iff h = H_2(m, e(S, [H_1(ID)]Q + Q_pub) g^(-h))
        let Q = pk.1;
        let Qpub = pk.3;
        let g = pk.4;
        let h = sigma.0;
        let S = sigma.1;
        let r = BNPairing::opt(&(BLMQ::H1(&id)*Q + Qpub), &S)*g.pow(&(-h).to_uint());
        let c = BLMQ::H2(m, &r);
        h.ct_eq(&c)
    }

}

#[allow(non_snake_case)]
fn main() {
    // choose a target parameter set:
    type BN = BN062Param;
    //type BN = BN126Param;
    //type BN = BN190Param;
    //type BN = BN254Param;
    //type BN = BN318Param;
    //type BN = BN382Param;
    //type BN = BN446Param;
    //type BN = BN510Param;
    //type BN = BN574Param;
    //type BN = BN638Param;
    //type BN = BN702Param;
    //type BN = BN766Param;

    const LIMBS: usize = BN::LIMBS;
    println!("Showcasing BLMQ identity-based signatures over BN{:03}...", 64*LIMBS - 2);

    //let mut rng: SmallRng = SmallRng::from_seed([0; 32]);
    let mut rng = rand::rng();
    let now = SystemTime::now();

    // setup:
    let (pk, sk) = BLMQ::<BN, LIMBS>::setup(&mut rng);
    //println!("    pk: {:?}", pk);
    //println!("    sk: {:?}", sk);

    // keygen:
    let S_ID = BLMQ::<BN, LIMBS>::keygen(sk, pk, "User ID".to_string());

    // sign:
    let m = "sample message".to_string().into_bytes().to_vec();
    let sigma = BLMQ::<BN, LIMBS>::sign(&mut rng, S_ID, pk, &m);
    //println!("    sign: {:?}", sigma);

    // verify:
    let ok = BLMQ::<BN, LIMBS>::verify(pk, "User ID".to_string(), &m, sigma);
    println!("    verify 1: {}  (should be true)", bool::from(ok));
    assert!(bool::from(ok));
    let x = "wrong message".to_string().into_bytes().to_vec();
    let ok = BLMQ::<BN, LIMBS>::verify(pk, "User ID".to_string(), &x, sigma);
    println!("    verify 0: {} (should be false)", bool::from(ok));
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
