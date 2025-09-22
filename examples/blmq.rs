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
use bn_curves::traits::{BNField, One};
use crypto_bigint::{Random, Zero};
use crypto_bigint::subtle::{Choice, ConditionallySelectable, ConstantTimeEq};
use crypto_bigint::rand_core::RngCore;
use std::marker::PhantomData;
use std::time::SystemTime;
use sha3::digest::ExtendableOutput;
use sha3::Shake256;

/// The Barreto-Libert-McCullagh-Quisquater (BLMQ) identity-based signature scheme over BN curves.
///
/// NB: The original description assumed Type 2 pairings, which Chatterjee and Menezes argue
/// to be just an inefficient form of Type 3 pairings.  Indeed, it is possible to adapt both
/// BLMQ protocols (i.e. the identity-based signature scheme and the signcryption scheme alike)
/// and their security proofs under the q-SDH assumption to Type 3 pairings, and this
/// implementation follows this more natural and more efficient approach.
///
/// References:
///
/// * P. S. L. M. Barreto, B. Libert, N. McCullagh, J.-J. Quisquater,
/// "Efficient and Provably-Secure Identity-Based Signatures and Signcryption from Bilinear Maps."
/// Advances in Cryptology -- ASIACRYPT 2005, LNCS 3788, pp. 515--532, Springer, 2005.
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
    /// Output the PKG public key <i>pk</i> &#x2254;
    /// (<i>P</i>, <i>Q</i>, <i>P<sub>pub</sub></i>, <i>Q<sub>pub</sub></i>, <i>g</i>)
    /// and the PKG secret key <i>sk</i>.
    ///
    /// NB: By hashing a PKG ID to curve group generators, the public parameters can be reduced to that ID,
    /// P<sub>pub</sub>, and Q<sub>pub</sub></i>, with the remaining values to be computed on demand.
    #[allow(non_snake_case)]
    pub fn setup<R: RngCore + ?Sized>(rng: &mut R)
            -> ((BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNFp12<BN, LIMBS>),
                BNZn<BN, LIMBS>) {
        /*
        // default generators:
        let P = BNPoint::default_generator();
        let Q = BNPoint2::default_generator();
        // */
        //*
        // pick individualized generators:
        let PKG_ID = "BLMQ PKG".to_string().into_bytes().to_vec();
        let P = BNPoint::point_factory(BNFp::shake256(&PKG_ID));
        let Q = BNPoint2::point_factory(BNFp2::shake256(&PKG_ID)).elim_cof();
        // */
        let sk = BNZn::random(rng);
        let Ppub = sk*P;
        let Qpub = sk*Q;
        let g = BNPairing::opt(&Q, &P);
        let pk = (P, Q, Ppub, Qpub, g);  // or just (PKG_ID, Ppub, Qpub)
        (pk, sk)
    }

    /// Validate the PKG public key for consistency by checking that e(<i>P<sub>pub</sub></i>, <i>Q</i>)
    /// = e(<i>P</i>, <i>Q<sub>pub</sub></i>) and that e(<i>P</i>, <i>Q</i>) = <i>g</i> &ne; 0, 1.
    #[allow(non_snake_case)]
    pub fn validate(pk: (BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNFp12<BN, LIMBS>)) -> Choice {
        let P = pk.0;
        let Q = pk.1;
        let Ppub = pk.2;
        let Qpub = pk.3;
        let g = pk.4;
        //*
        BNPairing::opt(&Q, &Ppub).ct_eq(&BNPairing::opt(&Qpub, &P)) &
        BNPairing::opt(&Q, &P).ct_eq(&g) & !g.is_zero() & !g.is_one()
        // */
        /*
        // since Q is common to two of the pairings, it may be advantageous to resort to precomputation:
        let Q_triples = BNPairing::precomp(&Q);
        BNPairing::eval(&Q_triples, &Ppub).ct_eq(&BNPairing::opt(&Qpub, &P)) &
        BNPairing::eval(&Q_triples, &P).ct_eq(&g) & !g.is_zero() & !g.is_one()
        // */
    }

    /// A sample hash function <i>H&#x2081;</i> ∶ {0,1}&ast; &rarr; &Zopf;<i>&#x2099;</i>&ast;.
    #[allow(non_snake_case)]
    pub fn H1(id: &String) -> BNZn<BN, LIMBS> {
        let mut bytes: Vec<u8> = id.as_bytes().to_vec();
        let mut sep: Vec<u8> = "BLMQ H_1".to_string().into_bytes().to_vec();  // domain separation string
        bytes.append(&mut sep);
        BNZn::shake256(bytes.as_slice())
    }

    /// A sample hash function <i>H&#x2082;</i> ∶ <b>F</b><sub><i>p&sup1;&#xFEFF;&sup2;</i></sub> &times; {0,1}&ast; &rarr; &Zopf;<i>&#x2099;</i>&ast;.
    #[allow(non_snake_case)]
    pub fn H2(r: &BNFp12<BN, LIMBS>, m: &[u8]) -> BNZn<BN, LIMBS> {
        let mut bytes = r.to_bytes();
        let mut data = m.to_vec();
        bytes.append(&mut data);
        let mut sep = "BLMQ H_2".to_string().into_bytes().to_vec();  // domain separation string
        bytes.append(&mut sep);
        BNZn::shake256(bytes.as_slice())
    }

    /// A sample hash function <i>H&#x2083;</i> ∶ <b>F</b><sub><i>p&sup1;&#xFEFF;&sup2;</i></sub> &rarr; {0,1}&ast;:
    /// absorb `r`, a domain separation string, and the output length `out`.len() into the sponge,
    /// then squeeze exactly `out`.len() hash bytes into `out`.
    /// This function is used for signcryption, not for pure signing.
    #[allow(non_snake_case)]
    pub fn H3(r: &BNFp12<BN, LIMBS>, out: &mut [u8]) {
        let mut bytes = r.to_bytes();
        let mut sep = ("BLMQ H_3_".to_owned() + &out.len().to_string()).into_bytes().to_vec();  // domain separation string
        bytes.append(&mut sep);
        Shake256::digest_xof(bytes, out);
    }

    /// Given an identity ID, the PKG private key <i>sk</i> and its associated public key
    /// <i>pk</i> &#x2254; (<i>P</i>, <i>Q</i>, <i>P<sub>pub</sub></i>, <i>Q<sub>pub</sub></i>, <i>g</i>),
    /// compute the corresponding user private key <i>S</i><sub>ID</sub> &#x2254;
    /// &lbrack;<i>1</i>/(<i>H&#x2081;</i>(ID) + <i>sk</i>)&rbrack;<i>P</i> &in; <b>G</b><i>&#x2081;</i>.
    /// This key is meant for BLMQ signatures only.
    #[allow(non_snake_case)]
    pub fn keygen1(sk: &BNZn<BN, LIMBS>,
            pk: &(BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNFp12<BN, LIMBS>),
            ID: &String) -> BNPoint<BN, LIMBS> {
        let P = pk.0;
        let S_ID = (BLMQ::<BN, LIMBS>::H1(&ID) + *sk).inv()*P;
        S_ID
    }

    /// Given an identity ID, the PKG private key <i>sk</i> and its associated public key
    /// <i>pk</i> &#x2254; (<i>P</i>, <i>Q</i>, <i>P<sub>pub</sub></i>, <i>Q<sub>pub</sub></i>, <i>g</i>),
    /// compute the corresponding user private keys <i>S</i><sub>ID</sub> &#x2254;
    /// &lbrack;<i>1</i>/(<i>H&#x2081;</i>(ID) + <i>sk</i>)&rbrack;<i>P</i> &in; <b>G</b><i>&#x2081;</i>
    /// and <i>T</i><sub>ID</sub> &#x2254; &lbrack;<i>1</i>/(<i>H&#x2081;</i>(ID) + <i>sk</i>)&rbrack;<i>Q</i>
    /// &in; <b>G</b><i>&#x2081;</i>.
    /// These keys are meant for BLMQ signcryption (but <i>S</i><sub>ID</sub> can still be used alone
    /// for BLMQ signatures).
    #[allow(non_snake_case)]
    pub fn keygen2(sk: &BNZn<BN, LIMBS>,
            pk: &(BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNFp12<BN, LIMBS>),
            ID: &String) -> (BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>) {
        let P = pk.0;
        let Q = pk.1;
        let u = (BLMQ::<BN, LIMBS>::H1(&ID) + *sk).inv();
        let S_ID = u*P;
        let T_ID = u*Q;
        (S_ID, T_ID)
    }

    /// Given the PKG public key <i>pk</i> &#x2254;
    /// (<i>P</i>, <i>Q</i>, <i>P<sub>pub</sub></i>, <i>Q<sub>pub</sub></i>, <i>g</i>),
    /// an identity ID, and a signing key <i>S<sub>ID</sub></i>,
    /// confirm that <i>S<sub>ID</sub></i> corresponds to ID.
    #[allow(non_snake_case)]
    pub fn keycheck1(pk: &(BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNFp12<BN, LIMBS>),
            ID: &String, S_ID: &BNPoint<BN, LIMBS>) -> Choice {
        // check that e(S_ID, [H_1(ID)]Q + Q_pub) = g:
        let Q = pk.1;
        let Qpub = pk.3;
        let g = pk.4;
        BNPairing::opt(&(BLMQ::H1(&ID)*Q + Qpub), S_ID).ct_eq(&g)
    }

    /// Given the PKG public key <i>pk</i> &#x2254;
    /// (<i>P</i>, <i>Q</i>, <i>P<sub>pub</sub></i>, <i>Q<sub>pub</sub></i>, <i>g</i>),
    /// an identity ID, and signcryption keys <i>S<sub>ID</sub></i> and <i>T<sub>ID</sub></i>,
    /// confirm that <i>S<sub>ID</sub></i> and <i>T<sub>ID</sub></i> correspond
    /// to each other and to ID.
    #[allow(non_snake_case)]
    pub fn keycheck2(pk: &(BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNFp12<BN, LIMBS>),
            ID: &String, S_ID: &BNPoint<BN, LIMBS>, T_ID: &BNPoint2<BN, LIMBS>) -> Choice {
        let P = pk.0;
        let Q = pk.1;
        let Ppub = pk.2;
        let g = pk.4;
        // check that e([H_1(ID)]P + P_pub, T_ID) = g (i.e. T_ID corresponds to ID)
        // and e(P, T_ID) = e(S_ID, Q) (i.e. S_ID and T_ID correspond to each other):
        //*
        BNPairing::opt(&T_ID, &(BLMQ::H1(&ID)*P + Ppub)).ct_eq(&g) &
        BNPairing::opt(&T_ID, &P).ct_eq(&BNPairing::opt(&Q, S_ID))
        // */
        /*
        // since T_ID is common to two of the pairings, it may be advantageous to resort to precomputation:
        let T_ID_triples = BNPairing::precomp(&T_ID);
        BNPairing::eval(&T_ID_triples, &(BLMQ::H1(&ID)*P + Ppub)).ct_eq(&g) &
        BNPairing::eval(&T_ID_triples, &P).ct_eq(&BNPairing::opt(&Q, S_ID))
        // */
    }

    /// Given a signing key <i>S<sub>ID</sub></i>,
    /// the PKG public key <i>pk</i> &#x2254; (<i>P</i>, <i>Q</i>, <i>P<sub>pub</sub></i>, <i>Q<sub>pub</sub></i>, <i>g</i>),
    /// and a message <i>m</i>,
    /// generate a BLMQ signature <i>&sigma;</i> for <i>m</i> under <i>S<sub>ID</sub></i>.
    #[allow(non_snake_case)]
    pub fn sign<R: RngCore + ?Sized>(rng: &mut R,
            pk: &(BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNFp12<BN, LIMBS>),
            S_ID: &BNPoint<BN, LIMBS>,
            m: &[u8]) -> (BNZn<BN, LIMBS>, BNPoint<BN, LIMBS>) {
        // pick a random x from Z_n^* and compute r ← g^x:
        let g = pk.4;
        let x = BNZn::random(rng);
        let r = g.pow(&x.to_uint());
        // set h ← H_2(m,r) ∈ Z_n^*:
        let h = BLMQ::H2(&r, m);
        // compute S ← [x+h]S_ID:
        let S = (x + h)*(*S_ID);
        // the signature is σ ∶= (h,S):
        (h, S)
    }

    /// Given the PKG public key <i>pk</i> &#x2254; (<i>P</i>, <i>Q</i>, <i>P<sub>pub</sub></i>, <i>Q<sub>pub</sub></i>, <i>g</i>),
    /// the signer's identity ID, a message <i>m</i>, and a signature <i>&sigma;</i> &#x2254; (<i>h</i>, <i>S</i>),
    /// output <i>true</i> if the signature verifies, or <i>false</i> otherwise.
    #[allow(non_snake_case)]
    pub fn verify(pk: &(BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNFp12<BN, LIMBS>),
            ID: &String, m: &[u8], sigma: &(BNZn<BN, LIMBS>, BNPoint<BN, LIMBS>)) -> Choice {
        // accept iff h = H_2(m, e(S, [H_1(ID)]Q + Q_pub)*g^(-h))
        let Q = pk.1;
        let Qpub = pk.3;
        let g = pk.4;
        let h = sigma.0;
        let S = sigma.1;
        let r = BNPairing::opt(&(BLMQ::H1(&ID)*Q + Qpub), &S)*g.pow(&(-h).to_uint());
        let c = BLMQ::H2(&r, m);
        h.ct_eq(&c)
    }

    /// Given a signcryption key <i>S<sub>ID_A</sub></i> and <i>T<sub>ID_A</sub></i>, the PKG public key
    /// <i>pk</i> &#x2254; (<i>P</i>, <i>Q</i>, <i>P<sub>pub</sub></i>, <i>Q<sub>pub</sub></i>, <i>g</i>),
    /// the recipient's identity <i>ID_B</i>, and a message <i>m</i>,
    /// generate a BLMQ signcryptogram <i>C</i> &#x2254; (<i>c</i>, <i>S</i>, <i>U</i>) on <i>m</i>
    /// encrypted for <i>ID_B</i> and signed under <i>S<sub>ID_A</sub></i>.
    #[allow(non_snake_case)]
    pub fn signcrypt<R: RngCore + ?Sized>(rng: &mut R,
            pk: &(BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNFp12<BN, LIMBS>),
            S_ID_A: &BNPoint<BN, LIMBS>, ID_B: &String, m: &[u8])
            -> (Vec<u8>, BNPoint<BN, LIMBS>, BNPoint<BN, LIMBS>) {
        // pick a random x from Z_n^* and compute r ← g^x and c ← H_3(r) ⊕ m:
        let P = pk.0;
        let Ppub = pk.2;
        let g = pk.4;
        let x = BNZn::random(rng);
        let r = g.pow(&x.to_uint());
        let mut c: Vec<u8> = vec![0u8; m.len()];
        BLMQ::H3(&r, &mut c);
        for j in 0..c.len() {
            c[j] ^= m[j];
        }
        // set h ← H_2(m,r) ∈ Z_n^*:
        let h = BLMQ::H2(&r, m);
        // compute S ← [x+h]S_ID_A:
        let S = (x + h)*(*S_ID_A);
        //compute U ← [x]([H_1(ID_B)]P + P_pub):
        let U = x*(BLMQ::H1(&ID_B)*P + Ppub);
        // the signcryptogram is C ∶= (c,S,U) ∈ {0,1}^* × G_1 × G_1:
        (c, S, U)
    }

    /// Given the PKG public key <i>pk</i> &#x2254; (<i>P</i>, <i>Q</i>, <i>P<sub>pub</sub></i>, <i>Q<sub>pub</sub></i>, <i>g</i>),
    /// a signcryptogram <i>C</i> &#x2254; (<i>c</i>, <i>S</i>, <i>U</i>),
    /// the recipient's private key <i>T<sub>ID_B</sub></i>,
    /// and the purported sender's identity <i>ID_A</i>,
    /// output <i>true</i> if the signcryptogram verifies (and then extract the message <i>m</i> and
    /// the signature <i>&sigma;</i> &#x2254; (<i>h</i>, <i>S</i>) from it), or <i>false</i> otherwise.
    #[allow(non_snake_case)]
    pub fn unsigncrypt(pk: &(BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNPoint<BN, LIMBS>, BNPoint2<BN, LIMBS>, BNFp12<BN, LIMBS>),
            C: &(Vec<u8>, BNPoint<BN, LIMBS>, BNPoint<BN, LIMBS>),
            T_ID_B: &BNPoint2<BN, LIMBS>, ID_A: &String,
            m: &mut [u8], sigma: &mut (BNZn<BN, LIMBS>, BNPoint<BN, LIMBS>)) -> Choice {
        let Q = pk.1;
        let Qpub = pk.3;
        let g = pk.4;
        let c = &C.0;
        let S = C.1;
        let U = C.2;
        // compute r ← e(U, T_ID_B), m ← H_3(r) ⊕ c, and h ← H_2(r, m):
        let r = BNPairing::opt(&T_ID_B, &U);
        let mut d: Vec<u8> = vec![0u8; c.len()];
        BLMQ::H3(&r, &mut d);
        for j in 0..c.len() {
            d[j] ^= c[j];
        }
        let h = BLMQ::H2(&r, &d);
        // accept iff r = e(S, [H_1(ID_A)]Q + Q_pub)*g^(-h) (and the decrypted message fits):
        let w = BNPairing::opt(&(BLMQ::H1(&ID_A)*Q + Qpub), &S)*g.pow(&(-h).to_uint());
        let accept = r.ct_eq(&w) & m.len().ct_eq(&c.len());
        // if the acceptance condition holds, extract the message m and the signature (h, S):
        for j in 0..d.len() {
            m[j].conditional_assign(&d[j], accept);
        }
        sigma.0.conditional_assign(&h, accept);
        sigma.1.conditional_assign(&S, accept);
        accept
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
    println!("Showcasing BLMQ identity-based signatures and signcryption over BN{:03}...", 64*LIMBS - 2);

    //let mut rng: SmallRng = SmallRng::from_seed([0; 32]);
    let mut rng = rand::rng();
    let now = SystemTime::now();

    // ---- BLMQ identity-based signatures ----

    // setup:
    println!("setting up...");
    let (pk, sk) = BLMQ::<BN, LIMBS>::setup(&mut rng);
    //println!("    pk: {:?}", pk);
    //println!("    sk: {:?}", sk);

    // validate:
    println!("validating...");
    let ok = BLMQ::<BN, LIMBS>::validate(pk);
    println!("    validate: {}", bool::from(ok));
    assert!(bool::from(ok));

    let ID = "User ID".to_string();  // a sample user identity
    println!("    ID: {:?}", ID);

    // keygen:
    println!("generating key S_ID...");
    let S_ID = BLMQ::<BN, LIMBS>::keygen1(&sk, &pk, &ID);
    //println!("    S_ID: {:?}", S_ID);

    // key check:
    println!("checking key...");
    let ok = BLMQ::<BN, LIMBS>::keycheck1(&pk, &ID, &S_ID);
    println!("    keycheck: {}", bool::from(ok));
    assert!(bool::from(ok));

    // sign:
    println!("signing sample message...");
    let m = "sample message".to_string().as_bytes().to_vec();
    let sigma = BLMQ::<BN, LIMBS>::sign(&mut rng, &pk, &S_ID, &m);
    //println!("    sign: {:?}", sigma);

    // verify:
    println!("verifying signature...");
    let ok = BLMQ::<BN, LIMBS>::verify(&pk, &ID, &m, &sigma);
    println!("    verify 1: {}  (should be true)", bool::from(ok));
    assert!(bool::from(ok));
    let x = "wrong message".to_string().as_bytes().to_vec();
    let ok = BLMQ::<BN, LIMBS>::verify(&pk, &ID, &x, &sigma);
    println!("    verify 0: {} (should be false)", bool::from(ok));
    assert!(!bool::from(ok));

    // ---- BLMQ signcryption ----

    let ID_A = "User ID_A".to_string();  // a sample user identity
    println!("    ID_A: {:?}", ID_A);

    let ID_B = "User ID_B".to_string();  // a sample user identity
    println!("    ID_B: {:?}", ID_B);

    // keygen:
    println!("generating keys...");
    let (S_ID_A, T_ID_A) = BLMQ::<BN, LIMBS>::keygen2(&sk, &pk, &ID_A);
    //println!("    S_ID_A: {:?}", S_ID_A);
    let (S_ID_B, T_ID_B) = BLMQ::<BN, LIMBS>::keygen2(&sk, &pk, &ID_B);
    //println!("    S_ID_B: {:?}", S_ID_B);

    // key check:
    println!("checking keys...");
    let ok = BLMQ::<BN, LIMBS>::keycheck2(&pk, &ID_A, &S_ID_A, &T_ID_A);
    println!("    keycheck A: {}", bool::from(ok));
    assert!(bool::from(ok));
    let ok = BLMQ::<BN, LIMBS>::keycheck2(&pk, &ID_B, &S_ID_B, &T_ID_B);
    println!("    keycheck B: {}", bool::from(ok));
    assert!(bool::from(ok));

    // signcrypt A -> B:
    println!("signcrypting A -> B...");
    let m = "sample message A->B".to_string().as_bytes().to_vec();
    let mut C = BLMQ::<BN, LIMBS>::signcrypt(&mut rng, &pk, &S_ID_A, &ID_B, &m);
    //println!("    signcrypt: {:?}", C);

    // unsigncrypt B <- A:
    println!("unsigncrypting B <- A...");
    let mut d = vec![0u8; C.0.len()];
    let mut sig = (BNZn::<BN, LIMBS>::zero(), BNPoint::<BN, LIMBS>::zero());
    let ok = BLMQ::<BN, LIMBS>::unsigncrypt(&pk, &C, &T_ID_B, &ID_A, &mut d, &mut sig);
    println!("    unsigncrypt 1: {}  (should be true)", bool::from(ok));
    assert!(bool::from(ok));

    C.0[0] ^= 1;  // just flip a bit to cause an error
    let ok = BLMQ::<BN, LIMBS>::unsigncrypt(&pk, &C, &T_ID_B, &ID_A, &mut d, &mut sig);
    println!("    unsigncrypt 0: {} (should be false)", bool::from(ok));
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
