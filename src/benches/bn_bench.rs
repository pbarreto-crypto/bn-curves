#[macro_use]
extern crate criterion;
extern crate bn_curves;

use bn_curves::bnpairing::BNPairing;
use bn_curves::bnparam::{BN062Param, BN126Param, BN190Param, BN254Param, BN318Param, BN382Param, BN446Param, BN510Param, BN574Param, BN638Param, BN702Param, BN766Param, BNParam};
use bn_curves::bnpoint::BNPoint;
use bn_curves::bnpoint2::BNPoint2;
use bn_curves::bnzn::BNZn;
use criterion::Criterion;
use crypto_bigint::Random;

#[allow(clippy::many_single_char_names)]
#[allow(non_snake_case)]
fn general_benchmark<BN: BNParam, const LIMBS: usize>(c: &mut Criterion) {
    let mut rng = rand::rng();
    let P: BNPoint<BN, LIMBS> = BNPoint::random(&mut rng);
    let Q: BNPoint2<BN, LIMBS> = BNPoint2::random(&mut rng).elim_cof();
    let s: BNZn<BN, LIMBS> = BNZn::random(&mut rng);

    // BNPoint arithmetic
    {
        c.bench_function(&format!("BN{:03} G_1 doubling", 64*LIMBS - 2), move |b| {
            b.iter(|| std::hint::black_box(P).double(1))
        });
        c.bench_function(&format!("BN{:03} G_1 addition", 64*LIMBS - 2), move |b| {
            b.iter(|| std::hint::black_box(P) + std::hint::black_box(P))
        });
        c.bench_function(&format!("BN{:03} G_1 scalar multiplication", 64*LIMBS - 2), move |b| {
            b.iter(|| std::hint::black_box(s) * std::hint::black_box(P))
        });
    }

    // BNPoint2 arithmetic
    {
        c.bench_function(&format!("BN{:03} G_2 doubling", 64*LIMBS - 2), move |b| {
            b.iter(|| std::hint::black_box(Q).double(1))
        });
        c.bench_function(&format!("BN{:03} G_2 addition", 64*LIMBS - 2), move |b| {
            b.iter(|| std::hint::black_box(Q) + std::hint::black_box(Q))
        });
        c.bench_function(&format!("BN{:03} G_2 scalar multiplication", 64*LIMBS - 2), move |b| {
            b.iter(|| std::hint::black_box(s) * std::hint::black_box(Q))
        });
    }

    // pairings
    {
        c.bench_function(&format!("BN{:03} Tate pairing", 64*LIMBS - 2), move |b| {
            b.iter(|| BNPairing::tate(std::hint::black_box(&P), std::hint::black_box(&Q)))
        });
        c.bench_function(&format!("BN{:03} Ate pairing", 64*LIMBS - 2), move |b| {
            b.iter(|| BNPairing::ate(std::hint::black_box(&Q), std::hint::black_box(&P)))
        });
        c.bench_function(&format!("BN{:03} optimal pairing", 64*LIMBS - 2), move |b| {
            b.iter(|| BNPairing::opt(std::hint::black_box(&Q), std::hint::black_box(&P)))
        });
    }
}

#[allow(non_snake_case)]
fn criterion_benchmark_BN062(c: &mut Criterion) {
    type BN = BN062Param;
    const LIMBS: usize = BN::LIMBS;
    general_benchmark::<BN, LIMBS>(c);
}

#[allow(non_snake_case)]
fn criterion_benchmark_BN126(c: &mut Criterion) {
    type BN = BN126Param;
    const LIMBS: usize = BN::LIMBS;
    general_benchmark::<BN, LIMBS>(c);
}

#[allow(non_snake_case)]
fn criterion_benchmark_BN190(c: &mut Criterion) {
    type BN = BN190Param;
    const LIMBS: usize = BN::LIMBS;
    general_benchmark::<BN, LIMBS>(c);
}

#[allow(non_snake_case)]
fn criterion_benchmark_BN254(c: &mut Criterion) {
    type BN = BN254Param;
    const LIMBS: usize = BN::LIMBS;
    general_benchmark::<BN, LIMBS>(c);
}

#[allow(non_snake_case)]
fn criterion_benchmark_BN318(c: &mut Criterion) {
    type BN = BN318Param;
    const LIMBS: usize = BN::LIMBS;
    general_benchmark::<BN, LIMBS>(c);
}

#[allow(non_snake_case)]
fn criterion_benchmark_BN382(c: &mut Criterion) {
    type BN = BN382Param;
    const LIMBS: usize = BN::LIMBS;
    general_benchmark::<BN, LIMBS>(c);
}

#[allow(non_snake_case)]
fn criterion_benchmark_BN446(c: &mut Criterion) {
    type BN = BN446Param;
    const LIMBS: usize = BN::LIMBS;
    general_benchmark::<BN, LIMBS>(c);
}

#[allow(non_snake_case)]
fn criterion_benchmark_BN510(c: &mut Criterion) {
    type BN = BN510Param;
    const LIMBS: usize = BN::LIMBS;
    general_benchmark::<BN, LIMBS>(c);
}

#[allow(non_snake_case)]
fn criterion_benchmark_BN574(c: &mut Criterion) {
    type BN = BN574Param;
    const LIMBS: usize = BN::LIMBS;
    general_benchmark::<BN, LIMBS>(c);
}

#[allow(non_snake_case)]
fn criterion_benchmark_BN638(c: &mut Criterion) {
    type BN = BN638Param;
    const LIMBS: usize = BN::LIMBS;
    general_benchmark::<BN, LIMBS>(c);
}

#[allow(non_snake_case)]
fn criterion_benchmark_BN702(c: &mut Criterion) {
    type BN = BN702Param;
    const LIMBS: usize = BN::LIMBS;
    general_benchmark::<BN, LIMBS>(c);
}

#[allow(non_snake_case)]
fn criterion_benchmark_BN766(c: &mut Criterion) {
    type BN = BN766Param;
    const LIMBS: usize = BN::LIMBS;
    general_benchmark::<BN, LIMBS>(c);
}

criterion_group!(benches,
    criterion_benchmark_BN062,
    criterion_benchmark_BN126,
    criterion_benchmark_BN190,
    criterion_benchmark_BN254,
    criterion_benchmark_BN318,
    criterion_benchmark_BN382,
    criterion_benchmark_BN446,
    criterion_benchmark_BN510,
    criterion_benchmark_BN574,
    criterion_benchmark_BN638,
    criterion_benchmark_BN702,
    criterion_benchmark_BN766,
);
criterion_main!(benches);
