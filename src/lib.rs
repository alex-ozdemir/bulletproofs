#![feature(test)]

extern crate test as rust_test;

pub type FiatShamirRng = ark_marlin::rng::FiatShamirRng<blake2::Blake2s>;

pub mod curves;
pub mod proofs;
pub mod r1cs;
pub mod reductions;
pub mod relations;
pub mod util;

use ark_ec::group::Group;
use curves::Pair;
use log::debug;
use rand::Rng;
use relations::ipa::{IpaInstance, IpaRelation};
use std::time::Instant;

#[macro_export]
macro_rules! timed {
    ($label:expr, $val:expr) => {{
        use ::ark_std::{end_timer, start_timer};
        let timer = start_timer!($label);
        let val = $val;
        end_timer!(timer);
        val
    }};
}

/// A witness relation, with setup.
pub trait Relation {
    /// Configuration for the reduction.
    type Cfg;
    type Inst;
    type Wit;
    fn check(x: &Self::Inst, w: &Self::Wit);
    fn check_cfg(c: &Self::Cfg, x: &Self::Inst);
    fn size(x: &Self::Inst) -> Self::Cfg;
}

pub trait SampleableRelation: Relation {
    type Params;
    fn sample<R: Rng>(p: &Self::Params, rng: &mut R) -> Self;
}

/// A reduction between relations
pub trait Reduction {
    /// Public parameters. Create by Setup, used by other algorithms.
    type From: Relation;
    type To: Relation;
    type Params;
    type Proof;
    fn prove(
        &self,
        pp: &Self::Params,
        x: &<Self::From as Relation>::Inst,
        w: &<Self::From as Relation>::Wit,
        fs: &mut FiatShamirRng,
    ) -> (
        Self::Proof,
        <Self::To as Relation>::Inst,
        <Self::To as Relation>::Wit,
    );
    fn verify(
        &self,
        pp: &Self::Params,
        x: &<Self::From as Relation>::Inst,
        pf: &Self::Proof,
        fs: &mut FiatShamirRng,
    ) -> <Self::To as Relation>::Inst;
    /// Return the number of field or group elements in a seralized proof.
    fn proof_size(p: &Self::Proof) -> usize;
    /// Setup public parameters for this relation configuration
    fn setup<R: Rng>(&self, c: &<Self::From as Relation>::Cfg, rng: &mut R) -> Self::Params;
    /// Map relation cfg
    fn map_params(&self, c: &<Self::From as Relation>::Cfg) -> <Self::To as Relation>::Cfg;
}

pub trait Proof<R: Relation> {
    type Params;
    type Proof;
    fn prove(
        &self,
        pp: &Self::Params,
        x: &<R as Relation>::Inst,
        w: &<R as Relation>::Wit,
        fs: &mut FiatShamirRng,
    ) -> Self::Proof;
    fn verify(
        &self,
        pp: &Self::Params,
        x: &<R as Relation>::Inst,
        pf: &Self::Proof,
        fs: &mut FiatShamirRng,
    );
    /// Setup public parameters for this relation configuration
    fn setup<Rn: Rng>(&self, c: &R::Cfg, rng: &mut Rn) -> Self::Params;
    fn proof_size(p: &Self::Proof) -> usize;
}

/// Test an IPA on random instance-witness pairs.
///
/// ## Arguments
///
/// * `sizes`: vector lengths
/// * `reps`: repetitions per length
/// * `i`: the IPA
pub fn test_ipa<G: Group, I: Proof<IpaRelation<G>>>(sizes: Vec<usize>, reps: usize, i: I) {
    let rng = &mut ark_std::test_rng();
    for size in sizes {
        for _ in 0..reps {
            let (instance, witness) = IpaInstance::<G>::sample_from_length(rng, size);
            let pp = i.setup(&size, rng);
            IpaRelation::check(&instance, &witness);
            let fs_seed: [u8; 32] = rng.gen();
            let mut fs_rng = FiatShamirRng::from_seed(&fs_seed);
            let pf_start = Instant::now();
            let proof = timed!(|| "proving", i.prove(&pp, &instance, &witness, &mut fs_rng));
            let pf_end = Instant::now();
            debug!(target: "pf_time", "Proof time (s): {}", (pf_end-pf_start).as_secs_f64());
            let proof_size = I::proof_size(&proof);
            debug!(target: "pf_size", "Proof size: {}", proof_size);
            let mut fs_rng = FiatShamirRng::from_seed(&fs_seed);
            let ver_start = Instant::now();
            timed!(
                || "verifying",
                i.verify(&pp, &instance, &proof, &mut fs_rng)
            );
            let ver_end = Instant::now();
            debug!(target: "ver_time", "Verifier time (s): {}", (ver_end-ver_start).as_secs_f64());
        }
    }
}

/// Measure IPA size for a random instance-witness pair
///
/// ## Arguments
///
/// * `sizes`: vector lengths
/// * `i`: the IPA
pub fn ipa_size<G: Group, I: Proof<IpaRelation<G>>>(size: usize, i: I) -> usize {
    let rng = &mut ark_std::test_rng();
    let (instance, witness) = IpaInstance::<G>::sample_from_length(rng, size);
    let pp = i.setup(&size, rng);
    IpaRelation::check(&instance, &witness);
    let fs_seed: [u8; 32] = rng.gen();
    let mut fs_rng = FiatShamirRng::from_seed(&fs_seed);
    let proof = i.prove(&pp, &instance, &witness, &mut fs_rng);
    I::proof_size(&proof)
}

/// Measure R1CS constraints size for a random instance-witness pair
///
/// ## Arguments
///
/// * `size`: lengths
pub fn constraints<C: Pair>(size: usize, k: usize, r: usize) -> usize {
    let reduction = reductions::combinator::Sequence::new(
        reductions::ipa_to_bp_unroll::IpaToBpUnroll::<C>::new(k, r),
        reductions::bp_unroll_to_com_r1cs::UnrollToComR1cs::default(),
    );
    let rng = &mut ark_std::test_rng();
    let (instance, witness) = IpaInstance::<C::G1>::sample_from_length(rng, size);
    let pp = reduction.setup(&size, rng);
    //IpaRelation::check(&instance, &witness);
    let fs_seed: [u8; 32] = rng.gen();
    let mut fs_rng = FiatShamirRng::from_seed(&fs_seed);
    let (_proof, x, _w) = reduction.prove(&pp, &instance, &witness, &mut fs_rng);
    x.n
}

#[cfg(test)]
pub mod test {
    use super::proofs::{bp_iter, bp_rec, bp_rec_kary, ipa_send};
    use super::relations::ipa::{IpaInstance, IpaRelation};
    use super::test_ipa;
    use super::{FiatShamirRng, Proof, Reduction, Relation};
    use ark_bls12_381::Bls12_381;
    use ark_ec::{group::Group, PairingEngine};
    use rand::Rng;

    #[test]
    fn test_bp_ipa_bls_g1() {
        type G = <Bls12_381 as PairingEngine>::G1Projective;
        let i = bp_iter::Bp::<G>::default();
        test_ipa(vec![1, 2, 4, 8, 16, 17], 1, i);
    }

    #[test]
    fn test_send_ipa() {
        type G = <Bls12_381 as PairingEngine>::G1Projective;
        let i = ipa_send::SendIpa::<G>::default();
        test_ipa(vec![1, 2, 3, 4, 8, 9, 15], 1, i);
    }

    #[test]
    fn test_rec_bp_ipa() {
        type G = <Bls12_381 as PairingEngine>::G1Projective;
        let i = bp_rec::Bp::<G, ipa_send::SendIpa<G>>::new(Default::default());
        test_ipa(vec![1, 2, 4, 8], 3, i);
    }

    #[test]
    fn test_kary_bp_ipa() {
        for k in vec![2, 3, 4] {
            type G = <Bls12_381 as PairingEngine>::G1Projective;
            let base = ipa_send::SendIpa::<G>::default();
            let i = bp_rec_kary::KaryBp::<G, ipa_send::SendIpa<G>>::new(k, base);
            test_ipa(vec![1, 2, 4, 8], 1, i);
        }
    }

    pub fn test_reduction<R: Reduction>(
        r: &R,
        x: <R::From as Relation>::Inst,
        w: <R::From as Relation>::Wit,
    ) {
        let c = <R::From as Relation>::size(&x);
        let p_fs_rng = &mut test_fs_rng();
        let v_fs_rng = &mut test_fs_rng();
        let s_fs_rng = &mut test_fs_rng();
        let pp = r.setup(&c, s_fs_rng);
        let (pf, p_x_2, p_w_2) = r.prove(&pp, &x, &w, p_fs_rng);
        <R::To as Relation>::check(&p_x_2, &p_w_2);
        let v_x_2 = r.verify(&pp, &x, &pf, v_fs_rng);
        <R::To as Relation>::check(&v_x_2, &p_w_2);
    }

    pub fn test_fs_rng() -> FiatShamirRng {
        let rng = &mut ark_std::test_rng();
        let fs_seed: [u8; 32] = rng.gen();
        FiatShamirRng::from_seed(&fs_seed)
    }

    pub fn test_proof<R: Relation, P: Proof<R>>(
        sys: &P,
        x: <R as Relation>::Inst,
        w: <R as Relation>::Wit,
    ) where
        <R as Relation>::Inst: std::fmt::Debug + Eq,
    {
        let c = R::size(&x);
        let p_fs_rng = &mut test_fs_rng();
        let v_fs_rng = &mut test_fs_rng();
        let s_fs_rng = &mut test_fs_rng();
        let pp = sys.setup(&c, s_fs_rng);
        let pf = sys.prove(&pp, &x, &w, p_fs_rng);
        sys.verify(&pp, &x, &pf, v_fs_rng);
    }

    #[test]
    fn test_bp_ipa_pallas() {
        type G = ark_pallas::Projective;
        let i = bp_iter::Bp::<G>::default();
        test_ipa(vec![1, 2, 4, 8, 16], 1, i);
    }

    #[test]
    fn test_bp_ipa_vesta() {
        type G = ark_pallas::Projective;
        let i = bp_iter::Bp::<G>::default();
        test_ipa(vec![1, 2, 4, 8, 16], 1, i);
    }

    mod benches {
        use super::*;
        use rust_test::Bencher;

        #[bench]
        fn bp_ipa_bls_g1(b: &mut Bencher) {
            let i = bp_iter::Bp::<<Bls12_381 as PairingEngine>::G1Projective>::default();
            bench_ipa(16, i, b);
        }

        #[bench]
        fn bp_ipa_pallas(b: &mut Bencher) {
            let i = bp_iter::Bp::<ark_pallas::Projective>::default();
            bench_ipa(16, i, b);
        }

        #[bench]
        fn bp_ipa_vesta(b: &mut Bencher) {
            let i = bp_iter::Bp::<ark_vesta::Projective>::default();
            bench_ipa(16, i, b);
        }

        pub fn bench_ipa<G: Group, I: Proof<IpaRelation<G>>>(size: usize, i: I, b: &mut Bencher) {
            let rng = &mut ark_std::test_rng();
            let (instance, witness) = IpaInstance::<G>::sample_from_length(rng, size);
            let pp = i.setup(&size, rng);
            IpaRelation::check(&instance, &witness);
            let fs_seed: [u8; 32] = rng.gen();
            b.iter(|| {
                let mut fs_rng = FiatShamirRng::from_seed(&fs_seed);
                let proof = i.prove(&pp, &instance, &witness, &mut fs_rng);
                let mut fs_rng = FiatShamirRng::from_seed(&fs_seed);
                i.verify(&pp, &instance, &proof, &mut fs_rng);
            })
        }
    }
}
