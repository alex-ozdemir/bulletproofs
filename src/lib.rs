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

pub trait Relation {
    type Inst;
    type Wit;
    fn check(x: &Self::Inst, w: &Self::Wit);
}

pub trait SampleableRelation: Relation {
    type Params;
    fn sample<R: Rng>(p: &Self::Params, rng: &mut R) -> Self;
}

pub trait Reduction {
    type From: Relation;
    type To: Relation;
    type Proof;
    fn prove(
        &self,
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
        x: &<Self::From as Relation>::Inst,
        pf: &Self::Proof,
        fs: &mut FiatShamirRng,
    ) -> <Self::To as Relation>::Inst;
    /// Return the number of field or group elements in a seralized proof.
    fn proof_size(p: &Self::Proof) -> usize;
}

pub trait Proof<R: Relation> {
    type Proof;
    fn prove(
        &self,
        x: &<R as Relation>::Inst,
        w: &<R as Relation>::Wit,
        fs: &mut FiatShamirRng,
    ) -> Self::Proof;
    fn verify(&self, x: &<R as Relation>::Inst, pf: &Self::Proof, fs: &mut FiatShamirRng);
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
            IpaRelation::check(&instance, &witness);
            let fs_seed: [u8; 32] = rng.gen();
            let mut fs_rng = FiatShamirRng::from_seed(&fs_seed);
            let proof = i.prove(&instance, &witness, &mut fs_rng);
            let proof_size = I::proof_size(&proof);
            debug!("Proof size: {}", proof_size);
            let mut fs_rng = FiatShamirRng::from_seed(&fs_seed);
            i.verify(&instance, &proof, &mut fs_rng);
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
    IpaRelation::check(&instance, &witness);
    let fs_seed: [u8; 32] = rng.gen();
    let mut fs_rng = FiatShamirRng::from_seed(&fs_seed);
    let proof = i.prove(&instance, &witness, &mut fs_rng);
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
    //IpaRelation::check(&instance, &witness);
    let fs_seed: [u8; 32] = rng.gen();
    let mut fs_rng = FiatShamirRng::from_seed(&fs_seed);
    let (_proof, x, _w) = reduction.prove(&instance, &witness, &mut fs_rng);
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
        test_ipa(vec![1, 2, 4, 8, 16], 1, i);
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
            dbg!(&k);
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
        let p_fs_rng = &mut test_fs_rng();
        let v_fs_rng = &mut test_fs_rng();
        let (pf, p_x_2, p_w_2) = r.prove(&x, &w, p_fs_rng);
        <R::To as Relation>::check(&p_x_2, &p_w_2);
        let v_x_2 = r.verify(&x, &pf, v_fs_rng);
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
        let p_fs_rng = &mut test_fs_rng();
        let v_fs_rng = &mut test_fs_rng();
        let pf = sys.prove(&x, &w, p_fs_rng);
        sys.verify(&x, &pf, v_fs_rng);
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
            IpaRelation::check(&instance, &witness);
            let fs_seed: [u8; 32] = rng.gen();
            b.iter(|| {
                let mut fs_rng = FiatShamirRng::from_seed(&fs_seed);
                let proof = i.prove(&instance, &witness, &mut fs_rng);
                let mut fs_rng = FiatShamirRng::from_seed(&fs_seed);
                i.verify(&instance, &proof, &mut fs_rng);
            })
        }
    }
}
