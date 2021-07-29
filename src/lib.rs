use std::marker::PhantomData;

pub type FiatShamirRng = ark_marlin::rng::FiatShamirRng<blake2::Blake2s>;

pub mod curves;
pub mod proofs;
pub mod r1cs;
pub mod reductions;
pub mod relations;
pub mod util;

pub trait Relation {
    type Inst;
    type Wit;
    fn check(x: &Self::Inst, w: &Self::Wit);
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
}

pub struct True;

impl Relation for True {
    type Inst = ();
    type Wit = ();
    fn check(_: &Self::Inst, _: &Self::Wit) {
        // always holds
    }
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
}

pub struct TrueReductionToProof<R: Relation, P: Reduction<From = R, To = True>>(
    pub P,
    pub PhantomData<R>,
);

impl<R: Relation, P: Reduction<From = R, To = True>> TrueReductionToProof<R, P> {
    pub fn new(pf: P) -> Self {
        Self(pf, Default::default())
    }
}

impl<R: Relation, P: Reduction<From = R, To = True>> Proof<R> for TrueReductionToProof<R, P> {
    type Proof = <P as Reduction>::Proof;
    fn prove(
        &self,
        x: &<R as Relation>::Inst,
        w: &<R as Relation>::Wit,
        fs: &mut FiatShamirRng,
    ) -> Self::Proof {
        self.0.prove(x, w, fs).0
    }
    fn verify(&self, x: &<R as Relation>::Inst, pf: &Self::Proof, fs: &mut FiatShamirRng) {
        self.0.verify(x, pf, fs);
    }
}

#[cfg(test)]
pub mod test {
    use super::proofs::{bp_iter, bp_rec, bp_rec_kary, ipa_send};
    use super::relations::ipa::{IpaInstance, IpaRelation};
    use super::{FiatShamirRng, Proof, Reduction, Relation};
    use ark_bls12_381::Bls12_381;
    use ark_ec::{group::Group, PairingEngine};
    use rand::Rng;
    fn test_ipa<G: Group, I: Proof<IpaRelation<G>>>(sizes: Vec<usize>, reps: usize, i: I) {
        let rng = &mut ark_std::test_rng();
        for size in sizes {
            for _ in 0..reps {
                let (instance, witness) = IpaInstance::<G>::sample_from_length(rng, size);
                IpaRelation::check(&instance, &witness);
                let fs_seed: [u8; 32] = rng.gen();
                let mut fs_rng = FiatShamirRng::from_seed(&fs_seed);
                let proof = i.prove(&instance, &witness, &mut fs_rng);
                let mut fs_rng = FiatShamirRng::from_seed(&fs_seed);
                i.verify(&instance, &proof, &mut fs_rng);
            }
        }
    }

    #[test]
    fn test_bp_ipa() {
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
}
