use crate::{
    reductions::combinator::True,
    relations::ipa::{IpaRelation, IpaWitness},
    FiatShamirRng, Reduction, Relation,
};
use ark_ec::group::Group;
use derivative::Derivative;
use std::marker::PhantomData;

#[derive(Derivative)]
#[derivative(Default(bound = ""))]
pub struct SendIpa<G: Group>(pub PhantomData<G>);

impl<G: Group> Reduction for SendIpa<G> {
    type From = IpaRelation<G>;
    type To = True;
    type Params = ();
    type Proof = (G::ScalarField, G::ScalarField);
    fn prove(
        &self,
        _pp: &Self::Params,
        _instance: &<Self::From as Relation>::Inst,
        witness: &<Self::From as Relation>::Wit,
        _fs: &mut FiatShamirRng,
    ) -> (
        Self::Proof,
        <Self::To as Relation>::Inst,
        <Self::To as Relation>::Wit,
    ) {
        assert_eq!(witness.a.len(), 1, "Can only send size-1 IPAs");
        let a = witness.a.last().unwrap().clone();
        let b = witness.b.last().unwrap().clone();
        ((a, b), (), ())
    }
    fn verify(
        &self,
        _pp: &Self::Params,
        instance: &<Self::From as Relation>::Inst,
        (ref a, ref b): &Self::Proof,
        _fs: &mut FiatShamirRng,
    ) -> <Self::To as Relation>::Inst {
        let w = IpaWitness {
            a: vec![a.clone()],
            b: vec![b.clone()],
        };
        IpaRelation::check(&instance, &w);
        ()
    }
    fn proof_size(_p: &Self::Proof) -> usize {
        2
    }
    fn setup<R: rand::Rng>(&self, _: &<IpaRelation<G> as Relation>::Cfg, _: &mut R) -> Self::Params {
        ()
    }
    fn map_params(&self, _: &<IpaRelation<G> as Relation>::Cfg) -> () {
        ()
    }
}

#[cfg(test)]
mod test {
    use super::SendIpa;
    use crate::{
        relations::ipa::{IpaInstance, IpaRelation},
        test::test_reduction,
        Reduction, Relation,
    };
    use ark_ec::group::Group;
    fn test_ipa<G: Group, I: Reduction<From = IpaRelation<G>>>(
        sizes: Vec<usize>,
        reps: usize,
        i: I,
    ) {
        let rng = &mut ark_std::test_rng();
        for size in sizes {
            for _ in 0..reps {
                let (instance, witness) = IpaInstance::<G>::sample_from_length(rng, size);
                IpaRelation::check(&instance, &witness);
                test_reduction(&i, instance, witness);
            }
        }
    }
    #[test]
    fn test_bls() {
        type G = ark_bls12_381::G1Projective;
        let i = SendIpa::<G>::default();
        test_ipa(vec![1], 4, i);
    }
    #[test]
    fn test_pallas() {
        type G = ark_pallas::Projective;
        let i = SendIpa::<G>::default();
        test_ipa(vec![1], 4, i);
    }
    #[test]
    fn test_vesta() {
        type G = ark_vesta::Projective;
        let i = SendIpa::<G>::default();
        test_ipa(vec![1], 4, i);
    }
}
