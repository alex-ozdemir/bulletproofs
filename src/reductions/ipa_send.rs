use crate::{
    relations::ipa::{IpaRelation, IpaWitness},
    reductions::combinator::True,
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
    type Proof = (G::ScalarField, G::ScalarField);
    fn prove(
        &self,
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
}

#[cfg(test)]
mod test {
    use crate::{
        test::test_reduction,
        relations::ipa::{IpaInstance, IpaRelation},
        Reduction,
        Relation,
    };
    use super::SendIpa;
    use ark_ec::group::Group;
    fn test_ipa<G: Group, I: Reduction<From=IpaRelation<G>>>(sizes: Vec<usize>, reps: usize, i: I) {
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
}
