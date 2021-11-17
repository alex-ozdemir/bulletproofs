use crate::{
    relations::ipa::{IpaInstance, IpaRelation, IpaWitness},
    FiatShamirRng, Proof, Relation,
};
use ark_ec::group::Group;
use std::marker::PhantomData;

pub struct SendIpa<G>(PhantomData<G>);

impl<G> std::default::Default for SendIpa<G> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<G: Group> Proof<IpaRelation<G>> for SendIpa<G> {
    type Params = ();
    type Proof = IpaWitness<G::ScalarField>;

    fn prove(
        &self,
        _pp: &Self::Params,
        _instance: &IpaInstance<G>,
        witness: &IpaWitness<G::ScalarField>,
        _fs: &mut FiatShamirRng,
    ) -> Self::Proof {
        witness.clone()
    }

    fn verify(
        &self,
        _pp: &Self::Params,
        instance: &IpaInstance<G>,
        proof: &Self::Proof,
        _fs: &mut FiatShamirRng,
    ) {
        IpaRelation::check(&instance, &proof);
    }

    fn setup<Rn: rand::Rng>(&self, _: &<IpaRelation<G> as Relation>::Cfg, _: &mut Rn) -> Self::Params {
        ()
    }

    fn proof_size(p: &Self::Proof) -> usize {
        p.a.len() + p.b.len()
    }
}
