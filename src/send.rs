use crate::{FiatShamirRng, Ipa, IpaInstance, IpaWitness};
use ark_ec::group::Group;
use std::marker::PhantomData;

pub struct SendIpa<G>(PhantomData<G>);

impl<G> std::default::Default for SendIpa<G> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<G: Group> Ipa<G> for SendIpa<G> {
    type Proof = IpaWitness<G::ScalarField>;

    fn prove(
        &self,
        _instance: &IpaInstance<G>,
        witness: &IpaWitness<G::ScalarField>,
        _fs: &mut FiatShamirRng,
    ) -> Self::Proof {
        witness.clone()
    }

    fn check(
        &self,
        instance: &IpaInstance<G>,
        proof: &Self::Proof,
        _fs: &mut FiatShamirRng,
    ) -> bool {
        self.check_witness(&instance, &proof)
    }
}
