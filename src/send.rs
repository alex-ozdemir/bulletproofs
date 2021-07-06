use ark_ec::group::Group;
use std::marker::PhantomData;
use crate::{IpaWitness, IpaInstance, Ipa, FiatShamirRng};

pub struct SendIpa<G>(PhantomData<G>);

impl<G> std::default::Default for SendIpa<G> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<G: Group> Ipa<G> for SendIpa<G> {
    type Proof = IpaWitness<G::ScalarField>;

    fn prove(
        _instance: &IpaInstance<G>,
        witness: &IpaWitness<G::ScalarField>,
        _fs: &mut FiatShamirRng,
    ) -> Self::Proof {
        witness.clone()
    }

    fn check(instance: &IpaInstance<G>, proof: &Self::Proof, _fs: &mut FiatShamirRng) -> bool {
        Self::check_witness(&instance, &proof)
    }
}
