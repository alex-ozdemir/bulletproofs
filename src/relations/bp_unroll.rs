use super::ipa::{IpaGens, IpaInstance, IpaWitness};
use crate::Relation;
use ark_ec::group::Group;
use ark_ec::{twisted_edwards_extended::GroupProjective, TEModelParameters};
use std::marker::PhantomData;

#[derive(Clone)]
/// Represents the predicate that must be proved after unrolling the k-ary BP protocol for r rounds
/// with the prover committing to the cross-terms in each round.
pub struct UnrolledBpInstance<G: Group> {
    /// Number of chunks per round
    pub k: usize,
    /// Number of rounds
    pub r: usize,
    /// Generators that remain
    pub gens: IpaGens<G>,
    /// Challenges that were used
    pub challs: Vec<G::ScalarField>,
    /// Commitments to cross-terms
    /// Each commitments is to the positive terms and then the negative terms
    pub commits: Vec<G>,
    /// The original result: w/o cross-terms folded in
    pub result: G,
}

pub struct UnrolledBpWitness<P: TEModelParameters> {
    pub a: Vec<P::ScalarField>,
    pub b: Vec<P::ScalarField>,
    pub pos_cross_terms: Vec<Vec<GroupProjective<P>>>,
    pub neg_cross_terms: Vec<Vec<GroupProjective<P>>>,
}

pub struct UnrollRelation<P: TEModelParameters>(pub PhantomData<P>);

impl<P: TEModelParameters> Relation for UnrollRelation<P> {
    type Inst = UnrolledBpInstance<GroupProjective<P>>;
    type Wit = UnrolledBpWitness<P>;
    fn check(_instance: &Self::Inst, _witness: &Self::Wit) {
        unimplemented!()
    }
}

impl<P: TEModelParameters> UnrolledBpWitness<P> {
    pub fn from_ipa(
        k: usize,
        instance: &IpaInstance<GroupProjective<P>>,
        witness: &IpaWitness<P::ScalarField>,
    ) -> (UnrolledBpInstance<GroupProjective<P>>, Self) {
        (
            UnrolledBpInstance {
                k,
                r: 0,
                gens: instance.gens.clone(),
                challs: vec![],
                commits: vec![],
                result: instance.result,
            },
            UnrolledBpWitness {
                a: witness.a.clone(),
                b: witness.b.clone(),
                pos_cross_terms: vec![],
                neg_cross_terms: vec![],
            },
        )
    }
}
