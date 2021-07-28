use super::ipa::{IpaGens, IpaInstance, IpaWitness};
use crate::{curves::TEPair, Relation};
use ark_ec::{twisted_edwards_extended::GroupProjective, ModelParameters, TEModelParameters};
use derivative::Derivative;
use std::marker::PhantomData;

#[derive(Clone, Derivative)]
#[derivative(Debug(bound = ""), PartialEq(bound = ""), Eq(bound = ""))]
/// Represents the predicate that must be proved after unrolling the k-ary BP protocol for r rounds
/// with the prover committing to the cross-terms in each round.
pub struct UnrolledBpInstance<P: TEPair> {
    /// Number of chunks per round
    pub k: usize,
    /// Number of rounds
    pub r: usize,
    /// Generators that remain
    pub gens: IpaGens<GroupProjective<P::P1>>,
    /// Challenges that were used
    pub challs: Vec<<P::P1 as ModelParameters>::ScalarField>,
    /// Commitments to cross-terms
    /// Each commitments is to the positive terms and then the negative terms
    pub commits: Vec<P::G2>,
    /// Commit
    pub commit_gens: Vec<Vec<P::G2>>,
    /// The original result: w/o cross-terms folded in
    pub result: GroupProjective<P::P1>,
}

pub struct UnrolledBpWitness<P: TEModelParameters> {
    pub a: Vec<P::ScalarField>,
    pub b: Vec<P::ScalarField>,
    pub pos_cross_terms: Vec<Vec<GroupProjective<P>>>,
    pub neg_cross_terms: Vec<Vec<GroupProjective<P>>>,
}

pub struct UnrollRelation<P: TEPair>(pub PhantomData<P>);

impl<P: TEPair> Relation for UnrollRelation<P> {
    type Inst = UnrolledBpInstance<P>;
    type Wit = UnrolledBpWitness<P::P1>;
    fn check(_instance: &Self::Inst, _witness: &Self::Wit) {
        unimplemented!()
    }
}

impl<P1: TEModelParameters> UnrolledBpWitness<P1> {
    pub fn from_ipa<P: TEPair<P1 = P1>>(
        k: usize,
        instance: &IpaInstance<GroupProjective<P1>>,
        witness: &IpaWitness<P1::ScalarField>,
    ) -> (UnrolledBpInstance<P>, Self) {
        (
            UnrolledBpInstance {
                k,
                r: 0,
                gens: instance.gens.clone(),
                challs: vec![],
                commits: vec![],
                result: instance.result,
                commit_gens: vec![],
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

impl<P: TEPair> UnrolledBpInstance<P> {
    pub fn from_ipa(k: usize, instance: &IpaInstance<GroupProjective<P::P1>>) -> Self {
        UnrolledBpInstance {
            k,
            r: 0,
            gens: instance.gens.clone(),
            challs: vec![],
            commits: vec![],
            result: instance.result,
            commit_gens: vec![],
        }
    }
}
