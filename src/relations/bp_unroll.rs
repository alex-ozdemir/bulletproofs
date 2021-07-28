use super::ipa::{IpaGens, IpaInstance, IpaWitness};
use crate::{
    curves::TEPair,
    util::{msm, neg_powers, powers, CollectIter},
    Relation,
};
use ark_ec::{group::Group, twisted_edwards_extended::{GroupProjective, GroupAffine}, ModelParameters, TEModelParameters};
use derivative::Derivative;
use std::marker::PhantomData;
use std::iter::once;

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
    fn check(instance: &Self::Inst, witness: &Self::Wit) {
        let left = instance.result
            + msm(
                &(0..instance.r)
                    .flat_map(|i| {
                        witness.pos_cross_terms[i]
                            .iter()
                            .chain(&witness.neg_cross_terms[i])
                            .cloned()
                    })
                    .vcollect(),
                &(0..instance.r).flat_map(|i| {
                    powers(instance.challs[i], 1..instance.k)
                        .into_iter()
                        .chain(neg_powers(instance.challs[i], 1..instance.k))
                }).vcollect(),
            );
        let residual_witness = IpaWitness {
            a: witness.a.clone(),
            b: witness.b.clone(),
        };
        let right = instance.gens.commit_for_witness(&residual_witness);
        assert_eq!(left, right);
        for i in 0..instance.r {
            let aff_coords: Vec<<P::G2 as Group>::ScalarField> = witness.pos_cross_terms[i]
                .iter()
                .chain(&witness.neg_cross_terms[i])
                .flat_map(|proj| {
                    let aff: GroupAffine<P::P1> = proj.clone().into();
                    once(aff.x).chain(once(aff.y))
                })
                .collect();
            let computed_commit = msm(&instance.commit_gens[i], &aff_coords);
            assert_eq!(computed_commit, instance.commits[i]);
        }
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
