use super::ipa::{IpaGens, IpaInstance, IpaWitness};
use crate::{
    curves::{AffCoords, Pair},
    util::{msm, neg_powers, powers, CollectIter},
    Relation,
};
use ark_ec::{group::Group, ProjectiveCurve};
use derivative::Derivative;
use std::iter::once;
use std::marker::PhantomData;

#[derive(Derivative)]
#[derivative(
    Clone(bound = ""),
    Debug(bound = ""),
    PartialEq(bound = ""),
    Eq(bound = "")
)]
/// Represents the predicate that must be proved after unrolling the k-ary BP protocol for r rounds
/// with the prover committing to the cross-terms in each round.
pub struct UnrolledBpInstance<C: Pair> {
    /// Number of chunks per round
    pub k: usize,
    /// Number of rounds
    pub r: usize,
    /// Generators that remain
    pub gens: IpaGens<C::G1>,
    /// Challenges that were used
    pub challs: Vec<C::TopField>,
    /// Commitments to cross-terms
    /// Each commitments is to the positive terms and then the negative terms
    pub commits: Vec<C::G2>,
    /// Commit
    pub commit_gens: Vec<Vec<C::G2>>,
    /// The original result: w/o cross-terms folded in
    pub result: C::G1,
}

#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
pub struct CrossTerms<G: Group> {
    pub pos: Vec<G>,
    pub neg: Vec<G>,
}

impl<P: AffCoords + ProjectiveCurve> CrossTerms<P> {
    /// Returns all cross terms in a list of affine coordinates.
    /// The order is x then y for all positive, then negative, terms
    pub fn to_aff_coord_list(&self) -> Vec<<P as AffCoords>::BaseField> {
        self.pos
            .iter()
            .chain(&self.neg)
            .flat_map(|proj| {
                let (x, y) = proj.get_xy();
                once(x).chain(once(y))
            })
            .collect()
    }
}

#[derive(Derivative)]
#[derivative(Clone(bound = ""))]
pub struct UnrolledBpWitness<G: Group> {
    pub a: Vec<G::ScalarField>,
    pub b: Vec<G::ScalarField>,
    pub cross_terms: Vec<CrossTerms<G>>,
}

pub struct UnrollRelation<C: Pair>(pub PhantomData<C>);

impl<C: Pair> Relation for UnrollRelation<C> {
    type Inst = UnrolledBpInstance<C>;
    type Wit = UnrolledBpWitness<C::G1>;
    fn check(instance: &Self::Inst, witness: &Self::Wit) {
        let left = instance.result
            + msm(
                &(0..instance.r)
                    .flat_map(|i| {
                        witness.cross_terms[i]
                            .pos
                            .iter()
                            .chain(&witness.cross_terms[i].neg)
                            .cloned()
                    })
                    .vcollect(),
                &(0..instance.r)
                    .flat_map(|i| {
                        powers(instance.challs[i], 1..instance.k)
                            .into_iter()
                            .chain(neg_powers(instance.challs[i], 1..instance.k))
                    })
                    .vcollect(),
            );
        let residual_witness = IpaWitness {
            a: witness.a.clone(),
            b: witness.b.clone(),
        };
        let right = instance.gens.commit_for_witness(&residual_witness);
        assert_eq!(left, right);
        for i in 0..instance.r {
            let aff_coords = witness.cross_terms[i].to_aff_coord_list();
            let computed_commit = msm(&instance.commit_gens[i], &aff_coords);
            assert_eq!(computed_commit, instance.commits[i]);
        }
    }
}

impl<G: Group> UnrolledBpWitness<G> {
    pub fn from_ipa<C: Pair<G1 = G>>(
        k: usize,
        instance: &IpaInstance<G>,
        witness: &IpaWitness<G::ScalarField>,
    ) -> (UnrolledBpInstance<C>, Self) {
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
                cross_terms: vec![],
            },
        )
    }
}

impl<C: Pair> UnrolledBpInstance<C> {
    pub fn from_ipa(k: usize, instance: &IpaInstance<C::G1>) -> Self {
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
