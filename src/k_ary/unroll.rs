//! BP relation instances for unrolled protocols with commitments from the prover.

use crate::{
    k_ary::zero_pad_to_multiple,
    util::{ip, msm, scale_vec, sum_vecs},
    FiatShamirRng, IpaGens, IpaInstance, IpaWitness,
};
use ark_ec::group::Group;
use ark_ec::{twisted_edwards_extended::GroupProjective, TEModelParameters};
use ark_ff::{Field, One, UniformRand};

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

pub fn prove_unroll<P: TEModelParameters>(
    r: usize,
    instance: &mut UnrolledBpInstance<GroupProjective<P>>,
    witness: &mut UnrolledBpWitness<P>,
    fs: &mut FiatShamirRng,
) {
    for _ in 0..r {
        prove_step(instance, witness, fs);
    }
}

pub fn prove_step<P: TEModelParameters>(
    instance: &mut UnrolledBpInstance<GroupProjective<P>>,
    witness: &mut UnrolledBpWitness<P>,
    fs: &mut FiatShamirRng,
) {
    let k = instance.k;
    let a = zero_pad_to_multiple(&witness.a, k);
    let b = zero_pad_to_multiple(&witness.b, k);
    let a_gen = zero_pad_to_multiple(&instance.gens.a_gens, k);
    let b_gen = zero_pad_to_multiple(&instance.gens.b_gens, k);
    let q = instance.gens.ip_gen;
    debug_assert_eq!(a.len() % k, 0);
    debug_assert_eq!(b.len() % k, 0);
    debug_assert_eq!(a_gen.len() % k, 0);
    debug_assert_eq!(b_gen.len() % k, 0);

    // chunk them
    let ck_size = a.len() / k;
    let a: Vec<_> = a.chunks_exact(ck_size).collect();
    let b: Vec<_> = b.chunks_exact(ck_size).collect();
    let a_gen: Vec<_> = a_gen.chunks_exact(ck_size).collect();
    let b_gen: Vec<_> = b_gen.chunks_exact(ck_size).collect();

    // Compute cross-terms
    // Let X[i,j] = a[i]*A[j] + b[j]*B[i] + <a[i],b[j]>*Q
    let x = |i: usize, j: usize| {
        msm(&a_gen[j], &a[i]) + msm(&b_gen[i], &b[j]) + q.mul(&ip(&a[i], &b[j]))
    };
    // Then the positive cross-term T[i] for i in {0,..,k-2{ is
    // \sum j={1,..k-i} X[i+j,j]
    // should be multiplied by x^(i+1)
    let pos_cross: Vec<GroupProjective<P>> = (0..k - 1)
        .map(|i| {
            let xs: Vec<_> = (0..k - i - 1).map(|j| x(i + j + 1, j)).collect();
            debug_assert_eq!(xs.len(), k - 1 - i);
            xs.into_iter().sum::<GroupProjective<P>>().into()
        })
        .collect();
    // Then the negative cross-term T[-i] for i in {0,..,k-2} is
    // \sum j={1,..k-i} X[i+j,j]
    // should be multiplied by x^-(i+1)
    let neg_cross: Vec<GroupProjective<P>> = (0..k - 1)
        .map(|i| {
            (0..k - i - 1)
                .map(|j| x(j, i + j + 1))
                .sum::<GroupProjective<P>>()
                .into()
        })
        .collect();

    // TODO: commit and feed FS.
    let one = P::ScalarField::one();
    let x = P::ScalarField::rand(fs);

    // Fold everything in response to challenges...
    let x_inv = x.inverse().unwrap();
    let x_pows: Vec<_> = std::iter::successors(Some(one), |x_i| Some(x * x_i))
        .take(k)
        .collect();
    let x_inv_pows: Vec<_> = std::iter::successors(Some(one), |x_i| Some(x_inv * x_i))
        .take(k)
        .collect();
    debug_assert_eq!(
        one,
        x_pows
            .iter()
            .zip(&x_inv_pows)
            .map(|(a, b)| *a * b)
            .product()
    );

    for (a, b) in x_pows.iter().zip(&x_inv_pows) {
        debug_assert_eq!(*a * b, one);
    }

    let a_next = sum_vecs(a.iter().zip(&x_pows).map(|(c, y)| scale_vec(y, c)), ck_size);
    let b_next = sum_vecs(
        b.iter().zip(&x_inv_pows).map(|(c, y)| scale_vec(y, c)),
        ck_size,
    );
    let a_gen_next = sum_vecs(
        a_gen.iter().zip(&x_inv_pows).map(|(c, y)| scale_vec(y, c)),
        ck_size,
    );
    let b_gen_next = sum_vecs(
        b_gen.iter().zip(&x_pows).map(|(c, y)| scale_vec(y, c)),
        ck_size,
    );

    // only holds for the first round
    // debug_assert_eq!(
    //     msm(&pos_cross, &x_pows[1..]) + p + msm(&neg_cross, &x_inv_pows[1..]),
    //     msm(&a_gen_next, &a_next) + msm(&b_gen_next, &b_next) + q.mul(&ip(&a_next, &b_next))
    // );
    instance.gens.a_gens = a_gen_next;
    instance.gens.b_gens = b_gen_next;
    instance.gens.vec_size /= k;
    instance.challs.push(x);
    // TODO: push commitment
    instance.r += 1;
    witness.pos_cross_terms.push(pos_cross);
    witness.neg_cross_terms.push(neg_cross);
    witness.a = a_next;
    witness.b = b_next;
}
