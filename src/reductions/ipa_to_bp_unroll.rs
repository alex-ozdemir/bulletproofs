use crate::{
    curves::Pair,
    relations::{
        bp_unroll::{CrossTerms, UnrollRelation, UnrolledBpInstance, UnrolledBpWitness},
        ipa::IpaRelation,
    },
    util::{
        ip, msm, neg_powers, powers, rand_vec, scale_vec, sum_vecs, zero_pad_to_multiple,
        CollectIter,
    },
    FiatShamirRng, Reduction, Relation,
};
use ark_ff::{One, UniformRand};
use std::iter::once;
use std::marker::PhantomData;

pub struct IpaToBpUnroll<C: Pair> {
    pub k: usize,
    pub r: usize,
    pub _phants: PhantomData<C>,
}

impl<C: Pair> IpaToBpUnroll<C> {
    pub fn new(k: usize, r: usize) -> Self {
        Self {
            k,
            r,
            _phants: Default::default(),
        }
    }
}

impl<C: Pair> Reduction for IpaToBpUnroll<C> {
    type From = IpaRelation<C::G1>;
    type To = UnrollRelation<C>;
    /// The commitments
    type Proof = Vec<C::G2>;
    fn prove(
        &self,
        x: &<Self::From as Relation>::Inst,
        w: &<Self::From as Relation>::Wit,
        fs: &mut FiatShamirRng,
    ) -> (
        Self::Proof,
        <Self::To as Relation>::Inst,
        <Self::To as Relation>::Wit,
    ) {
        let (mut u_x, mut u_w) = UnrolledBpWitness::from_ipa(self.k, &x, &w);
        prove_unroll(self.r, &mut u_x, &mut u_w, fs);
        (u_x.commits.clone(), u_x, u_w)
    }
    fn verify(
        &self,
        x: &<Self::From as Relation>::Inst,
        pf: &Self::Proof,
        fs: &mut FiatShamirRng,
    ) -> <Self::To as Relation>::Inst {
        let mut u_x = UnrolledBpInstance::from_ipa(self.k, &x);
        verify_unroll(self.r, &mut u_x, &pf, fs);
        u_x
    }
    fn proof_size(p: &Self::Proof) -> usize {
        p.len()
    }
}

pub fn prove_unroll<C: Pair>(
    r: usize,
    instance: &mut UnrolledBpInstance<C>,
    witness: &mut UnrolledBpWitness<C::G1>,
    fs: &mut FiatShamirRng,
) {
    for _ in 0..r {
        prove_step(instance, witness, fs);
    }
}

pub fn prove_step<C: Pair>(
    instance: &mut UnrolledBpInstance<C>,
    witness: &mut UnrolledBpWitness<C::G1>,
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
    let a = a.chunks_exact(ck_size).vcollect();
    let b = b.chunks_exact(ck_size).vcollect();
    let a_gen = a_gen.chunks_exact(ck_size).vcollect();
    let b_gen = b_gen.chunks_exact(ck_size).vcollect();

    // Compute cross-terms
    // Let X[i,j] = a[i]*A[j] + b[j]*B[i] + <a[i],b[j]>*Q
    let x = |i: usize, j: usize| {
        msm(
            a_gen[j].iter().chain(b_gen[i]).chain(once(&q)),
            a[i].iter().chain(b[j]).chain(once(&ip(&a[i], &b[j]))),
        )
    };
    // Then the positive cross-term T[i] for i in {0,..,k-2{ is
    // \sum j={1,..k-i} X[i+j,j]
    // should be multiplied by x^(i+1)
    let pos_cross: Vec<C::G1> = (0..k - 1)
        .map(|i| {
            let xs = (0..k - i - 1).map(|j| x(i + j + 1, j)).vcollect();
            debug_assert_eq!(xs.len(), k - 1 - i);
            xs.into_iter().sum::<C::G1>().into()
        })
        .collect();
    // Then the negative cross-term T[-i] for i in {0,..,k-2} is
    // \sum j={1,..k-i} X[i+j,j]
    // should be multiplied by x^-(i+1)
    let neg_cross: Vec<C::G1> = (0..k - 1)
        .map(|i| {
            (0..k - i - 1)
                .map(|j| x(j, i + j + 1))
                .sum::<C::G1>()
                .into()
        })
        .collect();
    let cross = CrossTerms {
        pos: pos_cross,
        neg: neg_cross,
    };

    let n_cross_terms = 2 * (k - 1);
    let n_aff_coords = 2 * n_cross_terms;

    let commit_gens: Vec<C::G2> = rand_vec(n_aff_coords, fs);
    let aff_coords = cross.to_aff_coord_list();
    let commit: C::G2 = msm(&commit_gens, &aff_coords);

    fs.absorb(&commit);
    let one = C::TopField::one();
    let x = C::TopField::rand(fs);

    // Fold everything in response to challenges...
    let x_pows = powers(x, 0..k);
    let x_inv_pows = neg_powers(x, 0..k);
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
    instance.commits.push(commit);
    instance.commit_gens.push(commit_gens);
    instance.r += 1;
    witness.cross_terms.push(cross);
    witness.a = a_next;
    witness.b = b_next;
}

pub fn verify_unroll<C: Pair>(
    r: usize,
    instance: &mut UnrolledBpInstance<C>,
    pf: &[C::G2],
    fs: &mut FiatShamirRng,
) {
    assert_eq!(pf.len(), r);
    for i in 0..r {
        verify_step(instance, &pf[i], fs);
    }
}

pub fn verify_step<C: Pair>(
    instance: &mut UnrolledBpInstance<C>,
    commit: &C::G2,
    fs: &mut FiatShamirRng,
) {
    let k = instance.k;
    let a_gen = zero_pad_to_multiple(&instance.gens.a_gens, k);
    let b_gen = zero_pad_to_multiple(&instance.gens.b_gens, k);
    debug_assert_eq!(a_gen.len() % k, 0);
    debug_assert_eq!(b_gen.len() % k, 0);

    // chunk them
    let ck_size = a_gen.len() / k;
    let a_gen = a_gen.chunks_exact(ck_size).vcollect();
    let b_gen = b_gen.chunks_exact(ck_size).vcollect();

    // generate cross term commitment generators
    let n_cross_terms = 2 * (k - 1);
    let n_aff_coords = 2 * n_cross_terms;

    let commit_gens: Vec<C::G2> = rand_vec(n_aff_coords, fs);

    // recieve cross-term commitment
    fs.absorb(&commit);

    let x = C::TopField::rand(fs);
    // Fold everything in response to challenges...
    let x_pows = powers(x, 0..k);
    let x_inv_pows = neg_powers(x, 0..k);
    let a_gen_next = sum_vecs(
        a_gen.iter().zip(&x_inv_pows).map(|(c, y)| scale_vec(y, c)),
        ck_size,
    );
    let b_gen_next = sum_vecs(
        b_gen.iter().zip(&x_pows).map(|(c, y)| scale_vec(y, c)),
        ck_size,
    );
    instance.gens.a_gens = a_gen_next;
    instance.gens.b_gens = b_gen_next;
    instance.gens.vec_size /= k;
    instance.challs.push(x);
    instance.commits.push(commit.clone());
    instance.commit_gens.push(commit_gens);
    instance.r += 1;
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        curves::{
            models::{JubJubPair, PastaPair, VellasPair},
            Pair,
        },
        reductions::ipa_to_bp_unroll::IpaToBpUnroll,
        relations::ipa::IpaInstance,
    };
    use rand::Rng;
    fn unroll_check<C: Pair>(init_size: usize, k: usize, r: usize) {
        println!(
            "doing a unrolled circuit check with {} elems, k: {}, r: {}",
            init_size, k, r
        );
        let rng = &mut ark_std::test_rng();
        let fs_seed: [u8; 32] = rng.gen();
        let mut fs_rng = crate::FiatShamirRng::from_seed(&fs_seed);
        let mut v_fs_rng = crate::FiatShamirRng::from_seed(&fs_seed);
        let (instance, witness) = IpaInstance::<C::G1>::sample_from_length(rng, init_size);
        let reducer = IpaToBpUnroll::<C>::new(k, r);
        let (proof, u_instance, u_witness) = reducer.prove(&instance, &witness, &mut fs_rng);
        UnrollRelation::check(&u_instance, &u_witness);
        let verif_u_instance = reducer.verify(&instance, &proof, &mut v_fs_rng);
        assert_eq!(verif_u_instance, u_instance);
        UnrollRelation::check(&verif_u_instance, &u_witness);
    }

    #[test]
    fn jubjub_unroll_test() {
        unroll_check::<JubJubPair>(4, 2, 1);
        unroll_check::<JubJubPair>(8, 2, 2);
        unroll_check::<JubJubPair>(8, 2, 3);
        unroll_check::<JubJubPair>(9, 3, 1);
        unroll_check::<JubJubPair>(9, 3, 2);
        //unroll_check::<JubJubPair>(2048, 4, 4);
        //unroll_check::<JubJubPair>(2048, 4, 5);
    }
    #[test]
    fn pasta_unroll_test() {
        unroll_check::<PastaPair>(4, 2, 1);
        unroll_check::<PastaPair>(8, 2, 2);
        unroll_check::<PastaPair>(8, 2, 3);
        unroll_check::<PastaPair>(9, 3, 1);
        unroll_check::<PastaPair>(9, 3, 2);
        //unroll_check::<PastaPair>(2048, 4, 4);
        //unroll_check::<PastaPair>(2048, 4, 5);
    }
    #[test]
    fn vellas_unroll_test() {
        unroll_check::<VellasPair>(4, 2, 1);
        unroll_check::<VellasPair>(8, 2, 2);
        unroll_check::<VellasPair>(8, 2, 3);
        unroll_check::<VellasPair>(9, 3, 1);
        unroll_check::<VellasPair>(9, 3, 2);
        //unroll_check::<VellasPair>(2048, 4, 4);
        //unroll_check::<VellasPair>(2048, 4, 5);
    }
}
