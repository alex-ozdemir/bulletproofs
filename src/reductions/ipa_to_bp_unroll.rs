use crate::{
    curves::Pair,
    relations::{
        bp_unroll::{CrossTerms, UnrollRelation, UnrolledBpInstance, UnrolledBpWitness},
        ipa::IpaRelation,
    },
    timed,
    util::{
        ip, msm, neg_powers, powers, rand_vec, scale_vec, sum_vecs, zero_intersperse_to_multiple,
        CollectIter,
    },
    FiatShamirRng, Reduction, Relation,
};
use ark_ec::group::Group;
use ark_ff::{Field, One, PrimeField, UniformRand};
use log::debug;
use std::iter::once;
use std::marker::PhantomData;
use ark_std::{start_timer, end_timer};

fn compute_bp_unroll_msms<G: Group>(v: &[G], k: usize, challenges: &[G::ScalarField]) -> Vec<G> {
    let timer = start_timer!(|| "unroll scalars");
    let mut groups: Vec<Vec<(G, G::ScalarField)>> = v
        .iter()
        .map(|g| vec![(g.clone(), G::ScalarField::one())])
        .vcollect();
    let r = challenges.len();
    let n_end = (v.len() - 1) / k.pow(r as u32) + 1;
    for c in challenges {
        let c_pows = powers(*c, 0..k);
        let n_bkts = (groups.len() - 1) / k + 1;
        let full_chunk_size = n_bkts;
        let n_chunks = k;
        let n_not_full_chunks = n_bkts * n_chunks - groups.len();
        assert!(n_not_full_chunks < n_chunks);
        let n_full_chunks = n_chunks - n_not_full_chunks;
        let mut bkts = vec![Vec::new(); n_bkts];
        groups.reverse();
        for chunk_i in 0..k {
            let mut mult = G::ScalarField::one();
            let chunk_size = full_chunk_size - if chunk_i < n_full_chunks { 0 } else { 1 };
            for bkt_i in 0..chunk_size {
                let gp = groups.pop().unwrap();
                bkts[bkt_i].extend(gp.into_iter().map(|(g, s)| (g, s * c_pows[chunk_i])));
            }
            mult *= c;
        }
        assert_eq!(groups.len(), 0);
        groups = bkts;
    }
    end_timer!(timer);
    assert_eq!(n_end, groups.len());
    timed!(
        || "msms",
        groups
            .into_iter()
            .enumerate()
            .map(|(_i, gp)| timed!(|| format!("msm{}", _i), {
                let (pts, scalars): (Vec<G>, Vec<_>) = gp.into_iter().unzip();
                msm(&pts, &scalars)
            }))
            .collect()
    )
}

/// Computes the outer product of
///
/// (1, c_i, c_i^2, ..., c_i^(k-1))
///
/// for all i, with c_0 on the outside. That is, adjacent entries in the final vector generally
/// have the same power of c_0.
#[allow(dead_code)]
fn outer_product<F: PrimeField>(k: usize, challenges: &[F]) -> Vec<F> {
    match challenges.first() {
        None => vec![F::one()],
        Some(first) => {
            let v = outer_product(k, &challenges[1..]);
            let ps = powers(*first, 1..k);
            ps.iter().flat_map(|p| scale_vec(p, &v)).collect()
        }
    }
}

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
    type Params = ();
    /// The commitments
    type Proof = Vec<C::G2>;
    fn prove(
        &self,
        _pp: &Self::Params,
        x: &<Self::From as Relation>::Inst,
        w: &<Self::From as Relation>::Wit,
        fs: &mut FiatShamirRng,
    ) -> (
        Self::Proof,
        <Self::To as Relation>::Inst,
        <Self::To as Relation>::Wit,
    ) {
        timed!(|| "proving ipa_unroll", {
            let (mut u_x, mut u_w) = UnrolledBpWitness::from_ipa(self.k, &x, &w);
            prove_unroll(self.r, &mut u_x, &mut u_w, fs);
            (u_x.commits.clone(), u_x, u_w)
        })
    }
    fn verify(
        &self,
        _pp: &Self::Params,
        x: &<Self::From as Relation>::Inst,
        pf: &Self::Proof,
        fs: &mut FiatShamirRng,
    ) -> <Self::To as Relation>::Inst {
        timed!(|| "verifying ipa_unroll", {
            let mut u_x = UnrolledBpInstance::from_ipa(self.k, &x);
            verify_unroll(self.r, &mut u_x, &pf, fs);
            u_x
        })
    }
    fn proof_size(p: &Self::Proof) -> usize {
        p.len()
    }
    fn setup<R: rand::Rng>(
        &self,
        _c: &<Self::From as Relation>::Cfg,
        _rng: &mut R,
    ) -> Self::Params {
        ()
    }
    fn map_params(&self, c: &<Self::From as Relation>::Cfg) -> <Self::To as Relation>::Cfg {
        ((*c - 1) / self.k.pow(self.r as u32) + 1, self.k, self.r)
    }
}

#[allow(unused_variables)]
pub fn prove_unroll<C: Pair>(
    r: usize,
    instance: &mut UnrolledBpInstance<C>,
    witness: &mut UnrolledBpWitness<C::G1>,
    fs: &mut FiatShamirRng,
) {
    for i in 0..r {
        timed!(|| format!("step {}", i), prove_step(instance, witness, fs));
    }
}

pub fn prove_step<C: Pair>(
    instance: &mut UnrolledBpInstance<C>,
    witness: &mut UnrolledBpWitness<C::G1>,
    fs: &mut FiatShamirRng,
) {
    let k = instance.k;
    let a = zero_intersperse_to_multiple(&witness.a, k);
    debug!("Folding {} by {}: pad to {}", witness.a.len(), k, a.len());
    let b = zero_intersperse_to_multiple(&witness.b, k);
    let a_gen = zero_intersperse_to_multiple(&instance.gens.a_gens, k);
    let b_gen = zero_intersperse_to_multiple(&instance.gens.b_gens, k);
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
    // Then the positive cross-term T[i] for i in {0,..,k-2} is
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
    instance.gens.vec_size = (instance.gens.vec_size - 1) / k + 1;
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
    let k = instance.k;
    let n_cross_terms = 2 * (k - 1);
    let n_aff_coords = 2 * n_cross_terms;
    assert_eq!(instance.challs.len(), 0);
    assert_eq!(instance.commit_gens.len(), 0);
    assert_eq!(instance.r, 0);

    for i in 0..r {
        // generate cross term commitment generators
        instance.commit_gens.push(rand_vec(n_aff_coords, fs));

        // recieve cross-term commitment
        instance.commits.push(pf[i].clone());
        fs.absorb(&pf[i]);

        // sample challenge
        instance.challs.push(C::TopField::rand(fs));
    }

    assert_eq!(instance.challs.len(), r);
    assert_eq!(instance.commit_gens.len(), r);

    let chall_invs = instance
        .challs
        .iter()
        .map(|c| c.inverse().unwrap())
        .vcollect();
    let a_gen_next = compute_bp_unroll_msms(&instance.gens.a_gens, k, &chall_invs);
    let b_gen_next = compute_bp_unroll_msms(&instance.gens.b_gens, k, &instance.challs);
    let nxt_size = (instance.gens.vec_size - 1) / k.pow(r as u32) + 1;
    assert_eq!(nxt_size, a_gen_next.len());
    assert_eq!(nxt_size, b_gen_next.len());
    instance.gens.vec_size = a_gen_next.len();
    instance.gens.a_gens = a_gen_next;
    instance.gens.b_gens = b_gen_next;
    instance.r = r;
}

pub fn verify_step<C: Pair>(
    instance: &mut UnrolledBpInstance<C>,
    commit: &C::G2,
    fs: &mut FiatShamirRng,
) {
    let k = instance.k;
    let a_gen = zero_intersperse_to_multiple(&instance.gens.a_gens, k);
    let b_gen = zero_intersperse_to_multiple(&instance.gens.b_gens, k);
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
    instance.gens.vec_size = (instance.gens.vec_size - 1) / k + 1;
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
        let pp = reducer.setup(&init_size, rng);
        let (proof, u_instance, u_witness) = reducer.prove(&pp, &instance, &witness, &mut fs_rng);
        UnrollRelation::check(&u_instance, &u_witness);
        let verif_u_instance = reducer.verify(&pp, &instance, &proof, &mut v_fs_rng);
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
