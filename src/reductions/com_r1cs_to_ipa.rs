use crate::{
    relations::{
        com_r1cs::{mat_vec_mult, vec_mat_mult, ComR1csRelation},
        ipa::{IpaGens, IpaInstance, IpaRelation, IpaWitness},
    },
    util::{hadamard, hadamard_gp, ip, msm, rand_vec, scale_vec, sum_vecs, CollectIter},
    FiatShamirRng, Reduction, Relation,
};
use ark_ec::group::Group;
use ark_ff::prelude::*;
use derivative::Derivative;
use std::marker::PhantomData;

pub fn powers<F: Field>(f: F, biggest: usize) -> Vec<F> {
    crate::util::powers(f, 1..biggest + 1)
}
pub fn neg_powers<F: Field>(f: F, biggest: usize) -> Vec<F> {
    crate::util::neg_powers(f, 1..biggest + 1)
}

#[derive(Derivative)]
#[derivative(Default(bound = ""))]
pub struct ComR1csToIpa<G>(pub PhantomData<G>);

impl<G: Group> Reduction for ComR1csToIpa<G> {
    type From = ComR1csRelation<G>;
    type To = IpaRelation<G>;
    type Proof = G;
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
        // Setup
        let n = x.n;
        let m = x.m;
        let p1 = x.ts.iter().flatten().cloned().vcollect();
        assert_eq!(x.r * x.c, p1.len());
        assert_eq!(x.r * x.c, p1.len());
        let p0 = G::rand(fs);
        let p2 = rand_vec::<G, _>(m - p1.len() - 1, fs);
        let p3 = rand_vec::<G, _>(n, fs);
        let q012 = rand_vec::<G, _>(m, fs);
        let q3 = rand_vec::<G, _>(n, fs);
        let r = G::rand(fs);

        // Prover
        let z = w.full_assignment();
        assert_eq!(z.len(), m);
        let az = mat_vec_mult(&x.r1cs.a, &z);
        let bz = mat_vec_mult(&x.r1cs.b, &z);
        assert_eq!(p2.len(), w.a.len());
        let s_prime = msm(&p2, &w.a) + msm(&p3, &az) + msm(&q3, &bz);

        // Interaction
        fs.absorb(&s_prime);
        let alpha = G::ScalarField::rand(fs);
        let beta = G::ScalarField::rand(fs);
        let gamma = G::ScalarField::rand(fs);
        let eps = G::ScalarField::rand(fs);

        // Both
        let one = G::ScalarField::one();
        let mu = alpha * gamma;
        let alpha_n = powers(alpha, n);
        let beta_n = powers(beta, n);
        let gamma_n = powers(gamma, n);
        let mu_n = powers(mu, n);
        let eps_n = powers(eps, n);
        let gamma_minus_n = neg_powers(gamma, n);
        let w = ip(&alpha_n, &beta_n);
        let c = sum_vecs(
            vec![
                vec_mat_mult(&mu_n, &x.r1cs.a, m),
                vec_mat_mult(&beta_n, &x.r1cs.b, m),
                scale_vec(&-one, &vec_mat_mult(&gamma_n, &x.r1cs.c, m)),
            ],
            m,
        );
        assert_eq!(c.len(), m);
        let p1_prime = eps_n
            .iter()
            .zip(&x.ts)
            .flat_map(|(e, s)| scale_vec(e, s))
            .vcollect();
        let p2_prime = p2;
        let p3_prime = hadamard_gp(&p3, &gamma_minus_n);
        let p_prime = vec![&vec![p0], &p1_prime, &p2_prime, &p3_prime]
            .into_iter()
            .flatten()
            .cloned()
            .vcollect();
        let q = vec![&q012, &q3].into_iter().flatten().cloned().vcollect();
        let s_pprime: G = eps_n.iter().zip(&x.ss).map(|(e, s)| s.mul(e)).sum::<G>()
            + s_prime
            + p0
            + msm(&q012, &c)
            - msm(&q3, &alpha_n)
            - msm(&p3_prime, &beta_n)
            + r.mul(&w);

        // prover computes new witness
        let u = z
            .into_iter()
            .chain(sum_vecs(
                vec![hadamard(&gamma_n, &az), scale_vec(&-one, &beta_n)],
                n,
            ))
            .vcollect();
        let v = c
            .into_iter()
            .chain(sum_vecs(vec![bz, scale_vec(&-one, &alpha_n)], n))
            .vcollect();
        assert_eq!(ip(&u, &v), w);
        assert_eq!(u.len(), m + n);
        assert_eq!(v.len(), m + n);
        assert_eq!(p_prime.len(), m + n);
        let gens = IpaGens {
            vec_size: n + m,
            a_gens: p_prime,
            b_gens: q,
            ip_gen: r,
        };
        let witness = IpaWitness { a: u, b: v };
        (
            s_prime,
            IpaInstance {
                gens,
                result: s_pprime,
            },
            witness,
        )
    }
    fn verify(
        &self,
        _x: &<Self::From as Relation>::Inst,
        _pf: &Self::Proof,
        _fs: &mut FiatShamirRng,
    ) -> <Self::To as Relation>::Inst {
        todo!()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        curves::{models::JubJubPair, TEPair},
        reductions::{
            bp_unroll_to_com_r1cs::UnrollToComR1cs, com_r1cs_to_ipa::ComR1csToIpa,
            ipa_to_bp_unroll::IpaToBpUnroll,
        },
        relations::ipa::IpaInstance,
    };
    use ark_ec::{twisted_edwards_extended::GroupProjective, ModelParameters};
    use rand::Rng;
    fn test_from_bp_unroll<P: TEPair>(init_size: usize, k: usize, r: usize)
    where
        <P::P1 as ModelParameters>::BaseField: PrimeField,
    {
        println!(
            "doing a unrolled circuit check with {} elems, k: {}, r: {}",
            init_size, k, r
        );
        let rng = &mut ark_std::test_rng();
        let fs_seed: [u8; 32] = rng.gen();
        let mut fs_rng = crate::FiatShamirRng::from_seed(&fs_seed);
        let mut v_fs_rng = crate::FiatShamirRng::from_seed(&fs_seed);
        let (instance, witness) =
            IpaInstance::<GroupProjective<P::P1>>::sample_from_length(rng, init_size);
        let reducer = IpaToBpUnroll::<P>::new(k, r);
        let (proof, u_instance, u_witness) = reducer.prove(&instance, &witness, &mut fs_rng);
        //UnrollRelation::check(&u_instance, &u_witness);
        let verif_u_instance = reducer.verify(&instance, &proof, &mut v_fs_rng);
        assert_eq!(verif_u_instance, u_instance);
        let reducer2 = UnrollToComR1cs::<P>::default();
        let ((), r_instance, r_witness) = reducer2.prove(&u_instance, &u_witness, &mut fs_rng);
        let reducer3 = ComR1csToIpa::<P::G2>::default();
        let (_proof3, ipa_instance, ipa_witness) =
            reducer3.prove(&r_instance, &r_witness, &mut fs_rng);
        IpaRelation::check(&ipa_instance, &ipa_witness);
    }

    #[test]
    fn jubjub_unroll_test() {
        test_from_bp_unroll::<JubJubPair>(4, 2, 1);
        //test_from_bp_unroll::<JubJubPair>(8, 2, 2);
        //test_from_bp_unroll::<JubJubPair>(8, 2, 3);
        //test_from_bp_unroll::<JubJubPair>(9, 3, 1);
        //test_from_bp_unroll::<JubJubPair>(9, 3, 2);
        //test_from_bp_unroll::<JubJubPair>(2048, 4, 4);
        //test_from_bp_unroll::<JubJubPair>(2048, 4, 5);
    }
}
