use crate::{
    relations::{
        com_r1cs::{mat_vec_mult, vec_mat_mult, ComR1csRelation},
        ipa::{IpaGens, IpaInstance, IpaRelation, IpaWitness},
    },
    timed,
    util::{hadamard, hadamard_gp, ip, msm, rand_vec, scale_vec, sum_vecs, CollectIter},
    FiatShamirRng, Reduction, Relation,
};
use ark_ec::group::Group;
use ark_ff::prelude::*;
use ark_std::{end_timer, start_timer};
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
    // TODO: fix.
    type Params = Vec<G>;
    type Proof = G;
    fn prove(
        &self,
        pp: &Self::Params,
        x: &<Self::From as Relation>::Inst,
        w: &<Self::From as Relation>::Wit,
        fs: &mut FiatShamirRng,
    ) -> (
        Self::Proof,
        <Self::To as Relation>::Inst,
        <Self::To as Relation>::Wit,
    ) {
        let timer = start_timer!(|| "proving com-r1cs-to-ipa");
        // Setup
        let n = x.n;
        let m = x.m;
        let p1 = x.ts.iter().flatten().cloned().vcollect();
        assert_eq!(x.r * x.c, p1.len());
        assert_eq!(x.r * x.c, p1.len());
        let mut pp = pp.clone();
        let p0 = pp.pop().unwrap();
        let p2 = pp.drain(..m-p1.len()-1).vcollect();
        let p3 = pp.drain(..n).vcollect();
        let q012 = pp.drain(..m).vcollect();
        let q3 = pp.drain(..n).vcollect();
        let r = pp.pop().unwrap();

        // Prover
        let mat_timer = start_timer!(|| "matrix products");
        let z = w.full_assignment();
        assert_eq!(z.len(), m);
        let az = mat_vec_mult(&x.r1cs.a, &z);
        let bz = mat_vec_mult(&x.r1cs.b, &z);
        assert_eq!(p2.len(), w.a.len());
        end_timer!(mat_timer);
        let s_prime = timed!(
            || "S msm",
            msm(
                p2.iter().chain(&p3).chain(&q3),
                w.a.iter().chain(&az).chain(&bz),
            )
        );

        // Interaction
        fs.absorb(&s_prime);
        let alpha = G::ScalarField::rand(fs);
        let beta = G::ScalarField::rand(fs);
        let gamma = G::ScalarField::rand(fs);
        let eps = G::ScalarField::rand(fs);

        // Both
        let fold_timer = start_timer!(|| "folding");
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
        end_timer!(fold_timer);
        let p_timer = start_timer!(|| "p");
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
        end_timer!(p_timer);
        let s_timer = start_timer!(|| "s");
        let q = vec![&q012, &q3].into_iter().flatten().cloned().vcollect();
        let neg_q012 = q012.into_iter().map(|s| -s).vcollect();
        let s_pprime: G = eps_n.iter().zip(&x.ss).map(|(e, s)| s.mul(e)).sum::<G>() + s_prime + p0
            - timed!(
                || "msm",
                msm(
                    neg_q012.iter().chain(&q3).chain(&p3_prime),
                    c.iter().chain(&alpha_n).chain(&beta_n),
                )
            )
            + r.mul(&w);
        end_timer!(s_timer);

        // prover computes new witness
        let new_wit_timer = start_timer!(|| "new wit");
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
        end_timer!(new_wit_timer);
        assert_eq!(ip(&u, &v), w);
        assert_eq!(u.len(), m + n);
        assert_eq!(v.len(), m + n);
        assert_eq!(p_prime.len(), m + n);
        let gens = IpaGens {
            vec_size: n + m,
            a_gens: p_prime,
            b_gens: q,
            ip_gen: r,
            challenges: Vec::new(),
        };
        let witness = IpaWitness { a: u, b: v };
        end_timer!(timer);
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
        pp: &Self::Params,
        x: &<Self::From as Relation>::Inst,
        s_prime: &Self::Proof,
        fs: &mut FiatShamirRng,
    ) -> <Self::To as Relation>::Inst {
        let timer = start_timer!(|| "verifying com-r1cs-to-ipa");
        // Setup
        let setup_timer = start_timer!(|| "setup");
        let n = x.n;
        let m = x.m;
        let p1 = x.ts.iter().flatten().cloned().vcollect();
        assert_eq!(x.r * x.c, p1.len());
        assert_eq!(x.r * x.c, p1.len());
        let mut pp = pp.clone();
        let p0 = pp.pop().unwrap();
        let p2 = pp.drain(..m-p1.len()-1).vcollect();
        let p3 = pp.drain(..n).vcollect();
        let q012 = pp.drain(..m).vcollect();
        let q3 = pp.drain(..n).vcollect();
        let r = pp.pop().unwrap();
        end_timer!(setup_timer);

        // Interaction
        fs.absorb(&s_prime);
        let alpha = G::ScalarField::rand(fs);
        let beta = G::ScalarField::rand(fs);
        let gamma = G::ScalarField::rand(fs);
        let eps = G::ScalarField::rand(fs);

        // Both
        let one = G::ScalarField::one();
        let mu = alpha * gamma;
        let chall_pow_timer = start_timer!(|| "challenge powers");
        let alpha_n = powers(alpha, n);
        let beta_n = powers(beta, n);
        let gamma_n = powers(gamma, n);
        let mu_n = powers(mu, n);
        let eps_n = powers(eps, n);
        let gamma_minus_n = neg_powers(gamma, n);
        let w = ip(&alpha_n, &beta_n);
        end_timer!(chall_pow_timer);
        let c = timed!(
            || "sum",
            sum_vecs(
                vec![
                    vec_mat_mult(&mu_n, &x.r1cs.a, m),
                    vec_mat_mult(&beta_n, &x.r1cs.b, m),
                    scale_vec(&-one, &vec_mat_mult(&gamma_n, &x.r1cs.c, m)),
                ],
                m,
            )
        );
        assert_eq!(c.len(), m);
        let s_timer = start_timer!(|| "s");
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
        let neg_q012 = q012.into_iter().map(|s| -s).vcollect();
        let s_pprime: G = eps_n.iter().zip(&x.ss).map(|(e, s)| s.mul(e)).sum::<G>() + s_prime + p0
            - msm(
                neg_q012.iter().chain(&q3).chain(&p3_prime),
                c.iter().chain(&alpha_n).chain(&beta_n),
            )
            + r.mul(&w);
        end_timer!(s_timer);

        // prover computes en(), m + n);
        let gens = IpaGens {
            vec_size: n + m,
            a_gens: p_prime,
            b_gens: q,
            ip_gen: r,
            challenges: Vec::new(),
        };
        end_timer!(timer);
        IpaInstance {
            gens,
            result: s_pprime,
        }
    }
    fn proof_size(_p: &Self::Proof) -> usize {
        1
    }
    fn setup<R: rand::Rng>(&self, c: &<Self::From as Relation>::Cfg, rng: &mut R) -> Self::Params {
        timed!(|| "setup", {
            let m = c.0;
            let n = c.1;
            rand_vec::<G, _>(2 * (m + n), rng)
        })
    }
    fn map_params(&self, c: &<Self::From as Relation>::Cfg) -> <Self::To as Relation>::Cfg {
        c.0 + c.1
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        curves::{
            models::{JubJubPair, PastaPair, VellasPair},
            Pair,
        },
        reductions::{
            bp_unroll_to_com_r1cs::UnrollToComR1cs, com_r1cs_to_ipa::ComR1csToIpa,
            ipa_to_bp_unroll::IpaToBpUnroll,
        },
        relations::bp_unroll::UnrollRelation,
        relations::ipa::IpaInstance,
    };
    use rand::Rng;
    fn test_from_bp_unroll<C: Pair>(init_size: usize, k: usize, r: usize) {
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
        let (proof, u_instance, u_witness) = reducer.prove(&(), &instance, &witness, &mut fs_rng);
        UnrollRelation::check(&u_instance, &u_witness);
        let verif_u_instance = reducer.verify(&(), &instance, &proof, &mut v_fs_rng);
        assert_eq!(verif_u_instance, u_instance);
        let reducer2 = UnrollToComR1cs::<C>::default();
        let ((), r_instance, r_witness) = reducer2.prove(&(), &u_instance, &u_witness, &mut fs_rng);
        let reducer3 = ComR1csToIpa::<C::G2>::default();
        let pp = reducer3.setup(&ComR1csRelation::<C::G2>::size(&r_instance), rng);
        let (proof3, ipa_instance, ipa_witness) =
            reducer3.prove(&pp, &r_instance, &r_witness, &mut fs_rng);
        IpaRelation::check(&ipa_instance, &ipa_witness);
        let v_r_instance = reducer2.verify(&(), &u_instance, &(), &mut v_fs_rng);
        let v_ipa_instance = reducer3.verify(&pp, &v_r_instance, &proof3, &mut v_fs_rng);
        IpaRelation::check(&v_ipa_instance, &ipa_witness);
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

    #[test]
    fn pasta_unroll_test() {
        test_from_bp_unroll::<PastaPair>(4, 2, 1);
    }

    #[test]
    fn vellas_unroll_test() {
        test_from_bp_unroll::<VellasPair>(4, 2, 1);
    }
}
