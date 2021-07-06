use ark_ec::group::Group;
use ark_ff::{UniformRand, Field, One};
use std::marker::PhantomData;
use crate::{IpaWitness, IpaInstance, Ipa, FiatShamirRng, util::{msm, ip}};

pub struct Bp<G>(PhantomData<G>);

impl<G> std::default::Default for Bp<G> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<G: Group> Bp<G> {
    fn scalars_from_challenges(challs: &[G::ScalarField]) -> Vec<G::ScalarField> {
        if challs.len() == 0 {
            vec![G::ScalarField::one()]
        } else {
            let mut left = Self::scalars_from_challenges(&challs[1..]);
            let n = left.len();
            let chall = challs[0];
            let chall_inv = chall.inverse().unwrap();
            for i in 0..n {
                left.push(left[i] * chall);
                left[i] *= chall_inv;
            }
            left
        }
    }
}

impl<G: Group> Ipa<G> for Bp<G> {
    type Proof = BpProof<G>;

    fn prove(
        instance: &IpaInstance<G>,
        witness: &IpaWitness<G::ScalarField>,
        fs: &mut FiatShamirRng,
    ) -> Self::Proof {
        let mut ls = Vec::new();
        let mut rs = Vec::new();
        let mut a = witness.a.clone();
        let mut b = witness.b.clone();
        let mut a_gen = instance.gens.a_gens.clone();
        let mut b_gen = instance.gens.b_gens.clone();
        let mut p = instance.result;
        let q = instance.gens.ip_gen;
        while a.len() > 1 {
            assert!(a.len() % 2 == 0);
            let n = a.len() / 2;
            let l = msm(&a_gen[n..], &a[..n])
                + msm(&b_gen[..n], &b[n..])
                + q.mul(&ip(&a[..n], &b[n..]));
            let r = msm(&a_gen[..n], &a[n..])
                + msm(&b_gen[n..], &b[..n])
                + q.mul(&ip(&a[n..], &b[..n]));
            ls.push(l);
            rs.push(r);
            fs.absorb(&l);
            fs.absorb(&r);
            let x: G::ScalarField = G::ScalarField::rand(fs);
            let x_inv = x.inverse().unwrap();
            let a_next: Vec<G::ScalarField> = a[..n]
                .iter()
                .zip(&a[n..])
                .map(|(l, r)| x * *l + x_inv * *r)
                .collect();
            let b_next: Vec<G::ScalarField> = b[..n]
                .iter()
                .zip(&b[n..])
                .map(|(l, r)| x_inv * *l + x * *r)
                .collect();
            let p_next = l.mul(&x.square()) + r.mul(&x_inv.square()) + p;
            let a_gen_next: Vec<G> = a_gen[..n]
                .iter()
                .zip(&a_gen[n..])
                .map(|(l, r)| l.mul(&x_inv) + r.mul(&x))
                .collect();
            let b_gen_next: Vec<G> = b_gen[..n]
                .iter()
                .zip(&b_gen[n..])
                .map(|(l, r)| l.mul(&x) + r.mul(&x_inv))
                .collect();
            debug_assert_eq!(
                p_next,
                msm(&a_gen_next, &a_next)
                    + msm(&b_gen_next, &b_next)
                    + q.mul(&ip(&a_next, &b_next))
            );
            a = a_next;
            b = b_next;
            a_gen = a_gen_next;
            b_gen = b_gen_next;
            p = p_next;
        }
        assert_eq!(a.len(), 1);
        assert_eq!(b.len(), 1);
        let final_a = a.pop().unwrap();
        let final_b = b.pop().unwrap();
        BpProof {
            ls,
            rs,
            final_a,
            final_b,
        }
    }

    fn check(instance: &IpaInstance<G>, proof: &Self::Proof, fs: &mut FiatShamirRng) -> bool {
        assert!(instance.gens.vec_size.is_power_of_two());
        let mut challenges: Vec<G::ScalarField> = Vec::new();
        for i in 0..proof.ls.len() {
            fs.absorb(&proof.ls[i]);
            fs.absorb(&proof.rs[i]);
            let x = G::ScalarField::rand(fs);
            challenges.push(x);
        }
        dbg!(&challenges);
        let scalars = Self::scalars_from_challenges(&challenges);
        let scalars_inv: Vec<G::ScalarField> =
            scalars.iter().map(|s| s.inverse().unwrap()).collect();
        //let a_gen = msm(&instance.gens.a_gens, &scalars);
        //let b_gen = msm(&instance.gens.b_gens, &scalars_inv);

        let mut final_msm_scalars = Vec::new();
        let mut final_msm_points = Vec::new();
        final_msm_points.extend(instance.gens.a_gens.iter().cloned());
        final_msm_scalars.extend(scalars.into_iter().map(|s| s * &proof.final_a));
        final_msm_points.extend(instance.gens.b_gens.iter().cloned());
        final_msm_scalars.extend(scalars_inv.into_iter().map(|s| s * &proof.final_b));
        final_msm_points.push(instance.gens.ip_gen.clone());
        final_msm_scalars.push(proof.final_a * &proof.final_b);
        for j in 0..proof.ls.len() {
            final_msm_points.push(proof.ls[j]);
            final_msm_scalars.push(-challenges[j].square());
            final_msm_points.push(proof.rs[j]);
            final_msm_scalars.push(-challenges[j].inverse().unwrap().square());
        }
        instance.result == msm(&final_msm_points, &final_msm_scalars)
    }
}

pub struct BpProof<G: Group> {
    ls: Vec<G>,
    rs: Vec<G>,
    final_a: G::ScalarField,
    final_b: G::ScalarField,
}

