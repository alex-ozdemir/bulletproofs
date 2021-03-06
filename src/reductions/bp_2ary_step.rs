use crate::{
    relations::ipa::{IpaGens, IpaInstance, IpaRelation, IpaWitness},
    util::{ip, msm, zero_pad_to_two_power},
    FiatShamirRng, Reduction, Relation,
};
use ark_ec::group::Group;
use ark_ff::{Field, UniformRand};
use derivative::Derivative;
use std::marker::PhantomData;

use ark_std::cfg_iter;
#[cfg(feature = "parallel")]
use rayon::prelude::*;

#[derive(Derivative)]
#[derivative(Default(bound = ""))]
pub struct Bp2aryStep<G: Group>(pub PhantomData<G>);

impl<G: Group> Reduction for Bp2aryStep<G> {
    type From = IpaRelation<G>;
    type To = IpaRelation<G>;
    type Params = ();
    type Proof = (G, G);
    fn prove(
        &self,
        _pp: &Self::Params,
        instance: &<Self::From as Relation>::Inst,
        witness: &<Self::From as Relation>::Wit,
        fs: &mut FiatShamirRng,
    ) -> (
        Self::Proof,
        <Self::To as Relation>::Inst,
        <Self::To as Relation>::Wit,
    ) {
        let a = zero_pad_to_two_power(&witness.a);
        let b = zero_pad_to_two_power(&witness.b);
        let a_gen = zero_pad_to_two_power(&instance.gens.a_gens);
        let b_gen = zero_pad_to_two_power(&instance.gens.b_gens);
        let p = instance.result;
        let q = instance.gens.ip_gen;
        assert!(a.len() % 2 == 0);
        let n = a.len() / 2;
        let l =
            msm(&a_gen[n..], &a[..n]) + msm(&b_gen[..n], &b[n..]) + q.mul(&ip(&a[..n], &b[n..]));
        let r =
            msm(&a_gen[..n], &a[n..]) + msm(&b_gen[n..], &b[..n]) + q.mul(&ip(&a[n..], &b[..n]));
        fs.absorb(&l);
        fs.absorb(&r);
        let x: G::ScalarField = G::ScalarField::rand(fs);
        let x_inv = x.inverse().unwrap();
        let a_next: Vec<G::ScalarField> = cfg_iter!(a[..n])
            .zip(&a[n..])
            .map(|(l, r)| x * *l + x_inv * *r)
            .collect();
        let b_next: Vec<G::ScalarField> = cfg_iter!(b[..n])
            .zip(&b[n..])
            .map(|(l, r)| x_inv * *l + x * *r)
            .collect();
        let p_next = l.mul(&x.square()) + r.mul(&x_inv.square()) + p;
        let a_gen_next: Vec<G> = cfg_iter!(a_gen[..n])
            .zip(&a_gen[n..])
            .map(|(l, r)| l.mul(&x_inv) + r.mul(&x))
            .collect();
        let b_gen_next: Vec<G> = cfg_iter!(b_gen[..n])
            .zip(&b_gen[n..])
            .map(|(l, r)| l.mul(&x) + r.mul(&x_inv))
            .collect();
        debug_assert_eq!(
            p_next,
            msm(&a_gen_next, &a_next) + msm(&b_gen_next, &b_next) + q.mul(&ip(&a_next, &b_next))
        );
        let wit_next = IpaWitness {
            a: a_next,
            b: b_next,
        };
        let instance_next = IpaInstance {
            gens: IpaGens {
                vec_size: n,
                ip_gen: q,
                a_gens: a_gen_next,
                b_gens: b_gen_next,
                challenges: Vec::new(),
            },
            result: p_next,
        };
        ((l, r), instance_next, wit_next)
    }
    fn verify(
        &self,
        _pp: &Self::Params,
        instance: &<Self::From as Relation>::Inst,
        (ref l, ref r): &Self::Proof,
        fs: &mut FiatShamirRng,
    ) -> <Self::To as Relation>::Inst {
        let a_gen = zero_pad_to_two_power(&instance.gens.a_gens);
        let b_gen = zero_pad_to_two_power(&instance.gens.b_gens);
        let p = instance.result;
        let q = instance.gens.ip_gen;
        assert!(a_gen.len() % 2 == 0);
        let n = a_gen.len() / 2;
        fs.absorb(&l);
        fs.absorb(&r);
        let x: G::ScalarField = G::ScalarField::rand(fs);
        let x_inv = x.inverse().unwrap();
        let p_next = l.mul(&x.square()) + r.mul(&x_inv.square()) + p;
        let a_gen_next: Vec<G> = cfg_iter!(a_gen[..n])
            .zip(&a_gen[n..])
            .map(|(l, r)| l.mul(&x_inv) + r.mul(&x))
            .collect();
        let b_gen_next: Vec<G> = cfg_iter!(b_gen[..n])
            .zip(&b_gen[n..])
            .map(|(l, r)| l.mul(&x) + r.mul(&x_inv))
            .collect();
        let instance_next = IpaInstance {
            gens: IpaGens {
                vec_size: n,
                ip_gen: q,
                a_gens: a_gen_next,
                b_gens: b_gen_next,
                challenges: Vec::new(),
            },
            result: p_next,
        };
        instance_next
    }
    fn proof_size(_p: &Self::Proof) -> usize {
        2
    }
    fn setup<R: rand::Rng>(
        &self,
        _: &<IpaRelation<G> as Relation>::Cfg,
        _: &mut R,
    ) -> Self::Params {
        ()
    }
    fn map_params(
        &self,
        c: &<IpaRelation<G> as Relation>::Cfg,
    ) -> <IpaRelation<G> as Relation>::Cfg {
        (*c - 1) / 2 + 1
    }
}

#[cfg(test)]
mod test {
    use super::Bp2aryStep;
    use crate::{
        relations::ipa::{IpaInstance, IpaRelation},
        test::test_reduction,
        Reduction, Relation,
    };
    use ark_ec::group::Group;
    fn test_ipa<G: Group, I: Reduction<From = IpaRelation<G>>>(
        sizes: Vec<usize>,
        reps: usize,
        i: I,
    ) {
        let rng = &mut ark_std::test_rng();
        for size in sizes {
            for _ in 0..reps {
                let (instance, witness) = IpaInstance::<G>::sample_from_length(rng, size);
                IpaRelation::check(&instance, &witness);
                test_reduction(&i, instance, witness);
            }
        }
    }
    #[test]
    fn test_bls() {
        type G = ark_bls12_381::G1Projective;
        let i = Bp2aryStep::<G>::default();
        test_ipa(vec![2, 4, 8, 16], 4, i);
    }
    #[test]
    fn test_pallas() {
        type G = ark_pallas::Projective;
        let i = Bp2aryStep::<G>::default();
        test_ipa(vec![2, 4, 8, 16], 4, i);
    }
    #[test]
    fn test_vesta() {
        type G = ark_vesta::Projective;
        let i = Bp2aryStep::<G>::default();
        test_ipa(vec![2, 4, 8, 16], 4, i);
    }
}
