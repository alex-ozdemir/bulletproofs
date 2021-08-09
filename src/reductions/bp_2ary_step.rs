use crate::{
    relations::ipa::{IpaGens, IpaInstance, IpaRelation, IpaWitness},
    util::{ip, msm, zero_pad_to_multiple},
    FiatShamirRng, Reduction, Relation,
};
use ark_ec::group::Group;
use ark_ff::{Field, UniformRand};
use derivative::Derivative;
use std::marker::PhantomData;

#[derive(Derivative)]
#[derivative(Default(bound = ""))]
pub struct Bp2aryStep<G: Group>(pub PhantomData<G>);

impl<G: Group> Reduction for Bp2aryStep<G> {
    type From = IpaRelation<G>;
    type To = IpaRelation<G>;
    type Proof = (G, G);
    fn prove(
        &self,
        instance: &<Self::From as Relation>::Inst,
        witness: &<Self::From as Relation>::Wit,
        fs: &mut FiatShamirRng,
    ) -> (
        Self::Proof,
        <Self::To as Relation>::Inst,
        <Self::To as Relation>::Wit,
    ) {
        let a = zero_pad_to_multiple(&witness.a, 2);
        let b = zero_pad_to_multiple(&witness.b, 2);
        let a_gen = zero_pad_to_multiple(&instance.gens.a_gens, 2);
        let b_gen = zero_pad_to_multiple(&instance.gens.b_gens, 2);
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
            },
            result: p_next,
        };
        ((l, r), instance_next, wit_next)
    }
    fn verify(
        &self,
        instance: &<Self::From as Relation>::Inst,
        (ref l, ref r): &Self::Proof,
        fs: &mut FiatShamirRng,
    ) -> <Self::To as Relation>::Inst {
        let a_gen = zero_pad_to_multiple(&instance.gens.a_gens, 2);
        let b_gen = zero_pad_to_multiple(&instance.gens.b_gens, 2);
        let p = instance.result;
        let q = instance.gens.ip_gen;
        assert!(a_gen.len() % 2 == 0);
        let n = a_gen.len() / 2;
        fs.absorb(&l);
        fs.absorb(&r);
        let x: G::ScalarField = G::ScalarField::rand(fs);
        let x_inv = x.inverse().unwrap();
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
        let instance_next = IpaInstance {
            gens: IpaGens {
                vec_size: n,
                ip_gen: q,
                a_gens: a_gen_next,
                b_gens: b_gen_next,
            },
            result: p_next,
        };
        instance_next
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
}
