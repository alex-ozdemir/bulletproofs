use crate::{
    relations::ipa::{IpaGens, IpaInstance, IpaRelation, IpaWitness},
    util::{ip, msm},
    FiatShamirRng, Proof, Relation,
};
use ark_ec::group::Group;
use ark_ff::{Field, UniformRand};
use std::marker::PhantomData;

pub struct Bp<G, B>(PhantomData<G>, B);

impl<G, B> Bp<G, B> {
    pub fn new(b: B) -> Self {
        Self(Default::default(), b)
    }
}

impl<G: Group, B: Proof<IpaRelation<G>>> Proof<IpaRelation<G>> for Bp<G, B> {
    type Params = B::Params;
    type Proof = BpProof<G, B>;

    fn prove(
        &self,
        pp: &Self::Params,
        instance: &IpaInstance<G>,
        witness: &IpaWitness<G::ScalarField>,
        fs: &mut FiatShamirRng,
    ) -> Self::Proof {
        if instance.gens.vec_size == 1 {
            BpProof::Base(self.1.prove(pp, instance, witness, fs))
        } else {
            let a = witness.a.clone();
            let b = witness.b.clone();
            let a_gen = instance.gens.a_gens.clone();
            let b_gen = instance.gens.b_gens.clone();
            let p = instance.result;
            let q = instance.gens.ip_gen;
            assert!(a.len() % 2 == 0);
            let n = a.len() / 2;
            let l = msm(&a_gen[n..], &a[..n])
                + msm(&b_gen[..n], &b[n..])
                + q.mul(&ip(&a[..n], &b[n..]));
            let r = msm(&a_gen[..n], &a[n..])
                + msm(&b_gen[n..], &b[..n])
                + q.mul(&ip(&a[n..], &b[..n]));
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
            let wit_next = IpaWitness {
                a: a_next,
                b: b_next,
            };
            let instance_next = IpaInstance {
                gens: IpaGens {
                    challenges: Vec::new(),
                    vec_size: n,
                    ip_gen: q,
                    a_gens: a_gen_next,
                    b_gens: b_gen_next,
                },
                result: p_next,
            };
            let rec_proof = self.prove(pp, &instance_next, &wit_next, fs);
            BpProof::Rec(l, r, Box::new(rec_proof))
        }
    }

    fn verify(&self, pp: &Self::Params, instance: &IpaInstance<G>, proof: &Self::Proof, fs: &mut FiatShamirRng) {
        match proof {
            BpProof::Base(base_proof) => self.1.verify(pp, instance, base_proof, fs),
            BpProof::Rec(l, r, inner_proof) => {
                fs.absorb(l);
                fs.absorb(r);
                let x = G::ScalarField::rand(fs);
                let x_inv = x.inverse().unwrap();
                let a_gen = instance.gens.a_gens.clone();
                let b_gen = instance.gens.b_gens.clone();
                let n = a_gen.len() / 2;
                let p_next = l.mul(&x.square()) + r.mul(&x_inv.square()) + instance.result;
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
                        challenges: Vec::new(),
                        vec_size: n,
                        ip_gen: instance.gens.ip_gen,
                        a_gens: a_gen_next,
                        b_gens: b_gen_next,
                    },
                    result: p_next,
                };
                self.verify(pp, &instance_next, inner_proof, fs)
            }
        }
    }
    fn setup<Rn: rand::Rng>(&self, _: &<IpaRelation<G> as Relation>::Cfg, rng: &mut Rn) -> Self::Params {
        self.1.setup(&2, rng)
    }

    fn proof_size(p: &Self::Proof) -> usize {
        match p {
            BpProof::Rec(_, _, r) => 2 + Self::proof_size(r),
            BpProof::Base(b) => B::proof_size(b),
        }
    }
}

pub enum BpProof<G: Group, B: Proof<IpaRelation<G>>> {
    Rec(G, G, Box<BpProof<G, B>>),
    Base(B::Proof),
}
