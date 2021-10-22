use crate::{
    relations::ipa::{IpaGens, IpaInstance, IpaRelation, IpaWitness},
    util::{ip, msm, powers, scale_vec, sum_vecs, zero_pad_to_multiple},
    FiatShamirRng, Proof,
};
use ark_ec::group::Group;
use ark_ff::{Field, One, UniformRand};
use std::iter::once;
use std::marker::PhantomData;

pub struct KaryBp<G, B> {
    k: usize,
    base: B,
    _phants: PhantomData<G>,
}

impl<G, B> KaryBp<G, B> {
    pub fn new(k: usize, base: B) -> Self {
        Self {
            k,
            base,
            _phants: Default::default(),
        }
    }
}

pub fn prove_step<G: Group>(
    k: usize,
    instance: &IpaInstance<G>,
    witness: &IpaWitness<G::ScalarField>,
    fs: &mut FiatShamirRng,
) -> (IpaInstance<G>, IpaWitness<G::ScalarField>, Vec<G>, Vec<G>) {
    let a = zero_pad_to_multiple(&witness.a, k);
    let b = zero_pad_to_multiple(&witness.b, k);
    let a_gen = zero_pad_to_multiple(&instance.gens.a_gens, k);
    let b_gen = zero_pad_to_multiple(&instance.gens.b_gens, k);
    let p = instance.result;
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
        msm(
            a_gen[j].iter().chain(b_gen[i].iter()).chain(once(&q)),
            a[i].iter()
                .chain(b[j].iter())
                .chain(once(&ip(&a[i], &b[j]))),
        )
    };
    // Then the positive cross-term T[i] for i in {0,..,k-2{ is
    // \sum j={1,..k-i} X[i+j,j]
    // should be multiplied by x^(i+1)
    let pos_cross: Vec<G> = (0..k - 1)
        .map(|i| {
            let xs: Vec<_> = (0..k - i - 1).map(|j| x(i + j + 1, j)).collect();
            debug_assert_eq!(xs.len(), k - 1 - i);
            xs.into_iter().sum()
        })
        .collect();
    // Then the negative cross-term T[-i] for i in {0,..,k-2} is
    // \sum j={1,..k-i} X[i+j,j]
    // should be multiplied by x^-(i+1)
    let neg_cross: Vec<G> = (0..k - 1)
        .map(|i| (0..k - i - 1).map(|j| x(j, i + j + 1)).sum())
        .collect();

    fs.absorb(&pos_cross);
    fs.absorb(&neg_cross);
    let one = G::ScalarField::one();
    let x = G::ScalarField::rand(fs);

    // Fold everything in response to challenges...
    let x_inv = x.inverse().unwrap();
    let x_pows = powers(x, 0..k);
    let x_inv_pows = powers(x_inv, 0..k);
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
    let p_next = msm(
        pos_cross.iter().chain(&neg_cross),
        x_pows[1..].iter().chain(&x_inv_pows[1..]),
    ) + p;

    debug_assert_eq!(
        p_next,
        msm(
            a_gen_next.iter().chain(&b_gen_next).chain(once(&q)),
            a_next
                .iter()
                .chain(&b_next)
                .chain(once(&ip(&a_next, &b_next)))
        )
    );
    let wit_next = IpaWitness {
        a: a_next,
        b: b_next,
    };
    let instance_next = IpaInstance {
        gens: IpaGens {
            vec_size: ck_size,
            ip_gen: q,
            a_gens: a_gen_next,
            b_gens: b_gen_next,
        },
        result: p_next,
    };
    (instance_next, wit_next, pos_cross, neg_cross)
}

pub fn verify_step<G: Group>(
    k: usize,
    instance: &IpaInstance<G>,
    pos_cross: &[G],
    neg_cross: &[G],
    fs: &mut FiatShamirRng,
) -> IpaInstance<G> {
    let a_gen = zero_pad_to_multiple(&instance.gens.a_gens, k);
    let b_gen = zero_pad_to_multiple(&instance.gens.b_gens, k);
    let ck_size = a_gen.len() / k;
    let a_gen: Vec<_> = a_gen.chunks_exact(ck_size).collect();
    let b_gen: Vec<_> = b_gen.chunks_exact(ck_size).collect();
    let p = instance.result;
    fs.absorb(&pos_cross);
    fs.absorb(&neg_cross);
    let one = G::ScalarField::one();
    let x = G::ScalarField::rand(fs);

    // Fold everything in response to challenges...
    let x_inv = x.inverse().unwrap();
    let x_pows: Vec<_> = std::iter::successors(Some(one), |x_i| Some(x * x_i))
        .take(k)
        .collect();
    let x_inv_pows: Vec<_> = std::iter::successors(Some(one), |x_i| Some(x_inv * x_i))
        .take(k)
        .collect();
    let a_gen_next = sum_vecs(
        a_gen.iter().zip(&x_inv_pows).map(|(c, y)| scale_vec(y, c)),
        ck_size,
    );
    let b_gen_next = sum_vecs(
        b_gen.iter().zip(&x_pows).map(|(c, y)| scale_vec(y, c)),
        ck_size,
    );
    let p_next = msm(
        pos_cross.iter().chain(neg_cross),
        x_pows[1..].iter().chain(&x_inv_pows[1..]),
    ) + p;
    IpaInstance {
        gens: IpaGens {
            vec_size: ck_size,
            ip_gen: instance.gens.ip_gen,
            a_gens: a_gen_next,
            b_gens: b_gen_next,
        },
        result: p_next,
    }
}

impl<G: Group, B: Proof<IpaRelation<G>>> Proof<IpaRelation<G>> for KaryBp<G, B> {
    type Proof = BpProof<G, B>;

    fn prove(
        &self,
        instance: &IpaInstance<G>,
        witness: &IpaWitness<G::ScalarField>,
        fs: &mut FiatShamirRng,
    ) -> Self::Proof {
        if instance.gens.vec_size == 1 {
            BpProof::Base(self.base.prove(instance, witness, fs))
        } else {
            let (instance_next, wit_next, pos_cross, neg_cross) =
                prove_step(self.k, instance, witness, fs);
            let rec = self.prove(&instance_next, &wit_next, fs);
            BpProof::Rec {
                pos_cross,
                neg_cross,
                rec: Box::new(rec),
            }
        }
    }

    fn verify(&self, instance: &IpaInstance<G>, proof: &Self::Proof, fs: &mut FiatShamirRng) {
        match proof {
            BpProof::Base(base_proof) => self.base.verify(instance, base_proof, fs),
            BpProof::Rec {
                pos_cross,
                neg_cross,
                rec,
            } => {
                let instance_next = verify_step(self.k, instance, pos_cross, neg_cross, fs);
                self.verify(&instance_next, rec, fs)
            }
        }
    }
}

pub enum BpProof<G: Group, B: Proof<IpaRelation<G>>> {
    Rec {
        pos_cross: Vec<G>,
        neg_cross: Vec<G>,
        rec: Box<BpProof<G, B>>,
    },
    Base(B::Proof),
}
