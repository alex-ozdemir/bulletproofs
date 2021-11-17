use crate::{
    util::{msm, zero_pad_to_two_power},
    Relation,
};
use ark_ec::group::Group;
use ark_ff::Field;
use rand::Rng;
use std::marker::PhantomData;

#[derive(Clone, PartialEq, Eq, Debug)]
/// Generators for an inner product relation
pub struct IpaGens<G: Group> {
    /// The size of the vectors
    pub vec_size: usize,
    /// The A vector of generators
    pub a_gens: Vec<G>,
    /// The B vector of generators
    pub b_gens: Vec<G>,
    pub ip_gen: G,
    /// Challenges for folding the vectors
    /// let fold(x, A) = A_L x + A_r x^{-1}
    /// If the challenges are [c1, c2, ... cn],
    /// then A' = fold(cn, ... fold(c2, fold(c1, A)))
    pub challenges: Vec<G::ScalarField>,
}

impl<G: Group> IpaGens<G> {
    fn sample_from_length<R: Rng + ?Sized>(rng: &mut R, length: usize) -> Self {
        IpaGens {
            a_gens: (0..length).map(|_| G::rand(rng)).collect(),
            b_gens: (0..length).map(|_| G::rand(rng)).collect(),
            ip_gen: G::rand(rng),
            vec_size: length,
            challenges: Vec::new(),
        }
    }
    pub fn commit_for_witness(&self, witness: &IpaWitness<G::ScalarField>) -> G {
        let ip = witness.ip();
        assert_eq!(self.challenges.len(), 0);
        msm(&self.a_gens, &witness.a) + msm(&self.b_gens, &witness.b) + self.ip_gen.mul(&ip)
    }
    pub fn fold_to_length_1_naive(&self) -> Self {
        assert!(1 << self.challenges.len() >= self.a_gens.len());
        assert!(1 << self.challenges.len() >= self.b_gens.len());
        let mut a_gen = self.a_gens.clone();
        let mut b_gen = self.b_gens.clone();
        let mut c_i = 0;
        a_gen = zero_pad_to_two_power(&a_gen);
        b_gen = zero_pad_to_two_power(&b_gen);
        while a_gen.len() > 1 {
            let n = a_gen.len() / 2;
            let x = self.challenges[c_i].clone();
            let x_inv = x.inverse().unwrap();
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
            c_i += 1;
            a_gen = a_gen_next;
            b_gen = b_gen_next;
        }
        assert_eq!(c_i + 1, self.challenges.len());
        Self {
            vec_size: 1,
            a_gens: a_gen,
            b_gens: b_gen,
            ip_gen: self.ip_gen.clone(),
            challenges: Vec::new(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct IpaInstance<G: Group> {
    pub gens: IpaGens<G>,
    pub result: G,
}

impl<G: Group> IpaInstance<G> {
    fn from_gens_and_witness(gens: IpaGens<G>, witness: &IpaWitness<G::ScalarField>) -> Self {
        let result = gens.commit_for_witness(witness);
        Self { gens, result }
    }
    pub fn sample_from_length<R: Rng + ?Sized>(
        rng: &mut R,
        length: usize,
    ) -> (Self, IpaWitness<G::ScalarField>) {
        let gens = IpaGens::sample_from_length(rng, length);
        let witness = IpaWitness::sample_from_length(rng, length);
        (Self::from_gens_and_witness(gens, &witness), witness)
    }
    pub fn tweak(&mut self) {
        self.result.double_in_place();
    }
}

#[derive(Clone, Debug)]
pub struct IpaWitness<F: Field> {
    pub a: Vec<F>,
    pub b: Vec<F>,
}

impl<F: Field> IpaWitness<F> {
    fn sample_from_length<R: Rng + ?Sized>(rng: &mut R, length: usize) -> Self {
        IpaWitness {
            a: (0..length).map(|_| F::rand(rng)).collect(),
            b: (0..length).map(|_| F::rand(rng)).collect(),
        }
    }
}

impl<F: Field> IpaWitness<F> {
    pub fn ip(&self) -> F {
        self.a
            .iter()
            .zip(&self.b)
            .fold(F::zero(), |acc, (a, b)| acc + a.clone() * b)
    }
}

pub struct IpaRelation<G: Group>(pub PhantomData<G>);

impl<G: Group> Relation for IpaRelation<G> {
    /// Vector size
    type Cfg = usize;
    type Inst = IpaInstance<G>;
    type Wit = IpaWitness<G::ScalarField>;
    fn check(instance: &Self::Inst, witness: &Self::Wit) {
        let ip = witness.ip();
        assert_eq!(instance.gens.vec_size, instance.gens.a_gens.len());
        assert_eq!(instance.gens.vec_size, instance.gens.b_gens.len());
        assert_eq!(instance.gens.vec_size, witness.a.len());
        assert_eq!(instance.gens.vec_size, witness.b.len());
        assert_eq!(
            msm(&instance.gens.a_gens, &witness.a)
                + msm(&instance.gens.b_gens, &witness.b)
                + instance.gens.ip_gen.mul(&ip),
            instance.result
        );
    }

    fn check_cfg(size: &Self::Cfg, x: &Self::Inst) {
        assert!(
            x.gens.vec_size <= *size,
            "size: {}\nsupported: {}",
            x.gens.vec_size,
            size
        );
    }

    fn size(x: &Self::Inst) -> Self::Cfg {
        x.gens.vec_size
    }
}
