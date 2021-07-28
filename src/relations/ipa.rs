use crate::{util::msm, Relation};
use ark_ec::group::Group;
use ark_ff::Field;
use rand::Rng;
use std::marker::PhantomData;

#[derive(Clone)]
pub struct IpaGens<G: Group> {
    pub vec_size: usize,
    pub a_gens: Vec<G>,
    pub b_gens: Vec<G>,
    pub ip_gen: G,
}

impl<G: Group> IpaGens<G> {
    fn sample_from_length<R: Rng + ?Sized>(rng: &mut R, length: usize) -> Self {
        IpaGens {
            a_gens: (0..length).map(|_| G::rand(rng)).collect(),
            b_gens: (0..length).map(|_| G::rand(rng)).collect(),
            ip_gen: G::rand(rng),
            vec_size: length,
        }
    }
    fn commit_for_witness(&self, witness: &IpaWitness<G::ScalarField>) -> G {
        let ip = witness.ip();
        msm(&self.a_gens, &witness.a) + msm(&self.b_gens, &witness.b) + self.ip_gen.mul(&ip)
    }
}

#[derive(Clone)]
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

#[derive(Clone)]
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
    fn ip(&self) -> F {
        self.a
            .iter()
            .zip(&self.b)
            .fold(F::zero(), |acc, (a, b)| acc + a.clone() * b)
    }
}

pub struct IpaRelation<G: Group>(pub PhantomData<G>);

impl<G: Group> Relation for IpaRelation<G> {
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
}
