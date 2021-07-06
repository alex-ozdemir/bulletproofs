use ark_ec::group::Group;
use ark_ff::Field;
use rand::Rng;

pub type FiatShamirRng = ark_marlin::rng::FiatShamirRng<blake2::Blake2s>;

pub mod iter_bp;
pub mod send;
pub mod util;

use util::msm;

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

trait Ipa<G: Group> {
    type Proof;
    fn prove(
        instance: &IpaInstance<G>,
        witness: &IpaWitness<G::ScalarField>,
        fs: &mut FiatShamirRng,
    ) -> Self::Proof;
    fn check(instance: &IpaInstance<G>, proof: &Self::Proof, fs: &mut FiatShamirRng) -> bool;
    fn check_witness(instance: &IpaInstance<G>, witness: &IpaWitness<G::ScalarField>) -> bool {
        let ip = witness.ip();
        assert_eq!(instance.gens.vec_size, instance.gens.a_gens.len());
        assert_eq!(instance.gens.vec_size, instance.gens.b_gens.len());
        assert_eq!(instance.gens.vec_size, witness.a.len());
        assert_eq!(instance.gens.vec_size, witness.b.len());
        msm(&instance.gens.a_gens, &witness.a)
            + msm(&instance.gens.b_gens, &witness.b)
            + instance.gens.ip_gen.mul(&ip)
            == instance.result
    }
}

#[cfg(test)]
mod test {
    use super::{iter_bp, send, FiatShamirRng, Ipa, IpaInstance};
    use ark_bls12_381::Bls12_381;
    use ark_ec::{group::Group, PairingEngine};
    use rand::Rng;
    fn test_ipa<G: Group, I: Ipa<G>>(sizes: Vec<usize>, reps: usize) {
        let rng = &mut ark_std::test_rng();
        for size in sizes {
            for _ in 0..reps {
                let (mut instance, witness) = IpaInstance::<G>::sample_from_length(rng, size);
                assert!(I::check_witness(&instance, &witness));
                let fs_seed: [u8; 32] = rng.gen();
                let mut fs_rng = FiatShamirRng::from_seed(&fs_seed);
                let proof = I::prove(&instance, &witness, &mut fs_rng);
                let mut fs_rng = FiatShamirRng::from_seed(&fs_seed);
                assert!(I::check(&instance, &proof, &mut fs_rng));
                instance.tweak();
                let mut fs_rng = FiatShamirRng::from_seed(&fs_seed);
                assert!(!I::check(&instance, &proof, &mut fs_rng));
            }
        }
    }

    #[test]
    fn test_send_ipa() {
        type G = <Bls12_381 as PairingEngine>::G1Projective;
        test_ipa::<G, send::SendIpa<G>>(vec![1, 2, 3, 4, 8, 9, 15], 1);
    }

    #[test]
    fn test_bp_ipa() {
        type G = <Bls12_381 as PairingEngine>::G1Projective;
        test_ipa::<G, iter_bp::Bp<G>>(vec![1, 2, 4, 8, 16], 3);
    }
}
