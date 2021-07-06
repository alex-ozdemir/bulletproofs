use ark_ec::group::Group;
use ark_ff::{Field, One, UniformRand};
use rand::Rng;
use std::marker::PhantomData;

pub type FiatShamirRng = ark_marlin::rng::FiatShamirRng<blake2::Blake2s>;

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
    fn split(mut self) -> (Self, Self) {
        assert!(self.vec_size > 1);
        assert!(self.vec_size % 2 == 0);
        let h = self.vec_size / 2;
        let a_gens_high = self.a_gens.split_off(h);
        let b_gens_high = self.b_gens.split_off(h);
        self.vec_size = h;
        let mut other = Self {
            vec_size: h,
            ip_gen: self.ip_gen,
            a_gens: a_gens_high,
            b_gens: b_gens_high,
        };
        std::mem::swap(&mut self.b_gens, &mut other.b_gens);
        (self, other)
    }
    fn merge(mut self, other: &Self, chall: G::ScalarField) -> Self {
        assert_eq!(self.vec_size, other.vec_size);
        let chall_inv = chall.inverse().unwrap();
        for (l, h) in self.a_gens.iter_mut().zip(&other.a_gens) {
            *l *= chall_inv;
            *l += h.mul(&chall);
        }
        for (l, h) in self.b_gens.iter_mut().zip(&other.b_gens) {
            *l *= chall;
            *l += h.mul(&chall_inv);
        }
        self
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
    fn split(mut self) -> (Self, Self) {
        let n = self.a.len();
        assert_eq!(n, self.b.len());
        assert!(n > 1);
        assert!(n % 2 == 0);
        let h = n / 2;
        let a_high = self.a.split_off(h);
        let b_high = self.b.split_off(h);
        let mut other = Self {
            a: a_high,
            b: b_high,
        };
        std::mem::swap(&mut self.b, &mut other.b);
        (self, other)
    }
    fn merge(mut self, other: &Self, chall: F) -> Self {
        assert_eq!(self.a.len(), other.a.len());
        let chall_inv = chall.inverse().unwrap();
        for (l, h) in self.a.iter_mut().zip(&other.a) {
            *l *= chall;
            *l += *h * &chall_inv;
        }
        for (l, h) in self.b.iter_mut().zip(&other.b) {
            *l *= chall_inv;
            *l += *h * &chall;
        }
        self
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

struct SendIpa<G>(PhantomData<G>);

impl<G> std::default::Default for SendIpa<G> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<G: Group> Ipa<G> for SendIpa<G> {
    type Proof = IpaWitness<G::ScalarField>;

    fn prove(
        _instance: &IpaInstance<G>,
        witness: &IpaWitness<G::ScalarField>,
        _fs: &mut FiatShamirRng,
    ) -> Self::Proof {
        witness.clone()
    }

    fn check(instance: &IpaInstance<G>, proof: &Self::Proof, _fs: &mut FiatShamirRng) -> bool {
        Self::check_witness(&instance, &proof)
    }
}

fn msm<G: Group>(bases: &[G], scalars: &[G::ScalarField]) -> G {
    assert_eq!(bases.len(), scalars.len());
    let mut acc = G::zero();
    for (base, scalar) in bases.iter().zip(scalars) {
        acc += base.mul(scalar);
    }
    acc
}

fn ip<F: Field>(a: &[F], b: &[F]) -> F {
    assert_eq!(a.len(), b.len());
    let mut acc = F::zero();
    for (a, b) in a.iter().zip(b) {
        acc += *a * b;
    }
    acc
}

struct Bp<G>(PhantomData<G>);

impl<G> std::default::Default for Bp<G> {
    fn default() -> Self {
        Self(Default::default())
    }
}

fn split<T>(slice: &[T]) -> (&[T], &[T]) {
    let n = slice.len();
    assert!(n > 1);
    let h = n / 2;
    (&slice[..h], &slice[h..])
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

struct BpProof<G: Group> {
    ls: Vec<G>,
    rs: Vec<G>,
    final_a: G::ScalarField,
    final_b: G::ScalarField,
}

#[cfg(test)]
mod test {
    use super::{Bp, FiatShamirRng, Ipa, IpaInstance, SendIpa};
    use ark_bls12_381::Bls12_381;
    use ark_ec::{group::Group, PairingEngine};
    use rand::Rng;
    fn test_ipa<G: Group, I: Ipa<G>>(sizes: Vec<usize>, reps: usize) {
        let rng = &mut ark_std::test_rng();
        for size in sizes {
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

    #[test]
    fn test_send_ipa() {
        type G = <Bls12_381 as PairingEngine>::G1Projective;
        test_ipa::<G, SendIpa<G>>(vec![1, 2, 3, 4, 8, 9, 15], 1);
    }

    #[test]
    fn test_bp_ipa() {
        type G = <Bls12_381 as PairingEngine>::G1Projective;
        test_ipa::<G, Bp<G>>(vec![1, 2, 4, 8, 16], 3);
    }
}
