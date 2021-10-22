use ark_ec::group::Group;
use ark_ff::{Field, UniformRand, Zero};
use rand::Rng;
use std::ops::Range;
use std::ops::{AddAssign, MulAssign};

mod msm;

pub use msm::bos_coster_msm as msm;

#[track_caller]
pub fn ip<F: Field>(a: &[F], b: &[F]) -> F {
    assert_eq!(a.len(), b.len());
    let mut acc = F::zero();
    for (a, b) in a.iter().zip(b) {
        acc += *a * b;
    }
    acc
}

pub fn scale_vec<S: Clone, F: MulAssign<S> + Clone>(s: &S, b: &[F]) -> Vec<F> {
    let mut b = b.to_vec();
    for b in &mut b {
        *b *= s.clone();
    }
    b
}

#[track_caller]
pub fn sum_vecs<F: AddAssign + Zero + Clone, I: IntoIterator<Item = Vec<F>>>(
    i: I,
    len: usize,
) -> Vec<F> {
    i.into_iter()
        .fold(vec![F::zero(); len], |mut acc, summand| {
            assert_eq!(summand.len(), len);
            for (a, b) in acc.iter_mut().zip(summand) {
                *a += b;
            }
            acc
        })
}

pub fn powers<F: Field>(f: F, range: Range<usize>) -> Vec<F> {
    let first = f.pow(&[range.start as u64]);
    std::iter::successors(Some(first), |acc| Some(*acc * f))
        .take(range.end - range.start)
        .collect()
}

pub fn neg_powers<F: Field>(f: F, range: Range<usize>) -> Vec<F> {
    powers(f.inverse().unwrap(), range)
}

pub fn hadamard_gp<G: Group>(bases: &[G], scalars: &[G::ScalarField]) -> Vec<G> {
    assert_eq!(bases.len(), scalars.len());
    bases
        .iter()
        .zip(scalars)
        .map(|(base, scalar)| base.mul(scalar))
        .collect()
}

pub fn hadamard<F: Field>(a: &[F], b: &[F]) -> Vec<F> {
    assert_eq!(a.len(), b.len());
    a.iter().zip(b).map(|(a, b)| *a * b).collect()
}

pub trait CollectIter: Iterator + Sized
where
    Self::Item: Sized,
{
    fn vcollect(self) -> Vec<<Self as Iterator>::Item> {
        self.collect()
    }
}

impl<I: Iterator> CollectIter for I {}

pub fn rand_vec<U: UniformRand, R: Rng>(n: usize, rng: &mut R) -> Vec<U> {
    (0..n).map(|_| U::rand(rng)).collect()
}

/// Copy array into a vector, length at least k
pub fn zero_pad_to_multiple<Z: Zero + Clone>(array: &[Z], k: usize) -> Vec<Z> {
    let mut array = array.to_vec();
    let chunksize = (array.len() - 1) / k + 1;
    let desired_len = chunksize * k;
    if desired_len > array.len() {
        array.extend(std::iter::repeat(Z::zero()).take(desired_len - array.len()));
    }
    array
}
