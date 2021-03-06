use ark_ec::group::Group;
use ark_ff::{Field, UniformRand, Zero};
use rand::Rng;
use std::ops::Range;
use std::ops::{AddAssign, MulAssign};

use ark_std::{cfg_into_iter, cfg_iter, cfg_iter_mut};
#[cfg(feature = "parallel")]
use rayon::prelude::*;

use crate::timed;

pub mod msm;

pub use msm::pippenger_msm as msm;

#[track_caller]
pub fn ip<F: Field>(a: &[F], b: &[F]) -> F {
    timed!(|| "ip", {
        assert_eq!(a.len(), b.len());
        cfg_iter!(a).zip(b).map(|(a, b)| *a * b).sum()
    })
}

pub fn scale_vec<S: Clone + Sync + Send, F: MulAssign<S> + Clone + Sync + Send>(
    s: &S,
    b: &[F],
) -> Vec<F> {
    timed!(|| "scale_vec", {
        cfg_into_iter!(b)
            .map(|b| {
                let mut c = b.clone();
                c *= s.clone();
                c
            })
            .collect()
    })
}

#[track_caller]
pub fn sum_vecs<F: AddAssign + Zero + Clone + Send + Sync, I: IntoIterator<Item = Vec<F>>>(
    i: I,
    len: usize,
) -> Vec<F> {
    timed!(|| "sum_vecs", {
        i.into_iter()
            .fold(vec![F::zero(); len], |mut acc, summand| {
                assert_eq!(summand.len(), len);
                cfg_iter_mut!(acc).zip(summand).for_each(|(a, b)| {
                    *a += b;
                });
                acc
            })
    })
}

pub fn powers<F: Field>(f: F, range: Range<usize>) -> Vec<F> {
    timed!(|| "powers", {
        let first = f.pow(&[range.start as u64]);
        std::iter::successors(Some(first), |acc| Some(*acc * f))
            .take(range.end - range.start)
            .collect()
    })
}

pub fn neg_powers<F: Field>(f: F, range: Range<usize>) -> Vec<F> {
    powers(f.inverse().unwrap(), range)
}

pub fn hadamard_gp<G: Group>(bases: &[G], scalars: &[G::ScalarField]) -> Vec<G> {
    timed!(|| "hadamard_gp", {
        assert_eq!(bases.len(), scalars.len());
        cfg_iter!(bases)
            .zip(scalars)
            .map(|(base, scalar)| base.mul(scalar))
            .collect()
    })
}

pub fn hadamard<F: Field>(a: &[F], b: &[F]) -> Vec<F> {
    timed!(|| "hadamard", {
        assert_eq!(a.len(), b.len());
        cfg_iter!(a).zip(b).map(|(a, b)| *a * b).collect()
    })
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
    timed!(|| "rand_vec", (0..n).map(|_| U::rand(rng)).collect())
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

/// Copy array into a vector, interspersing zeros to make the final length a multiple of k.
///
/// Cuts the original array into k blocks. These blocks will now have two lengths.
/// For each block, if it is too short, adds a zero to it.
pub fn zero_intersperse_to_multiple<Z: Zero + Clone>(array: &[Z], k: usize) -> Vec<Z> {
    let block_size = (array.len() - 1) / k + 1;
    let final_size = block_size * k;
    let n_short_blocks = final_size - array.len();
    let mut output = Vec::new();
    for i in 0..k {
        if i >= k - n_short_blocks {
            let start =
                block_size * (k - n_short_blocks) + (block_size - 1) * (i + n_short_blocks - k);
            output.extend(array[start..start + block_size - 1].iter().cloned());
            output.push(Z::zero());
        } else {
            output.extend(array[block_size * i..block_size * (i + 1)].iter().cloned());
        }
    }
    assert_eq!(final_size, output.len());
    output
}

/// Copy array into a vector, making length a power of two
pub fn zero_pad_to_two_power<Z: Zero + Clone>(array: &[Z]) -> Vec<Z> {
    let mut array = array.to_vec();
    let desired_len = array.len().next_power_of_two();
    if desired_len > array.len() {
        array.extend(std::iter::repeat(Z::zero()).take(desired_len - array.len()));
    }
    array
}

#[cfg(test)]
mod test {
    use super::*;
    mod pallas {
        use super::*;

        use ark_pallas::Fr;

        #[test]
        fn zero_intersperse_max_fill() {
            let xs = (1u32..=4u32).map(|s| Fr::from(s)).vcollect();
            let ys = zero_intersperse_to_multiple(&xs, 3);
            assert_eq!(
                vec![
                    Fr::from(1),
                    Fr::from(2),
                    Fr::from(3),
                    Fr::from(0),
                    Fr::from(4),
                    Fr::from(0),
                ],
                ys
            );
        }
        #[test]
        fn zero_intersperse_full() {
            let xs = (1u32..=6u32).map(|s| Fr::from(s)).vcollect();
            let ys = zero_intersperse_to_multiple(&xs, 3);
            assert_eq!(
                vec![
                    Fr::from(1),
                    Fr::from(2),
                    Fr::from(3),
                    Fr::from(4),
                    Fr::from(5),
                    Fr::from(6),
                ],
                ys
            );
        }
        #[test]
        fn zero_intersperse_one_short() {
            let xs = (1u32..=5u32).map(|s| Fr::from(s)).vcollect();
            let ys = zero_intersperse_to_multiple(&xs, 3);
            assert_eq!(
                vec![
                    Fr::from(1),
                    Fr::from(2),
                    Fr::from(3),
                    Fr::from(4),
                    Fr::from(5),
                    Fr::from(0),
                ],
                ys
            );
        }
    }
}
