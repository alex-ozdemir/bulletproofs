#![allow(dead_code)]
use ark_ec::group::Group;
use ark_ff::{BigInteger, FpParameters, One, PrimeField, Zero};

use derivative::Derivative;

use std::collections::BinaryHeap;

#[track_caller]
pub fn msm<'a, G: Group>(
    bases: impl IntoIterator<Item = &'a G>,
    scalars: impl IntoIterator<Item = &'a G::ScalarField>,
) -> G {
    //assert_eq!(bases.len(), scalars.len());
    let mut acc = G::zero();
    for (base, scalar) in bases.into_iter().zip(scalars) {
        acc += base.mul(scalar);
    }
    acc
}

#[derive(Derivative)]
#[derivative(PartialEq, Eq, PartialOrd, Ord)]
pub struct Entry<S, G> {
    pub x: S,
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Ord = "ignore")]
    pub g: G,
}

#[track_caller]
pub fn bos_coster_msm<'a, G: Group>(
    bases: impl IntoIterator<Item = &'a G>,
    scalars: impl IntoIterator<Item = &'a G::ScalarField>,
) -> G {
    //assert_eq!(bases.len(), scalars.len());
    let mut heap = BinaryHeap::new();
    for (b, s) in bases.into_iter().zip(scalars) {
        if !s.is_zero() {
            heap.push(Entry {
                x: s.clone().into_repr(),
                g: b.clone(),
            })
        }
    }
    while heap.len() > 1 {
        let mut first = heap.pop().unwrap();
        let mut second = heap.pop().unwrap();
        let half_first = {
            let mut t = first.x;
            t.div2();
            t
        };
        if half_first > second.x {
            heap.push(second);
            if first.x.is_odd() {
                heap.push(Entry {
                    x: G::ScalarField::one().into_repr(),
                    g: first.g.clone(),
                });
            }
            first.x.div2();
            first.g.double_in_place();
            heap.push(first);
        } else {
            assert!(!first.x.sub_noborrow(&second.x));
            second.g = first.g + &second.g;
            heap.push(second);
            if !first.x.is_zero() {
                heap.push(first);
            }
        }
    }
    match heap.pop() {
        Some(last) => last.g.mul(&G::ScalarField::from_repr(last.x).unwrap()),
        None => G::zero(),
    }
}

fn ln_without_floats(a: usize) -> usize {
    // log2(a) * ln(2)
    (ark_std::log2(a) * 69 / 100) as usize
}

#[track_caller]
pub fn pippenger_msm<'a, G: Group>(
    bases: impl IntoIterator<Item = &'a G>,
    scalars: impl IntoIterator<Item = &'a G::ScalarField>,
) -> G {
    // Copied from ark-ec, more or less
    let (bases, scalars): (Vec<&'a G>, Vec<<G::ScalarField as PrimeField>::BigInt>) = bases
        .into_iter()
        .zip(scalars.into_iter().map(|s| s.into_repr()))
        .unzip();
    let size = bases.len();
    let scalars_and_bases_iter = scalars.iter().zip(bases).filter(|(s, _)| !s.is_zero());

    let c = if size < 32 {
        3
    } else {
        ln_without_floats(size) + 2
    };

    let num_bits = <G::ScalarField as PrimeField>::Params::MODULUS_BITS as usize;
    let fr_one = G::ScalarField::one().into_repr();

    let zero = G::zero();
    let window_starts: Vec<_> = (0..num_bits).step_by(c).collect();

    // Each window is of size `c`.
    // We divide up the bits 0..num_bits into windows of size `c`, and
    // in parallel process each such window.
    let window_sums: Vec<_> = window_starts.into_iter()
    // uncomment for parallelism
    //let window_sums: Vec<_> = ark_std::cfg_into_iter!(window_starts)
        .map(|w_start| {
            let mut res = zero;
            // We don't need the "zero" bucket, so we only have 2^c - 1 buckets.
            let mut buckets = vec![zero; (1 << c) - 1];
            // This clone is cheap, because the iterator contains just a
            // pointer and an index into the original vectors.
            scalars_and_bases_iter.clone().for_each(|(&scalar, base)| {
                if scalar == fr_one {
                    // We only process unit scalars once in the first window.
                    if w_start == 0 {
                        res += base;
                        //res.add_assign_mixed(base);
                    }
                } else {
                    let mut scalar = scalar;

                    // We right-shift by w_start, thus getting rid of the
                    // lower bits.
                    scalar.divn(w_start as u32);

                    // We mod the remaining bits by 2^{window size}, thus taking `c` bits.
                    let scalar = scalar.as_ref()[0] % (1 << c);

                    // If the scalar is non-zero, we update the corresponding
                    // bucket.
                    // (Recall that `buckets` doesn't have a zero bucket.)
                    if scalar != 0 {
                        // buckets[(scalar - 1) as usize].add_assign_mixed(base);
                        buckets[(scalar - 1) as usize] += base;
                    }
                }
            });

            // Compute sum_{i in 0..num_buckets} (sum_{j in i..num_buckets} bucket[j])
            // This is computed below for b buckets, using 2b curve additions.
            //
            // We could first normalize `buckets` and then use mixed-addition
            // here, but that's slower for the kinds of groups we care about
            // (Short Weierstrass curves and Twisted Edwards curves).
            // In the case of Short Weierstrass curves,
            // mixed addition saves ~4 field multiplications per addition.
            // However normalization (with the inversion batched) takes ~6
            // field multiplications per element,
            // hence batch normalization is a slowdown.

            // `running_sum` = sum_{j in i..num_buckets} bucket[j],
            // where we iterate backward from i = num_buckets to 0.
            let mut running_sum = G::zero();
            buckets.into_iter().rev().for_each(|b| {
                running_sum += &b;
                res += &running_sum;
            });
            res
        })
        .collect();

    // We store the sum for the lowest window.
    let lowest = *window_sums.first().unwrap();

    // We're traversing windows from high to low.
    lowest
        + &window_sums[1..]
            .iter()
            .rev()
            .fold(zero, |mut total, sum_i| {
                total += sum_i;
                for _ in 0..c {
                    total.double_in_place();
                }
                total
            })
}

#[cfg(test)]
mod test {
    use super::*;
    mod benches {
        use super::*;
        use crate::util::CollectIter;
        use ark_ff::UniformRand;
        use rust_test::Bencher;

        #[bench]
        fn pallas_naive_msm(b: &mut Bencher) {
            type G = ark_pallas::Projective;
            let length = 200;
            let rng = &mut ark_std::test_rng();
            let gs = (0..length).map(|_| G::rand(rng)).vcollect();
            let xs = (0..length)
                .map(|_| <G as Group>::ScalarField::rand(rng))
                .vcollect();
            b.iter(|| msm(&gs, &xs))
        }

        #[bench]
        fn pallas_bos_coster_msm(b: &mut Bencher) {
            type G = ark_pallas::Projective;
            let length = 200;
            let rng = &mut ark_std::test_rng();
            let gs = (0..length).map(|_| G::rand(rng)).vcollect();
            let xs = (0..length)
                .map(|_| <G as Group>::ScalarField::rand(rng))
                .vcollect();
            b.iter(|| bos_coster_msm(&gs, &xs))
        }
        #[bench]
        fn pallas_pippenger_msm(b: &mut Bencher) {
            type G = ark_pallas::Projective;
            let length = 200;
            let rng = &mut ark_std::test_rng();
            let gs = (0..length).map(|_| G::rand(rng)).vcollect();
            let xs = (0..length)
                .map(|_| <G as Group>::ScalarField::rand(rng))
                .vcollect();
            b.iter(|| pippenger_msm(&gs, &xs))
        }
    }
}
