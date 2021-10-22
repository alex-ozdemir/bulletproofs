#![allow(dead_code)]
use ark_ec::group::Group;
use ark_ff::{BigInteger, One, PrimeField, Zero};

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
    }
}
