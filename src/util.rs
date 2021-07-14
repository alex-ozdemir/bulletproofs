use ark_ec::group::Group;
use ark_ff::{Field, Zero};
use std::ops::{AddAssign, MulAssign};

pub fn msm<G: Group>(bases: &[G], scalars: &[G::ScalarField]) -> G {
    assert_eq!(bases.len(), scalars.len());
    let mut acc = G::zero();
    for (base, scalar) in bases.iter().zip(scalars) {
        acc += base.mul(scalar);
    }
    acc
}

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

pub fn sum_vecs<F: AddAssign + Zero + Clone, I: IntoIterator<Item = Vec<F>>>(i: I, len: usize) -> Vec<F> {
    i.into_iter().fold(vec![F::zero(); len], |mut acc, summand| {
        assert_eq!(summand.len(), len);
        for (a, b) in acc.iter_mut().zip(summand) {
            *a += b;
        }
        acc
    })
}

