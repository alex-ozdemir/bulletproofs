use ark_ec::group::Group;
use ark_ff::Field;

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

