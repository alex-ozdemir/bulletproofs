//! This module contains the relation from `doc/compiler.pdf`.
//!
//! It follows the notation there.
//!
//! The relation extends R1CS to witnesses which are partially committed.
use crate::{
    util::{hadamard, msm, CollectIter},
    Relation,
};
use ark_ec::group::Group;
use ark_ff::prelude::*;
use ark_relations::r1cs::{ConstraintMatrices, Matrix};
use derivative::Derivative;
use std::iter::once;
use std::marker::PhantomData;

pub struct ComR1csInstance<G: Group> {
    pub r1cs: ConstraintMatrices<G::ScalarField>,
    pub n: usize,
    pub r: usize,
    pub m: usize,
    /// Commitment size (`m'`)
    pub c: usize,
    pub ts: Vec<Vec<G>>,
    pub ss: Vec<G>,
}

pub struct ComR1csWitness<F: Field> {
    pub a: Vec<F>,
    pub zs: Vec<Vec<F>>,
}

impl<F: Field> ComR1csWitness<F> {
    pub fn full_assignment(&self) -> Vec<F> {
        once(F::one())
            .chain(self.zs.iter().flat_map(|x| x.clone()))
            .chain(self.a.iter().cloned())
            .vcollect()
    }
}

pub fn mat_vec_mult<F: Field>(mat: &Matrix<F>, vec: &[F]) -> Vec<F> {
    // matrices are lists of rows
    // rows are (value, idx) pairs
    let mut result = vec![F::zero(); mat.len()];
    for (r, mat_row) in mat.iter().enumerate() {
        for (mat_val, c) in mat_row.iter() {
            assert!(c < &vec.len());
            result[r] += *mat_val * vec[*c];
        }
    }
    result
}

pub fn mat_cols<F: Field>(mat: &Matrix<F>) -> usize {
    mat.iter()
        .flat_map(|row| row.iter().map(|(_, col_i)| *col_i))
        .max()
        .map(|i| i + 1)
        .unwrap_or(0)
}

pub fn vec_mat_mult<F: Field>(vec: &[F], mat: &Matrix<F>, output_size: usize) -> Vec<F> {
    // matrices are lists of rows
    // rows are (value, idx) pairs
    assert!(mat_cols(mat) <= output_size);
    let mut result = vec![F::zero(); output_size];
    assert_eq!(vec.len(), mat.len());
    for (r, mat_row) in mat.iter().enumerate() {
        for (mat_val, c) in mat_row.iter() {
            result[*c] += *mat_val * vec[r];
        }
    }
    result
}

#[derive(Derivative)]
#[derivative(Default(bound = ""))]
pub struct ComR1csRelation<G: Group>(pub PhantomData<G>);

impl<G: Group> Relation for ComR1csRelation<G> {
    /// (n_vars, n_constraints)
    type Cfg = (usize, usize);
    type Inst = ComR1csInstance<G>;
    type Wit = ComR1csWitness<G::ScalarField>;
    fn check(x: &Self::Inst, w: &Self::Wit) {
        assert_eq!(
            x.m,
            x.r1cs.num_instance_variables + x.r1cs.num_witness_variables
        );
        assert_eq!(x.r, x.ts.len());
        assert_eq!(x.r, x.ss.len());
        x.ts.iter().for_each(|t| assert_eq!(t.len(), x.c));
        w.zs.iter().for_each(|t| assert_eq!(t.len(), x.c));
        assert_eq!(x.n, x.r1cs.num_constraints);

        let z = w.full_assignment();
        assert_eq!(x.m, z.len());
        let az = mat_vec_mult(&x.r1cs.a, &z);
        let bz = mat_vec_mult(&x.r1cs.b, &z);
        let cz = mat_vec_mult(&x.r1cs.c, &z);

        let abz = hadamard(&az, &bz);

        for (i, (a, b)) in abz.iter().zip(&cz).enumerate() {
            if a != b {
                println!("Issue at {}:\n  {} v\n  {}", i, a, b);
            }
        }

        // Az * Bz = Cz (hadamard)
        // AO: May fail b/c a commitment is not first!
        assert_eq!(&abz, &cz);

        // check commitments
        for i in 0..x.r {
            // S_i = z_i * T_i
            assert_eq!(x.ss[i], msm(&x.ts[i], &w.zs[i]));
        }
    }

    fn check_cfg((n_vars, n_cs): &Self::Cfg, x: &Self::Inst) {
        assert!(x.n <= *n_vars, "vars:{}\nsupported:{}", x.n, n_vars);
        assert!(x.m <= *n_cs, "constraints:{}\nsupported:{}", x.n, n_cs);
    }

    fn size(x: &Self::Inst) -> Self::Cfg {
        (x.m, x.n)
    }
}
