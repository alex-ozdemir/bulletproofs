//! This module contains the relation from `doc/compiler.pdf`.
//!
//! It follows the notation there.
//!
//! The relation extends R1CS to witnesses which are partially committed.
use ark_ff::prelude::*;
use ark_ec::group::Group;
use ark_relations::r1cs::{ConstraintMatrices, Matrix};
use crate::util::{CollectIter, hadamard, msm};
use std::iter::once;

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

fn mat_vec_mult<F: Field>(mat: &Matrix<F>, vec: &[F]) -> Vec<F> {
    // matrices are lists of rows
    // rows are (value, idx) pairs
    let mut result = vec![F::zero(); mat.len()];
    for (r, mat_row) in mat.iter().enumerate() {
        for (mat_val, c) in mat_row.iter() {
            result[r] += *mat_val * vec[*c];
        }
    }
    result
}

impl<G: Group> ComR1csInstance<G> {
    pub fn check_witness(&self, w: &ComR1csWitness<G::ScalarField>) {
        assert_eq!(self.n, self.r1cs.num_instance_variables + self.r1cs.num_witness_variables);
        assert_eq!(self.r, self.ts.len());
        assert_eq!(self.r, self.ss.len());
        self.ts.iter().for_each(|t| assert_eq!(t.len(), self.c));
        w.zs.iter().for_each(|t| assert_eq!(t.len(), self.c));
        assert_eq!(self.m, self.r1cs.num_constraints);

        let z = once(G::ScalarField::one()).chain(w.zs.iter().flat_map(|x| x.clone())).chain(w.a.iter().cloned()).vcollect();
        let az = mat_vec_mult(&self.r1cs.a, &z);
        let bz = mat_vec_mult(&self.r1cs.b, &z);
        let cz = mat_vec_mult(&self.r1cs.c, &z);

        // Az * Bz = Cz (hadamard)
        assert_eq!(&hadamard(&az, &bz), &cz);

        for i in 0..self.r {
            // S_i = z_i * T_i
            assert_eq!(self.ss[i], msm(&self.ts[i], &w.zs[i]));
        }
    }
}

//    pub fn to_com_r1cs(&self) -> (com::ComR1csInstance<GroupProjective<P>>, Option<com::ComR1csWitness<P::ScalarField>>) {
//        let cs: ConstraintSystemRef<P::BaseField> = ConstraintSystem::new_ref();
//        cs.set_optimization_goal(OptimizationGoal::Constraints);
//        cs.set_mode(SynthesisMode::Setup);
//        circ.generate_constraints(cs.clone()).unwrap();
//        let mats = cs.to_matrices().expect("No matrices");
//        com::ComR1csInstance {
//            r1cs: mats,
//            n: mats.num_constraints,
//            r: 
//        }
//        todo!()
//    }
