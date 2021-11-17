use crate::{
    timed,
    curves::Pair,
    r1cs::BpRecCircuit,
    relations::{
        bp_unroll::UnrollRelation,
        com_r1cs::{ComR1csInstance, ComR1csRelation, ComR1csWitness},
    },
    util::CollectIter,
    FiatShamirRng, Reduction, Relation,
};
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, OptimizationGoal, SynthesisMode,
};
use derivative::Derivative;
use std::marker::PhantomData;
use log::debug;
use ark_std::{start_timer, end_timer};

#[derive(Derivative)]
#[derivative(Default(bound = ""))]
pub struct UnrollToComR1cs<C>(pub PhantomData<C>);

impl<C: Pair> Reduction for UnrollToComR1cs<C> {
    type From = UnrollRelation<C>;
    type To = ComR1csRelation<C::G2>;
    type Params = ();
    type Proof = ();

    fn prove(
        &self,
        _pp: &Self::Params,
        x: &<Self::From as Relation>::Inst,
        w: &<Self::From as Relation>::Wit,
        fs: &mut FiatShamirRng,
    ) -> (
        Self::Proof,
        <Self::To as Relation>::Inst,
        <Self::To as Relation>::Wit,
    ) {
        let timer = start_timer!(|| "proving unroll-to-com-r1cs");
        let cs: ConstraintSystemRef<C::LinkField> = ConstraintSystem::new_ref();
        let circ = BpRecCircuit::from_unrolled_bp_witness(x.clone(), w.clone(), fs);
        cs.set_optimization_goal(OptimizationGoal::Constraints);
        cs.set_mode(SynthesisMode::Prove {
            construct_matrices: true,
        });
        assert_eq!(cs.num_instance_variables(), 1);
        circ.generate_constraints(cs.clone()).unwrap();
        timed!(|| "Finalize R1CS", cs.finalize());
        //assert!(cs.is_satisfied().unwrap());
        let mats = timed!(|| "extract matrices", cs.to_matrices().expect("No matrices"));
        // (1, zs, a)
        let full_assignment: Vec<C::LinkField> = cs
            .borrow()
            .unwrap()
            .instance_assignment
            .iter()
            .chain(&cs.borrow().unwrap().witness_assignment)
            .cloned()
            .vcollect();
        assert_eq!(mats.num_instance_variables, 1);
        let m = mats.num_instance_variables + mats.num_witness_variables;
        assert_eq!(full_assignment.len(), m);
        let num_cross_terms = (x.k - 1) * 2;
        let num_aff_coords = num_cross_terms * 2;
        debug!("R1CS: n={}, m={}", mats.num_constraints, m);
        let x_r1cs = ComR1csInstance {
            m,
            r: x.r,
            n: mats.num_constraints,
            c: num_aff_coords,
            ts: x.commit_gens.clone(),
            ss: x.commits.clone(),
            r1cs: mats,
        };
        debug!("Number of constraints: {}", x_r1cs.n);
        let zs = w
            .cross_terms
            .iter()
            .map(|cross| cross.to_aff_coord_list())
            .vcollect();
        let n_zs = zs.iter().map(|z| z.len()).sum::<usize>();
        let w_r1cs = ComR1csWitness {
            a: full_assignment[1 + n_zs..].to_vec(),
            zs,
        };
        end_timer!(timer);
        ((), x_r1cs, w_r1cs)
    }
    fn verify(
        &self,
        _pp: &Self::Params,
        x: &<Self::From as Relation>::Inst,
        _pf: &Self::Proof,
        fs: &mut FiatShamirRng,
    ) -> <Self::To as Relation>::Inst {
        let timer = start_timer!(|| "verifying unroll-to-com-r1cs");
        let cs: ConstraintSystemRef<C::LinkField> = ConstraintSystem::new_ref();
        let circ = BpRecCircuit::from_unrolled_bp_instance(x.clone(), fs);
        cs.set_optimization_goal(OptimizationGoal::Constraints);
        cs.set_mode(SynthesisMode::Setup);
        assert_eq!(cs.num_instance_variables(), 1);
        circ.generate_constraints(cs.clone()).unwrap();
        timed!(|| "finalize", cs.finalize());
        let mats = timed!(|| "extract matrices", cs.to_matrices().expect("No matrices"));
        assert_eq!(mats.num_instance_variables, 1);
        let num_cross_terms = (x.k - 1) * 2;
        let num_aff_coords = num_cross_terms * 2;
        let x_r1cs = ComR1csInstance {
            m: mats.num_instance_variables + mats.num_witness_variables,
            r: x.r,
            n: mats.num_constraints,
            c: num_aff_coords,
            ts: x.commit_gens.clone(),
            ss: x.commits.clone(),
            r1cs: mats,
        };
        end_timer!(timer);
        x_r1cs
    }
    fn proof_size(_p: &Self::Proof) -> usize {
        0
    }
    fn setup<R: rand::Rng>(&self, _: &<Self::From as Relation>::Cfg, _: &mut R) -> Self::Params {
        ()
    }
    fn map_params(&self, (m, k, r): &<Self::From as Relation>::Cfg) -> <Self::To as Relation>::Cfg {
        // FS-MSM size
        let l = 2 * (k - 1) * r + 1;
        let l: f64 = l as f64;
        let m: f64 = *m as f64;
        let l_log2l: f64 = l / l.log2();
        // From our cost modeling. See analysis/cost.py
        let cs_expected: f64 = 1765.4 + 1288.0 * l_log2l + 1801.0 * m;
        // Add some buffer
        let cs = (cs_expected * 1.25 + 1000.0) as usize;
        (cs, cs)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        curves::{
            models::{JubJubPair, PastaPair, VellasPair},
            Pair,
        },
        reductions::{bp_unroll_to_com_r1cs::UnrollToComR1cs, ipa_to_bp_unroll::IpaToBpUnroll},
        relations::{com_r1cs::ComR1csRelation, ipa::IpaInstance},
    };
    use rand::Rng;
    fn test_from_bp_unroll<C: Pair>(init_size: usize, k: usize, r: usize) {
        println!(
            "doing a unrolled circuit check with {} elems, k: {}, r: {}",
            init_size, k, r
        );
        let rng = &mut ark_std::test_rng();
        let fs_seed: [u8; 32] = rng.gen();
        let mut fs_rng = crate::FiatShamirRng::from_seed(&fs_seed);
        let mut v_fs_rng = crate::FiatShamirRng::from_seed(&fs_seed);
        let (instance, witness) = IpaInstance::<C::G1>::sample_from_length(rng, init_size);
        let reducer = IpaToBpUnroll::<C>::new(k, r);
        let pp = reducer.setup(&init_size, rng);
        let (proof, u_instance, u_witness) = reducer.prove(&pp, &instance, &witness, &mut fs_rng);
        UnrollRelation::check(&u_instance, &u_witness);
        let verif_u_instance = reducer.verify(&pp, &instance, &proof, &mut v_fs_rng);
        assert_eq!(verif_u_instance, u_instance);
        UnrollRelation::check(&verif_u_instance, &u_witness);
        let reducer2 = UnrollToComR1cs::<C>::default();
        let ((), r_instance, r_witness) = reducer2.prove(&(), &u_instance, &u_witness, &mut fs_rng);
        ComR1csRelation::check(&r_instance, &r_witness);
        let v_r_instance = reducer2.verify(&(), &u_instance, &(), &mut v_fs_rng);
        ComR1csRelation::check(&v_r_instance, &r_witness);
    }

    #[test]
    fn jubjub_unroll_test() {
        test_from_bp_unroll::<JubJubPair>(4, 2, 1);
        //test_from_bp_unroll::<JubJubPair>(8, 2, 2);
        //test_from_bp_unroll::<JubJubPair>(8, 2, 3);
        //test_from_bp_unroll::<JubJubPair>(9, 3, 1);
        //test_from_bp_unroll::<JubJubPair>(9, 3, 2);
        //test_from_bp_unroll::<JubJubPair>(2048, 4, 4);
        //test_from_bp_unroll::<JubJubPair>(2048, 4, 5);
    }
    #[test]
    fn pasta_unroll_test() {
        test_from_bp_unroll::<PastaPair>(4, 2, 1);
    }
    #[test]
    fn vellas_unroll_test() {
        test_from_bp_unroll::<VellasPair>(4, 2, 1);
    }
}
