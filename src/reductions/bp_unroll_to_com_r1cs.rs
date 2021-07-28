use crate::{
    curves::TEPair,
    r1cs::BpRecCircuit,
    relations::{
        bp_unroll::UnrollRelation,
        com_r1cs::{ComR1csInstance, ComR1csRelation, ComR1csWitness},
    },
    util::CollectIter,
    FiatShamirRng, Reduction, Relation,
};
use ark_ec::{group::Group, ModelParameters};
use ark_ff::prelude::*;
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, OptimizationGoal, SynthesisMode,
};
use derivative::Derivative;
use std::marker::PhantomData;

#[derive(Derivative)]
#[derivative(Default(bound = ""))]
pub struct UnrollToComR1cs<P>(pub PhantomData<P>);

impl<P: TEPair> Reduction for UnrollToComR1cs<P>
where
    <P::P1 as ModelParameters>::BaseField: PrimeField,
{
    type From = UnrollRelation<P>;
    type To = ComR1csRelation<P::G2>;
    type Proof = ();

    fn prove(
        &self,
        x: &<Self::From as Relation>::Inst,
        w: &<Self::From as Relation>::Wit,
        _fs: &mut FiatShamirRng,
    ) -> (
        Self::Proof,
        <Self::To as Relation>::Inst,
        <Self::To as Relation>::Wit,
    ) {
        let cs: ConstraintSystemRef<<P::G2 as Group>::ScalarField> = ConstraintSystem::new_ref();
        let circ = BpRecCircuit::from_unrolled_bp_witness::<P>(x.clone(), w.clone());
        cs.set_optimization_goal(OptimizationGoal::Constraints);
        cs.set_mode(SynthesisMode::Prove {
            construct_matrices: true,
        });
        assert_eq!(cs.num_instance_variables(), 1);
        circ.generate_constraints(cs.clone()).unwrap();
        cs.finalize();
        let mats = cs.to_matrices().expect("No matrices");
        // (1, zs, a)
        let full_assignment: Vec<<P::G2 as Group>::ScalarField> = cs
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
        let x_r1cs = ComR1csInstance {
            m,
            r: x.r,
            n: mats.num_constraints,
            c: num_aff_coords,
            ts: x.commit_gens.clone(),
            ss: x.commits.clone(),
            r1cs: mats,
        };
        let zs = w
            .cross_terms
            .iter()
            .map(|cross| cross.to_aff_coord_list())
            .vcollect();
        let n_zs = zs.iter().map(|z| z.len()).sum::<usize>();
        let w_r1cs = ComR1csWitness {
            a: full_assignment[1+n_zs..].to_vec(),
            zs,
        };
        ((), x_r1cs, w_r1cs)
    }
    fn verify(
        &self,
        x: &<Self::From as Relation>::Inst,
        _pf: &Self::Proof,
        _fs: &mut FiatShamirRng,
    ) -> <Self::To as Relation>::Inst {
        let cs: ConstraintSystemRef<<P::G2 as Group>::ScalarField> = ConstraintSystem::new_ref();
        let circ = BpRecCircuit::from_unrolled_bp_instance::<P>(x.clone());
        cs.set_optimization_goal(OptimizationGoal::Constraints);
        cs.set_mode(SynthesisMode::Setup);
        assert_eq!(cs.num_instance_variables(), 1);
        circ.generate_constraints(cs.clone()).unwrap();
        cs.finalize();
        let mats = cs.to_matrices().expect("No matrices");
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
        x_r1cs
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        curves::{models::JubJubPair, TEPair},
        reductions::{bp_unroll_to_com_r1cs::UnrollToComR1cs, ipa_to_bp_unroll::IpaToBpUnroll},
        relations::{com_r1cs::ComR1csRelation, ipa::IpaInstance},
    };
    use ark_ec::twisted_edwards_extended::GroupProjective;
    use rand::Rng;
    fn test_from_bp_unroll<P: TEPair>(init_size: usize, k: usize, r: usize)
    where
        <P::P1 as ModelParameters>::BaseField: PrimeField,
    {
        println!(
            "doing a unrolled circuit check with {} elems, k: {}, r: {}",
            init_size, k, r
        );
        let rng = &mut ark_std::test_rng();
        let fs_seed: [u8; 32] = rng.gen();
        let mut fs_rng = crate::FiatShamirRng::from_seed(&fs_seed);
        let mut v_fs_rng = crate::FiatShamirRng::from_seed(&fs_seed);
        let (instance, witness) =
            IpaInstance::<GroupProjective<P::P1>>::sample_from_length(rng, init_size);
        let reducer = IpaToBpUnroll::<P>::new(k, r);
        let (proof, u_instance, u_witness) = reducer.prove(&instance, &witness, &mut fs_rng);
        //UnrollRelation::check(&u_instance, &u_witness);
        let verif_u_instance = reducer.verify(&instance, &proof, &mut v_fs_rng);
        assert_eq!(verif_u_instance, u_instance);
        //UnrollRelation::check(&verif_u_instance, &u_witness);
        let reducer2 = UnrollToComR1cs::<P>::default();
        let ((), r_instance, r_witness) = reducer2.prove(&u_instance, &u_witness, &mut fs_rng);
        ComR1csRelation::check(&r_instance, &r_witness);
    }

    #[test]
    fn jubjub_unroll_test() {
        test_from_bp_unroll::<JubJubPair>(4, 2, 1);
        test_from_bp_unroll::<JubJubPair>(8, 2, 2);
        test_from_bp_unroll::<JubJubPair>(8, 2, 3);
        test_from_bp_unroll::<JubJubPair>(9, 3, 1);
        test_from_bp_unroll::<JubJubPair>(9, 3, 2);
        test_from_bp_unroll::<JubJubPair>(2048, 4, 4);
        test_from_bp_unroll::<JubJubPair>(2048, 4, 5);
    }
}
