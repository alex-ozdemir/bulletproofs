use vector_addition_chain::{bos_coster_fast::build_chain, check_chain};

use ark_ec::models::twisted_edwards_extended::GroupAffine;
use ark_ec::models::TEModelParameters;
use ark_ff::prelude::*;

use ark_r1cs_std::groups::curves::twisted_edwards::AffineVar;

use ark_relations::{
    ns,
    r1cs::{self, ConstraintSynthesizer, ConstraintSystemRef},
};

use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::{alloc::AllocationMode, eq::EqGadget};

pub struct KnownScalarMsm<P: TEModelParameters> {
    pub scalars: Vec<P::ScalarField>,
    pub points: Option<Vec<GroupAffine<P>>>,
    pub result: Option<GroupAffine<P>>,
}

pub fn known_scalar_msm<P: TEModelParameters>(
    scalars: Vec<P::ScalarField>,
    mut points: Vec<AffineVar<P, FpVar<P::BaseField>>>,
) -> AffineVar<P, FpVar<P::BaseField>>
where
    P::BaseField: PrimeField,
{
    assert!(points.len() > 0);
    let chain = build_chain(scalars.clone());
    check_chain(&chain, &scalars);
    for (a, b) in &chain.adds {
        let new = points[*a].clone() + points[*b].clone();
        points.push(new);
    }
    println!("Additions per element: {}", chain.adds.len() as f64 / scalars.len() as f64);
    points.pop().unwrap()
}

impl<P: TEModelParameters> ConstraintSynthesizer<P::BaseField> for KnownScalarMsm<P>
where
    P::BaseField: PrimeField,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<P::BaseField>) -> r1cs::Result<()> {
        let pts = (0..self.scalars.len())
            .map(|i| {
                // TODO: check
                let v = AffineVar::new_variable_omit_on_curve_check(
                    ns!(cs, "point"),
                    || Ok(self.points.as_ref().unwrap()[i]),
                    AllocationMode::Witness,
                )?;
                Ok(v)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let result = known_scalar_msm(self.scalars.clone(), pts);
        let ex_result = AffineVar::new_variable_omit_on_curve_check(
            ns!(cs, "point2"),
            || Ok(self.result.as_ref().unwrap().clone()),
            AllocationMode::Input,
        )?;
        result.enforce_equal(&ex_result)?;
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_relations::r1cs::{ConstraintLayer, OptimizationGoal, TracingMode};
    use tracing_subscriber::layer::SubscriberExt;
    use ark_ec::AffineCurve;

    fn msm_test<P: TEModelParameters>(len: usize)
    where
        P::BaseField: PrimeField,
    {
        let rng = &mut ark_std::test_rng();
        // First, some boilerplat that helps with debugging
        let mut layer = ConstraintLayer::default();
        layer.mode = TracingMode::OnlyConstraints;
        let subscriber = tracing_subscriber::Registry::default().with(layer);
        let _guard = tracing::subscriber::set_default(subscriber);
        let cs: ConstraintSystemRef<P::BaseField> = ConstraintSystem::new_ref();
        cs.set_optimization_goal(OptimizationGoal::Constraints);
        let pts: Vec<_> = (0..len).map(|_| GroupAffine::<P>::rand(rng)).collect();
        //let pts: Vec<_> = (0..2).map(|_| GroupAffine::<P>::rand(rng)).collect();
        let scalars: Vec<_> = (0..len).map(|_| P::ScalarField::rand(rng)).collect();
        //let scalars = vec![P::ScalarField::from(7u32), P::ScalarField::from(2u32)];
        let scalar_ints: Vec<<P::ScalarField as PrimeField>::BigInt> = scalars.iter().map(|s| s.into_repr()).collect();
        let result: GroupAffine<P> = ark_ec::msm::VariableBaseMSM::multi_scalar_mul(&pts, &scalar_ints).into();
        let msm = KnownScalarMsm {
            points: Some(pts),
            scalars,
            result: Some(result),
        };
        msm.generate_constraints(cs.clone()).unwrap();
        cs.finalize();
        assert!(cs.is_satisfied().unwrap());
        println!("Constraints: {}", cs.num_constraints());
        println!("Witness vars: {}", cs.num_witness_variables());
        println!("Instance vars: {}", cs.num_instance_variables());
        let constraints_per_element = cs.num_constraints() as f64 / len as f64;
        let bits_per_elem = <P::ScalarField as PrimeField>::size_in_bits() as f64;
        println!("Elements: {}, Constraints per element: {}", len, constraints_per_element);
        println!("Elements: {}, Constraints per bit: {}", len, constraints_per_element / bits_per_elem);
    }

    #[test]
    fn jubjub() {
        msm_test::<ark_ed_on_bls12_381::EdwardsParameters>(1);
        msm_test::<ark_ed_on_bls12_381::EdwardsParameters>(10);
        msm_test::<ark_ed_on_bls12_381::EdwardsParameters>(100);
        msm_test::<ark_ed_on_bls12_381::EdwardsParameters>(1000);
        msm_test::<ark_ed_on_bls12_381::EdwardsParameters>(5000);
    }
}
