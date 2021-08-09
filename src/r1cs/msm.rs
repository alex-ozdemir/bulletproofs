use vector_addition_chain::bos_coster_fast::build_chain;

use ark_ec::group::Group;
use ark_ec::models::twisted_edwards_extended::{GroupAffine, GroupProjective};
use ark_ec::models::TEModelParameters;
use ark_ec::ProjectiveCurve;
use ark_ff::prelude::*;

use ark_r1cs_std::{
    boolean::Boolean, groups::curves::twisted_edwards::AffineVar, groups::CurveVar,
};

use ark_relations::{
    ns,
    r1cs::{self, ConstraintSynthesizer, ConstraintSystemRef},
};

macro_rules! timed {
    ($label:expr, $val:expr) => {{
        let timer = start_timer!($label);
        let val = $val;
        end_timer!(timer);
        val
    }};
}

use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::{alloc::AllocationMode, eq::EqGadget};
use ark_std::{end_timer, start_timer};

use crate::curves::IncompleteOpsGadget;

pub fn known_scalar_msm_twe<P: TEModelParameters>(
    scalars: Vec<P::ScalarField>,
    mut points: Vec<AffineVar<P, FpVar<P::BaseField>>>,
) -> AffineVar<P, FpVar<P::BaseField>>
where
    P::BaseField: PrimeField,
{
    let t = start_timer!(|| "msm");
    // special-case zero
    let r = if points.len() == 0 {
        let zero = GroupAffine::<P>::zero();
        AffineVar::new(FpVar::Constant(zero.x), FpVar::Constant(zero.y))
    } else {
        let chain = timed!(|| "build_chain", build_chain(scalars.clone()));
        // ~quadratic time..
        //timed!(|| "check chain", check_chain(&chain, &scalars));
        //println!(
        //    "Additions per element: {}",
        //    chain.adds.len() as f64 / scalars.len() as f64
        //);
        timed!(|| "embed chain", {
            for (a, b) in &chain.adds {
                let new = points[*a].clone() + points[*b].clone();
                points.push(new);
            }
        });
        points.pop().unwrap()
    };
    end_timer!(t);
    r
}

pub fn known_scalar_msm<
    F: Field,
    G: ProjectiveCurve,
    GVar: CurveVar<G, F>,
    I: IncompleteOpsGadget<F, G, GVar>,
>(
    scalars: Vec<G::ScalarField>,
    mut points: Vec<GVar>,
) -> GVar {
    let t = start_timer!(|| "msm");
    // special-case zero
    let r = if points.len() == 0 {
        GVar::zero()
    } else {
        let chain = timed!(|| "build_chain", build_chain(scalars.clone()));
        // ~quadratic time..
        //timed!(|| "check chain", check_chain(&chain, &scalars));
        //println!(
        //    "Additions per element: {}",
        //    chain.adds.len() as f64 / scalars.len() as f64
        //);
        timed!(|| "embed chain", {
            for (a, b) in &chain.adds {
                let new = if a == b {
                    // double
                    <I as IncompleteOpsGadget<F, G, GVar>>::double(&points[*a])
                } else {
                    // add
                    <I as IncompleteOpsGadget<F, G, GVar>>::add(&points[*a], &points[*b])
                };
                points.push(new);
            }
        });
        points.pop().unwrap()
    };
    end_timer!(t);
    r
}

pub struct KnownScalarMsm<P: TEModelParameters> {
    pub scalars: Vec<P::ScalarField>,
    pub points: Option<Vec<GroupAffine<P>>>,
    pub result: Option<GroupAffine<P>>,
}

impl<P: TEModelParameters> ConstraintSynthesizer<P::BaseField> for KnownScalarMsm<P>
where
    P::BaseField: PrimeField,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<P::BaseField>) -> r1cs::Result<()> {
        let pts = (0..self.scalars.len())
            .map(|i| {
                let v = AffineVar::new_variable_omit_on_curve_check(
                    ns!(cs, "point"),
                    || Ok(self.points.as_ref().unwrap()[i]),
                    AllocationMode::Witness,
                )?;
                Ok(v)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let result = known_scalar_msm_twe(self.scalars.clone(), pts);
        let ex_result = AffineVar::new_variable_omit_on_curve_check(
            ns!(cs, "point2"),
            || Ok(self.result.as_ref().unwrap().clone()),
            AllocationMode::Input,
        )?;
        result.enforce_equal(&ex_result)?;
        Ok(())
    }
}

pub fn known_point_msm_twe<P: TEModelParameters>(
    scalar_bits: Vec<Vec<Boolean<P::BaseField>>>,
    points: &[GroupProjective<P>],
) -> AffineVar<P, FpVar<P::BaseField>>
where
    P::BaseField: PrimeField,
{
    let t = start_timer!(|| "pb_msm");
    let point_powers = timed!(|| "point powers", compute_point_powers(points));
    let r = <AffineVar<P, FpVar<P::BaseField>> as CurveVar<
            GroupProjective<P>,
            P::BaseField,
        >>::precomputed_base_multiscalar_mul_le(
            &point_powers, scalar_bits.iter()
        ).unwrap();
    end_timer!(t);
    r
}

pub fn known_point_msm<G: ProjectiveCurve, GVar: CurveVar<G, G::BaseField>>(
    scalar_bits: Vec<Vec<Boolean<G::BaseField>>>,
    points: &[G],
) -> GVar {
    let t = start_timer!(|| "pb_msm");
    let point_powers = timed!(|| "point powers", compute_point_powers(points));
    let r = GVar::precomputed_base_multiscalar_mul_le(&point_powers, scalar_bits.iter()).unwrap();
    end_timer!(t);
    r
}

fn compute_point_powers<G: Group>(points: &[G]) -> Vec<Vec<G>> {
    let scalar_bits = <G::ScalarField as PrimeField>::size_in_bits();
    points
        .iter()
        .map(|p| {
            let mut acc = *p;
            (0..scalar_bits)
                .map(|_| {
                    let r = acc;
                    acc.double_in_place();
                    r
                })
                .collect()
        })
        .collect()
}

#[cfg(test)]
mod test {
    use super::*;
    use ark_ec::ModelParameters;
    use ark_nonnative_field::{AllocatedNonNativeFieldVar, NonNativeFieldVar};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_relations::r1cs::{ConstraintLayer, OptimizationGoal, TracingMode};
    use tracing_subscriber::layer::SubscriberExt;

    fn fs_msm_test<P: TEModelParameters>(len: usize)
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
        let scalar_ints: Vec<<P::ScalarField as PrimeField>::BigInt> =
            scalars.iter().map(|s| s.into_repr()).collect();
        let result: GroupAffine<P> =
            ark_ec::msm::VariableBaseMSM::multi_scalar_mul(&pts, &scalar_ints).into();
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
        println!(
            "Elements: {}, Constraints per element: {}",
            len, constraints_per_element
        );
        println!(
            "Elements: {}, Constraints per bit: {}",
            len,
            constraints_per_element / bits_per_elem
        );
    }

    #[test]
    fn fs_jubjub() {
        fs_msm_test::<ark_ed_on_bls12_381::EdwardsParameters>(1);
        fs_msm_test::<ark_ed_on_bls12_381::EdwardsParameters>(10);
        fs_msm_test::<ark_ed_on_bls12_381::EdwardsParameters>(100);
        //fs_msm_test::<ark_ed_on_bls12_381::EdwardsParameters>(1000);
        //fs_msm_test::<ark_ed_on_bls12_381::EdwardsParameters>(5000);
    }

    fn fb_msm_test<P: TEModelParameters>(m: usize) -> usize
    where
        P::BaseField: PrimeField,
    {
        let rng = &mut ark_std::test_rng();
        let cs: ConstraintSystemRef<P::BaseField> = ConstraintSystem::new_ref();
        let points: Vec<_> = (0..m).map(|_| GroupProjective::<P>::rand(rng)).collect();
        let scalars: Vec<_> = (0..m).map(|_| P::ScalarField::rand(rng)).collect();
        let (_scalar_vars, scalar_bits): (
            Vec<NonNativeFieldVar<P::ScalarField, P::BaseField>>,
            Vec<Vec<Boolean<P::BaseField>>>,
        ) = (0..m)
            .map(|i| {
                let (f, bits) = AllocatedNonNativeFieldVar::new_variable_alloc_le_bits(
                    ns!(cs, "a"),
                    || Ok(scalars[i].clone()),
                    AllocationMode::Witness,
                )
                .unwrap();
                (f.into(), bits)
            })
            .unzip();
        let cs_before = cs.num_constraints();
        let _msm = known_point_msm_twe(scalar_bits, &points);
        assert!(cs.is_satisfied().unwrap());
        cs.num_constraints() - cs_before
    }

    fn fit_linear<P: TEModelParameters, F: FnMut(usize) -> usize>(mut f: F)
    where
        P::BaseField: PrimeField,
    {
        println!(
            "Base bits: {}",
            <<P as ModelParameters>::BaseField as PrimeField>::size_in_bits()
        );
        let scalar_bits = <<P as ModelParameters>::ScalarField as PrimeField>::size_in_bits();
        println!("Scalar bits: {}", scalar_bits);
        let x1 = 1;
        let x2 = 10;
        let x3 = 20;
        let mut compute = |x1: usize| {
            let y1 = f(x1);
            println!("  {}: {}", x1, y1);
            y1
        };
        let estimate = |x1: usize, x2: usize, y1: usize, y2: usize| {
            let m = (y2 - y1) as f64 / (x2 - x1) as f64;
            let b = y1 as f64 - m * x1 as f64;
            println!("  rate {} constant {}", m, b);
        };
        println!("Costs:");
        let y1 = compute(x1);
        let y2 = compute(x2);
        let y3 = compute(x3);
        println!("Models:");
        estimate(x1, x2, y1, y2);
        estimate(x2, x3, y2, y3);
        let mut compute = |x1: usize| {
            let y1 = f(x1) as f64 / scalar_bits as f64;
            println!("  {}: {}", x1, y1);
            y1
        };
        let estimate = |x1: usize, x2: usize, y1: f64, y2: f64| {
            let m = (y2 - y1) as f64 / (x2 - x1) as f64;
            let b = y1 as f64 - m * x1 as f64;
            println!("  rate {} constant {}", m, b);
        };
        println!("Costs:");
        let y1 = compute(x1);
        let y2 = compute(x2);
        let y3 = compute(x3);
        println!("Models:");
        estimate(x1, x2, y1, y2);
        estimate(x2, x3, y2, y3);
    }
    #[test]
    fn pb_msm_jubjub() {
        fit_linear::<ark_ed_on_bls12_381::EdwardsParameters, _>(
            fb_msm_test::<ark_ed_on_bls12_381::EdwardsParameters>,
        );
    }
}
