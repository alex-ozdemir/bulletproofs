//! R1CS relations for BP recursions
use super::msm::{known_point_msm, known_scalar_msm};
use super::{IpaInstance, IpaWitness};
use ark_ec::models::twisted_edwards_extended::{GroupAffine, GroupProjective};
use ark_ec::models::TEModelParameters;
use ark_ff::prelude::*;
use ark_nonnative_field::{
    AllocatedNonNativeFieldVar, NonNativeFieldMulResultVar, NonNativeFieldVar,
};
use ark_r1cs_std::bits::ToBitsGadget;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::groups::curves::twisted_edwards::AffineVar;
use ark_r1cs_std::{alloc::AllocationMode, eq::EqGadget};
use ark_relations::{
    ns,
    r1cs::{self, ConstraintSynthesizer, ConstraintSystemRef},
};
use ark_std::{end_timer, start_timer};

pub mod ip;

macro_rules! timed {
    ($label:expr, $val:expr) => {{
        let timer = start_timer!($label);
        let val = $val;
        end_timer!(timer);
        val
    }};
}

/// The relation:
///
/// p + <s, t> = <a, gen_a> + <b, gen_b> + <a,b> * q AND c = commit(t)
///
/// where
///
/// * (t, a, b) are the witness
/// * (p, s, gen_a, gen_b, q, c) are the instance
pub struct BpRecRelation<P: TEModelParameters> {
    k: usize,
    m: usize,
    p: GroupProjective<P>,
    /// Size k
    t: Option<Vec<GroupAffine<P>>>,
    /// Size k
    s: Vec<P::ScalarField>,
    /// Size m
    a: Option<Vec<P::ScalarField>>,
    /// Size m
    b: Option<Vec<P::ScalarField>>,
    /// Size m
    gen_a: Vec<GroupProjective<P>>,
    /// Size m
    gen_b: Vec<GroupProjective<P>>,
    q: GroupProjective<P>,
    //c: GroupProjective<P>,
}

impl<P: TEModelParameters> BpRecRelation<P> {
    pub fn from_ipa_witness(instance: IpaInstance<GroupProjective<P>>, witness: IpaWitness<P::ScalarField>) -> Self {
        BpRecRelation {
            k: 0,
            m: instance.gens.vec_size,
            p: instance.result,
            t: Some(Vec::new()),
            s: Vec::new(),
            a: Some(witness.a),
            b: Some(witness.b),
            gen_a: instance.gens.a_gens,
            gen_b: instance.gens.b_gens,
            q: instance.gens.ip_gen,
        }
    }
}

impl<P: TEModelParameters> BpRecRelation<P> {
    fn check_sizes(&self) {
        assert_eq!(self.k, self.s.len());
        assert_eq!(self.m, self.gen_a.len());
        assert_eq!(self.m, self.gen_b.len());
        self.a.as_ref().map(|a| assert_eq!(self.m, a.len()));
        self.b.as_ref().map(|b| assert_eq!(self.m, b.len()));
        self.t.as_ref().map(|t| assert_eq!(self.k, t.len()));
    }
}

impl<P: TEModelParameters> ConstraintSynthesizer<P::BaseField> for BpRecRelation<P>
where
    P::BaseField: PrimeField,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<P::BaseField>) -> r1cs::Result<()> {
        self.check_sizes();
        let alloc_timer = start_timer!(|| "allocations");
        let t: Vec<AffineVar<P, FpVar<P::BaseField>>> = (0..self.k)
            .map(|i| {
                // TODO: check?
                AffineVar::new_variable_omit_on_curve_check(
                    ns!(cs, "t alloc"),
                    || Ok(self.t.as_ref().unwrap()[i].clone()),
                    AllocationMode::Witness,
                )
            })
            .collect::<Result<_, _>>()?;
        let (a, a_bits): (
            Vec<NonNativeFieldVar<P::ScalarField, P::BaseField>>,
            Vec<Vec<Boolean<P::BaseField>>>,
        ) = (0..self.m)
            .map(|i| {
                let (f, bits) = AllocatedNonNativeFieldVar::new_variable_alloc_le_bits(
                    ns!(cs, "a"),
                    || Ok(self.a.as_ref().unwrap()[i].clone()),
                    AllocationMode::Witness,
                )
                .unwrap();
                (f.into(), bits)
            })
            .unzip();
        let (b, b_bits): (
            Vec<NonNativeFieldVar<P::ScalarField, P::BaseField>>,
            Vec<Vec<Boolean<P::BaseField>>>,
        ) = (0..self.m)
            .map(|i| {
                let (f, bits) = AllocatedNonNativeFieldVar::new_variable_alloc_le_bits(
                    ns!(cs, "b"),
                    || Ok(self.b.as_ref().unwrap()[i].clone()),
                    AllocationMode::Witness,
                )
                .unwrap();
                (f.into(), bits)
            })
            .unzip();
        end_timer!(alloc_timer);

        // compute <a, b>
        let ip_bits = timed!(|| "gen ip", {
            let ip: NonNativeFieldVar<P::ScalarField, P::BaseField> = a
                .into_iter()
                .zip(b)
                .try_fold(
                    NonNativeFieldMulResultVar::Constant(P::ScalarField::from(0u32)),
                    |acc, (a, b)| {
                        let prod = a.mul_without_reduce(&b)?;
                        Ok(&prod + &acc)
                    },
                )?
                .reduce()?;
            ip.to_bits_le().unwrap()
        });

        // compute <a, gen_a> + <b, gen_b> + ip * q
        let commit = timed!(|| "gen commit", {
            let mut scalars: Vec<Vec<Boolean<P::BaseField>>> = Vec::new();
            let mut points: Vec<GroupProjective<P>> = Vec::new();
            scalars.extend(a_bits);
            points.extend_from_slice(&self.gen_a);
            scalars.extend(b_bits);
            points.extend_from_slice(&self.gen_b);
            scalars.push(ip_bits);
            points.push(self.q.clone());
            known_point_msm(scalars, &points)
        });

        // compute p + <s, t>
        let lhs = timed!(|| "gen lhs", {
            let st = known_scalar_msm(self.s.clone(), t);
            st + self.p
        });
        commit.enforce_equal(&lhs).unwrap();

        // TODO: check commitment to t OR integrate with an R1CS compiler that does so
        // automatically.
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use ark_ec::ModelParameters;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_relations::r1cs::{ConstraintLayer, OptimizationGoal, TracingMode};
    use tracing_subscriber::layer::SubscriberExt;

    fn bp_rec_test_k0<P: TEModelParameters>(m: usize)
    where
        P::BaseField: PrimeField,
    {
        let rng = &mut ark_std::test_rng();
        let (instance, witness) = IpaInstance::<GroupProjective<P>>::sample_from_length(rng, m);
        let rec_relation = BpRecRelation::from_ipa_witness(instance, witness);
        let mut layer = ConstraintLayer::default();
        layer.mode = TracingMode::OnlyConstraints;
        let subscriber = tracing_subscriber::Registry::default().with(layer);
        let _guard = tracing::subscriber::set_default(subscriber);
        let cs: ConstraintSystemRef<P::BaseField> = ConstraintSystem::new_ref();
        cs.set_optimization_goal(OptimizationGoal::Constraints);
        rec_relation.generate_constraints(cs.clone()).unwrap();
        cs.finalize();
        //for c in cs.constraint_names().unwrap() {
        //    println!("  {}", c);
        //}
        println!("Constraints: {}", cs.num_constraints());
        println!("Witness vars: {}", cs.num_witness_variables());
        println!("Instance vars: {}", cs.num_instance_variables());
        let constraints_per_m = cs.num_constraints() as f64 / m as f64;
        println!("m: {}, Constraints per m: {}", m, constraints_per_m,);
        assert!(cs.is_satisfied().unwrap());
        println!("Checked");
    }

    #[test]
    fn jubjub() {
        println!("Base bits: {}", <<ark_ed_on_bls12_381::EdwardsParameters as ModelParameters>::BaseField as PrimeField>::size_in_bits());
        println!("Scalar bits: {}", <<ark_ed_on_bls12_381::EdwardsParameters as ModelParameters>::ScalarField as PrimeField>::size_in_bits());
        bp_rec_test_k0::<ark_ed_on_bls12_381::EdwardsParameters>(1);
        bp_rec_test_k0::<ark_ed_on_bls12_381::EdwardsParameters>(2);
        bp_rec_test_k0::<ark_ed_on_bls12_381::EdwardsParameters>(3);
        bp_rec_test_k0::<ark_ed_on_bls12_381::EdwardsParameters>(4);
        //bp_rec_test_k0::<ark_ed_on_bls12_381::EdwardsParameters>(10);
        //bp_rec_test_k0::<ark_ed_on_bls12_381::EdwardsParameters>(100);
        //msm_test::<ark_ed_on_bls12_381::EdwardsParameters>(1000);
        //msm_test::<ark_ed_on_bls12_381::EdwardsParameters>(5000);
    }
}
