//! R1CS relations for BP recursions
use crate::{
    relations::{
        bp_unroll::{UnrolledBpInstance, UnrolledBpWitness},
        ipa::{IpaInstance, IpaWitness},
    },
    util::powers,
};
use ark_ec::models::{
    twisted_edwards_extended::{GroupAffine, GroupProjective},
    TEModelParameters,
};
use ark_ff::prelude::*;
use ark_nonnative_field::{
    AllocatedNonNativeFieldVar, NonNativeFieldMulResultVar, NonNativeFieldVar,
};
use ark_r1cs_std::{
    bits::ToBitsGadget,
    boolean::Boolean,
    fields::fp::FpVar,
    groups::curves::twisted_edwards::AffineVar,
    {alloc::AllocationMode, eq::EqGadget},
};
use ark_relations::{
    ns,
    r1cs::{
        self, ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, OptimizationGoal,
        SynthesisMode,
    },
};
use ark_std::{end_timer, start_timer};
use rand::Rng;

pub mod ip;
pub mod msm;
use msm::{known_point_msm, known_scalar_msm};

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
///
/// Some other machinery will check
///
/// c = commit(t)
pub struct BpRecCircuit<P: TEModelParameters> {
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
    #[allow(dead_code)]
    /// Commitment(s) TODO
    c: GroupProjective<P>,
}

impl<P: TEModelParameters> BpRecCircuit<P> {
    pub fn from_ipa_witness(
        instance: IpaInstance<GroupProjective<P>>,
        witness: IpaWitness<P::ScalarField>,
    ) -> Self {
        BpRecCircuit {
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
            c: GroupProjective::<P>::zero(),
        }
    }
    pub fn from_unrolled_bp_witness(
        instance: UnrolledBpInstance<GroupProjective<P>>,
        witness: UnrolledBpWitness<P>,
    ) -> Self {
        // FS-MSM order: concat(pos_terms) || concat(neg_terms)
        let t: Vec<GroupAffine<P>> = witness
            .pos_cross_terms
            .into_iter()
            .flatten()
            .chain(witness.neg_cross_terms.into_iter().flatten())
            .map(|p| p.into())
            .collect();
        let s: Vec<P::ScalarField> = instance
            .challs
            .iter()
            .map(|x| powers(*x, 1..instance.k))
            .chain(
                instance
                    .challs
                    .iter()
                    .map(|x| powers(x.inverse().unwrap(), 1..instance.k)),
            )
            .flatten()
            .collect();
        let k = (instance.k - 1) * instance.r * 2;
        assert_eq!(k, t.len());
        assert_eq!(k, s.len());
        BpRecCircuit {
            k,
            m: instance.gens.vec_size,
            p: instance.result,
            t: Some(t),
            s,
            a: Some(witness.a),
            b: Some(witness.b),
            gen_a: instance.gens.a_gens,
            gen_b: instance.gens.b_gens,
            q: instance.gens.ip_gen,
            c: GroupProjective::<P>::zero(),
        }
    }
    pub fn sized_instance<R: Rng>(k: usize, m: usize, rng: &mut R) -> Self {
        let s: Vec<_> = (0..k).map(|_| P::ScalarField::rand(rng)).collect();
        let gen_a: Vec<_> = (0..m).map(|_| GroupProjective::<P>::rand(rng)).collect();
        // insecure
        let gen_b = gen_a.clone();
        let zero = GroupProjective::<P>::zero();
        let a: Vec<_> = vec![P::ScalarField::zero(); m];
        let b = a.clone();
        let zeros = vec![zero.into(); k];
        BpRecCircuit {
            k,
            m,
            p: zero,
            t: Some(zeros),
            s,
            a: Some(a),
            b: Some(b),
            gen_a,
            gen_b,
            q: zero,
            c: zero,
        }
    }
}

impl<P: TEModelParameters> BpRecCircuit<P> {
    fn check_sizes(&self) {
        assert_eq!(self.k, self.s.len());
        assert_eq!(self.m, self.gen_a.len());
        assert_eq!(self.m, self.gen_b.len());
        self.a.as_ref().map(|a| assert_eq!(self.m, a.len()));
        self.b.as_ref().map(|b| assert_eq!(self.m, b.len()));
        self.t.as_ref().map(|t| assert_eq!(self.k, t.len()));
    }
}

impl<P: TEModelParameters> ConstraintSynthesizer<P::BaseField> for BpRecCircuit<P>
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

pub fn measure_constraints<P: TEModelParameters, R: Rng>(k: usize, m: usize, rng: &mut R) -> usize
where
    P::BaseField: PrimeField,
{
    let circ = BpRecCircuit::<P>::sized_instance(k, m, rng);
    let cs: ConstraintSystemRef<P::BaseField> = ConstraintSystem::new_ref();
    cs.set_optimization_goal(OptimizationGoal::Constraints);
    cs.set_mode(SynthesisMode::Setup);
    circ.generate_constraints(cs.clone()).unwrap();
    cs.num_constraints()
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::reductions::ipa_to_bp_unroll::IpaToBpUnroll;
    use crate::Reduction;
    use ark_ec::ModelParameters;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_relations::r1cs::{ConstraintLayer, OptimizationGoal, TracingMode};
    use rand::Rng;
    use tracing_subscriber::layer::SubscriberExt;

    fn ipa_check<P: TEModelParameters>(m: usize)
    where
        P::BaseField: PrimeField,
    {
        let rng = &mut ark_std::test_rng();
        let (instance, witness) = IpaInstance::<GroupProjective<P>>::sample_from_length(rng, m);
        let rec_relation = BpRecCircuit::from_ipa_witness(instance, witness);
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
    fn jubjub_ipa_test() {
        println!("Base bits: {}", <<ark_ed_on_bls12_381::EdwardsParameters as ModelParameters>::BaseField as PrimeField>::size_in_bits());
        println!("Scalar bits: {}", <<ark_ed_on_bls12_381::EdwardsParameters as ModelParameters>::ScalarField as PrimeField>::size_in_bits());
        ipa_check::<ark_ed_on_bls12_381::EdwardsParameters>(1);
        ipa_check::<ark_ed_on_bls12_381::EdwardsParameters>(2);
        ipa_check::<ark_ed_on_bls12_381::EdwardsParameters>(3);
        ipa_check::<ark_ed_on_bls12_381::EdwardsParameters>(4);
    }

    fn unroll_check<P: TEModelParameters>(init_size: usize, k: usize, r: usize)
    where
        P::BaseField: PrimeField,
    {
        println!(
            "doing a unrolled circuit check with {} elems, k: {}, r: {}",
            init_size, k, r
        );
        let rng = &mut ark_std::test_rng();
        let fs_seed: [u8; 32] = rng.gen();
        let mut fs_rng = crate::FiatShamirRng::from_seed(&fs_seed);
        let (instance, witness) =
            IpaInstance::<GroupProjective<P>>::sample_from_length(rng, init_size);
        let reducer = IpaToBpUnroll::new(k, r);
        let (_proof, u_instance, u_witness) =
            reducer.prove(&instance, &witness, &mut fs_rng);
        let rec_relation = BpRecCircuit::from_unrolled_bp_witness(u_instance, u_witness);
        println!(
            "R1CS FB-MSM size: {}, IP & commit size: {}",
            rec_relation.k, rec_relation.m
        );
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
        //let constraints_per_m = cs.num_constraints() as f64 / m as f64;
        //println!("m: {}, Constraints per m: {}", m, constraints_per_m,);
        assert!(cs.is_satisfied().unwrap());
        println!("Checked");
    }

    #[test]
    fn jubjub_unroll_test() {
        println!("Base bits: {}", <<ark_ed_on_bls12_381::EdwardsParameters as ModelParameters>::BaseField as PrimeField>::size_in_bits());
        println!("Scalar bits: {}", <<ark_ed_on_bls12_381::EdwardsParameters as ModelParameters>::ScalarField as PrimeField>::size_in_bits());
        unroll_check::<ark_ed_on_bls12_381::EdwardsParameters>(4, 2, 1);
        unroll_check::<ark_ed_on_bls12_381::EdwardsParameters>(8, 2, 2);
        unroll_check::<ark_ed_on_bls12_381::EdwardsParameters>(8, 2, 3);
        unroll_check::<ark_ed_on_bls12_381::EdwardsParameters>(9, 3, 1);
        unroll_check::<ark_ed_on_bls12_381::EdwardsParameters>(9, 3, 2);
        unroll_check::<ark_ed_on_bls12_381::EdwardsParameters>(2048, 4, 4);
        unroll_check::<ark_ed_on_bls12_381::EdwardsParameters>(2048, 4, 5);
    }
}
