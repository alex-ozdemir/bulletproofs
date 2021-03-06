//! R1CS relations for BP recursions
use crate::{
    curves::{IncompleteOpsGadget, Pair},
    relations::{
        bp_unroll::{UnrolledBpInstance, UnrolledBpWitness},
        ipa::{IpaInstance, IpaWitness},
    },
    timed,
    util::powers,
};
use ark_ec::group::Group;
use ark_ff::prelude::*;
use ark_r1cs_std::{
    bits::ToBitsGadget,
    boolean::Boolean,
    fields::nonnative::{
        AllocatedNonNativeFieldVar, NonNativeFieldMulResultVar, NonNativeFieldVar,
    },
    Assignment,
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
use std::marker::PhantomData;

pub mod ip;
pub mod msm;
use msm::{incomplete_known_point_msm, known_scalar_msm};

/// The relation:
///
///    p + <s, t> + randomizer
///      = <a, gen_a> + <b, gen_b> + <a,b> * q + randomizer
///    AND c = commit(t)
///
/// where
///
/// * (t, a, b) are the witness
/// * (p, s, gen_a, gen_b, q, c) are the instance
///
/// Some other machinery will check
///
/// c = commit(t)
pub struct BpRecCircuit<C: Pair> {
    k: usize,
    m: usize,
    p: C::G1,
    /// Size k
    t: Option<Vec<C::G1>>,
    /// Size k
    s: Vec<C::TopField>,
    /// Size m
    a: Option<Vec<C::TopField>>,
    /// Size m
    b: Option<Vec<C::TopField>>,
    /// Size m
    gen_a: Vec<C::G1>,
    /// Size m
    gen_b: Vec<C::G1>,
    q: C::G1,
    /// The randomizer to add to both sides
    randomizer: C::G1,
    _phants: PhantomData<C>,
}

impl<C: Pair> BpRecCircuit<C> {
    pub fn from_ipa_witness<R: Rng>(
        instance: IpaInstance<C::G1>,
        witness: IpaWitness<C::TopField>,
        rng: &mut R,
    ) -> Self {
        let randomizer = C::G1::rand(rng);
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
            randomizer,
            _phants: Default::default(),
        }
    }
    pub fn from_unrolled_bp_witness<R: Rng>(
        instance: UnrolledBpInstance<C>,
        witness: UnrolledBpWitness<C::G1>,
        rng: &mut R,
    ) -> Self {
        // FS-MSM order: concat(rounds, concat(pos_terms) || concat(neg_terms))
        let t: Vec<C::G1> = witness
            .cross_terms
            .iter()
            .flat_map(|cross| cross.pos.iter().chain(&cross.neg).cloned())
            .collect();
        let s: Vec<C::TopField> = instance
            .challs
            .iter()
            .flat_map(|x| {
                powers(*x, 1..instance.k)
                    .into_iter()
                    .chain(powers(x.inverse().unwrap(), 1..instance.k))
            })
            .collect();
        let k = (instance.k - 1) * instance.r * 2;
        let randomizer = C::G1::rand(rng);
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
            randomizer,
            _phants: Default::default(),
        }
    }
    pub fn from_unrolled_bp_instance<R: Rng>(instance: UnrolledBpInstance<C>, rng: &mut R) -> Self {
        let s: Vec<C::TopField> = instance
            .challs
            .iter()
            .flat_map(|x| {
                powers(*x, 1..instance.k)
                    .into_iter()
                    .chain(powers(x.inverse().unwrap(), 1..instance.k))
            })
            .collect();
        let k = (instance.k - 1) * instance.r * 2;
        assert_eq!(k, s.len());
        let randomizer = C::G1::rand(rng);
        BpRecCircuit {
            k,
            m: instance.gens.vec_size,
            p: instance.result,
            t: None,
            s,
            a: None,
            b: None,
            gen_a: instance.gens.a_gens,
            gen_b: instance.gens.b_gens,
            q: instance.gens.ip_gen,
            randomizer,
            _phants: Default::default(),
        }
    }
    pub fn sized_instance<R: Rng>(k: usize, m: usize, rng: &mut R) -> Self {
        let s: Vec<_> = (0..k).map(|_| C::TopField::rand(rng)).collect();
        let gen_a: Vec<_> = (0..m).map(|_| C::G1::rand(rng)).collect();
        // insecure
        let gen_b = gen_a.clone();
        let zero = C::G1::rand(rng);
        let a: Vec<_> = vec![C::TopField::zero(); m];
        let b = a.clone();
        let zeros = vec![zero.into(); k];
        let randomizer = C::G1::rand(rng);
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
            randomizer,
            _phants: Default::default(),
        }
    }
    pub fn rhs(&self) -> Option<C::G1> {
        let gens = self
            .gen_a
            .iter()
            .chain(self.gen_b.iter())
            .chain(vec![&self.q])
            .cloned()
            .collect::<Vec<_>>();
        let ip = crate::util::ip(self.a.as_ref()?, self.b.as_ref()?);
        let scalars = self
            .a
            .as_ref()?
            .iter()
            .chain(self.b.as_ref()?.iter())
            .chain([ip].iter())
            .cloned()
            .collect::<Vec<_>>();
        Some(crate::util::msm(&gens, &scalars) + self.randomizer)
    }
    pub fn lhs(&self) -> Option<C::G1> {
        Some(self.p.clone() + crate::util::msm(self.t.as_ref()?, &self.s) + self.randomizer)
    }
    pub fn check(&self) {
        self.lhs().map(|l| {
            self.rhs().map(|r| {
                assert_eq!(l, r);
            })
        });
    }
}

impl<C: Pair> BpRecCircuit<C> {
    fn check_sizes(&self) {
        assert_eq!(self.k, self.s.len());
        assert_eq!(self.m, self.gen_a.len());
        assert_eq!(self.m, self.gen_b.len());
        self.a.as_ref().map(|a| assert_eq!(self.m, a.len()));
        self.b.as_ref().map(|b| assert_eq!(self.m, b.len()));
        self.t.as_ref().map(|t| assert_eq!(self.k, t.len()));
    }
}

impl<C: Pair> ConstraintSynthesizer<C::LinkField> for BpRecCircuit<C> {
    fn generate_constraints(self, cs: ConstraintSystemRef<C::LinkField>) -> r1cs::Result<()> {
        let timer = start_timer!(|| "synthesis");
        self.check_sizes();
        let alloc_timer = start_timer!(|| "allocations");
        let t: Vec<C::G1Var> = (0..self.k)
            .map(|i| {
                C::G1IncompleteOps::new_variable(
                    ns!(cs, "t alloc"),
                    || self.t.as_ref().map(|a| a[i].clone()).get(),
                    AllocationMode::Witness,
                )
            })
            .collect::<Result<_, _>>()?;
        for ti in &t {
            C::G1IncompleteOps::enforce_on_curve(ti)?;
        }
        let (a, a_bits): (
            Vec<NonNativeFieldVar<C::TopField, C::LinkField>>,
            Vec<Vec<Boolean<C::LinkField>>>,
        ) = (0..self.m)
            .map(|i| {
                let (f, bits) =
                    AllocatedNonNativeFieldVar::new_witness_with_le_bits(ns!(cs, "a"), || {
                        self.a.as_ref().map(|a| a[i].clone()).get()
                    })
                    .unwrap();
                (f.into(), bits)
            })
            .unzip();
        let (b, b_bits): (
            Vec<NonNativeFieldVar<C::TopField, C::LinkField>>,
            Vec<Vec<Boolean<C::LinkField>>>,
        ) = (0..self.m)
            .map(|i| {
                let (f, bits) =
                    AllocatedNonNativeFieldVar::new_witness_with_le_bits(ns!(cs, "b"), || {
                        self.b.as_ref().map(|b| b[i].clone()).get()
                    })
                    .unwrap();
                (f.into(), bits)
            })
            .unzip();
        end_timer!(alloc_timer);

        // compute <a, b>
        let ip_bits = timed!(|| "gen ip", {
            let ip: NonNativeFieldVar<C::TopField, C::LinkField> = a
                .into_iter()
                .zip(b)
                .try_fold(
                    NonNativeFieldMulResultVar::Constant(C::TopField::from(0u32)),
                    |acc, (a, b)| {
                        let prod = a.mul_without_reduce(&b)?;
                        Ok(&prod + &acc)
                    },
                )?
                .reduce()?;
            ip.to_bits_le().unwrap()
        });

        // compute <a, gen_a> + <b, gen_b> + ip * q
        let commit: C::G1Var = timed!(|| "gen commit", {
            let mut scalars: Vec<Vec<Boolean<C::LinkField>>> = Vec::new();
            let mut points: Vec<C::G1> = Vec::new();
            scalars.extend(a_bits);
            points.extend_from_slice(&self.gen_a);
            scalars.extend(b_bits);
            points.extend_from_slice(&self.gen_b);
            scalars.push(ip_bits);
            points.push(self.q.clone());
            let acc_val: C::G1 = self.randomizer.clone();
            incomplete_known_point_msm::<_, _, _, C::G1IncompleteOps>(
                ns!(cs, "msm"),
                &acc_val,
                scalars,
                &points,
            )
        });

        // compute p + <s, t>
        let lhs = timed!(|| "gen lhs", {
            let p = C::G1IncompleteOps::alloc_constant(
                ns!(cs, "p+rand"),
                &(self.p.clone() + &self.randomizer),
            )
            .unwrap();
            known_scalar_msm::<C::LinkField, C::G1, C::G1Var, C::G1IncompleteOps>(
                p,
                self.s.clone(),
                t,
            )
        });
        commit.enforce_equal(&lhs).unwrap();
        end_timer!(timer);

        // TODO: check commitment to t OR integrate with an R1CS compiler that does so
        // automatically.
        Ok(())
    }
}

pub fn measure_constraints<C: Pair, R: Rng>(k: usize, m: usize, rng: &mut R) -> usize {
    let circ = BpRecCircuit::<C>::sized_instance(k, m, rng);
    let cs: ConstraintSystemRef<<C::G2 as Group>::ScalarField> = ConstraintSystem::new_ref();
    cs.set_optimization_goal(OptimizationGoal::Constraints);
    cs.set_mode(SynthesisMode::Setup);
    circ.generate_constraints(cs.clone()).unwrap();
    cs.num_constraints()
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        curves::models::{JubJubPair, PastaPair, VellasPair},
        reductions::ipa_to_bp_unroll::IpaToBpUnroll,
        relations::ipa::IpaRelation,
        Reduction, Relation,
    };
    use ark_ec::ModelParameters;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_relations::r1cs::{ConstraintLayer, OptimizationGoal, TracingMode};
    use rand::Rng;
    use tracing_subscriber::layer::SubscriberExt;

    fn ipa_check<C: Pair>(m: usize) {
        let rng = &mut ark_std::test_rng();
        let (instance, witness) = IpaInstance::<C::G1>::sample_from_length(rng, m);
        IpaRelation::check(&instance, &witness);
        let rec_relation = BpRecCircuit::<C>::from_ipa_witness(instance, witness, rng);
        rec_relation.check();
        let mut layer = ConstraintLayer::default();
        layer.mode = TracingMode::OnlyConstraints;
        let subscriber = tracing_subscriber::Registry::default().with(layer);
        let _guard = tracing::subscriber::set_default(subscriber);
        let cs: ConstraintSystemRef<C::LinkField> = ConstraintSystem::new_ref();
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
        ipa_check::<JubJubPair>(1);
        ipa_check::<JubJubPair>(2);
        ipa_check::<JubJubPair>(3);
        ipa_check::<JubJubPair>(4);
    }

    #[test]
    fn pasta_ipa_test() {
        ipa_check::<PastaPair>(1);
        ipa_check::<PastaPair>(2);
        ipa_check::<PastaPair>(3);
        ipa_check::<PastaPair>(4);
    }

    #[test]
    fn vellas_ipa_test() {
        ipa_check::<VellasPair>(1);
        ipa_check::<VellasPair>(2);
        ipa_check::<VellasPair>(3);
        ipa_check::<VellasPair>(4);
    }

    fn unroll_check<C: Pair>(init_size: usize, k: usize, r: usize) {
        println!(
            "doing a unrolled circuit check with {} elems, k: {}, r: {}",
            init_size, k, r
        );
        let rng = &mut ark_std::test_rng();
        let fs_seed: [u8; 32] = rng.gen();
        let mut fs_rng = crate::FiatShamirRng::from_seed(&fs_seed);
        let (instance, witness) = IpaInstance::<C::G1>::sample_from_length(rng, init_size);
        let reducer = IpaToBpUnroll::<C>::new(k, r);
        let pp = reducer.setup(&init_size, rng);
        let (_proof, u_instance, u_witness) = reducer.prove(&pp, &instance, &witness, &mut fs_rng);
        let rec_relation = BpRecCircuit::from_unrolled_bp_witness(u_instance, u_witness, rng);
        println!(
            "R1CS FB-MSM size: {}, IP & commit size: {}",
            rec_relation.k, rec_relation.m
        );
        let mut layer = ConstraintLayer::default();
        layer.mode = TracingMode::OnlyConstraints;
        let subscriber = tracing_subscriber::Registry::default().with(layer);
        let _guard = tracing::subscriber::set_default(subscriber);
        let cs: ConstraintSystemRef<C::LinkField> = ConstraintSystem::new_ref();
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
        unroll_check::<JubJubPair>(4, 2, 1);
        unroll_check::<JubJubPair>(8, 2, 2);
        unroll_check::<JubJubPair>(8, 2, 3);
        unroll_check::<JubJubPair>(9, 3, 1);
        unroll_check::<JubJubPair>(9, 3, 2);
        unroll_check::<JubJubPair>(2048, 4, 4);
        unroll_check::<JubJubPair>(2048, 4, 5);
    }

    #[test]
    fn pasta_unroll() {
        unroll_check::<PastaPair>(4, 2, 1);
        unroll_check::<PastaPair>(8, 2, 2);
        unroll_check::<PastaPair>(8, 2, 3);
        unroll_check::<PastaPair>(9, 3, 1);
        unroll_check::<PastaPair>(9, 3, 2);
    }

    #[test]
    fn vellas_unroll() {
        unroll_check::<VellasPair>(4, 2, 1);
        unroll_check::<VellasPair>(8, 2, 2);
        unroll_check::<VellasPair>(8, 2, 3);
        unroll_check::<VellasPair>(9, 3, 1);
        unroll_check::<VellasPair>(9, 3, 2);
    }
}
