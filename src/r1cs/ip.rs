//! R1CS non-native IP gadget
#![allow(dead_code, unused_imports)]
use super::msm::known_scalar_msm_twe;
use ark_ec::models::twisted_edwards_extended::GroupAffine;
use ark_ec::models::TEModelParameters;
use ark_ec::AffineCurve;
use ark_ff::prelude::*;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::groups::curves::twisted_edwards::AffineVar;
use ark_r1cs_std::Assignment;
use ark_r1cs_std::R1CSVar;
use ark_r1cs_std::alloc::AllocationMode;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::nonnative::{
    AllocatedNonNativeFieldVar, NonNativeFieldMulResultVar, NonNativeFieldVar,
};
use ark_relations::{
    lc, ns,
    r1cs::{
        self, ConstraintSynthesizer, ConstraintSystemRef, LinearCombination, Namespace,
        SynthesisError,
    },
};

pub struct AllocatedIpComputation<F: PrimeField> {
    pub a_bits: Vec<Vec<Boolean<F>>>,
    pub b_bits: Vec<Vec<Boolean<F>>>,
    pub ip_bits: Vec<Boolean<F>>,
}

fn alloc_vec_vec_bits<P: TEModelParameters, IN: Into<Namespace<P::BaseField>>>(
    ns: IN,
    n: usize,
    xs: Option<Vec<P::ScalarField>>,
) -> Vec<Vec<Boolean<P::BaseField>>> {
    let ns = ns.into();
    let cs = ns.cs();
    let scalar_bits = <P::ScalarField as PrimeField>::size_in_bits();
    let bits: Vec<Vec<Boolean<P::BaseField>>> = (0..n)
        .map(|i| {
            let bits: Option<Vec<bool>> = xs.as_ref().map(|a| {
                let mut bits = a[i].into_repr().to_bits_le();
                bits.truncate(scalar_bits);
                bits
            });

            (0..scalar_bits)
                .map(|j| {
                    Boolean::new_witness(ns!(cs, "bit"), || Ok(bits.as_ref().get()?[j])).unwrap()
                })
                .collect()
        })
        .collect();
    // if let Some(xs) = &xs {
    //     for i in 0..n {
    //         println!("val {}", xs[i]);
    //         println!("val {}", xs[i].into_repr());
    //         println!("val {:?}", xs[i].into_repr().to_bits_be());
    //         print!("bit ");
    //         for b in &bits[i] {
    //             print!("{}", if b.value().unwrap() { 1 } else { 0 });
    //         }
    //         println!("");
    //     }
    // }
    bits
}

#[derive(Clone)]
struct Limb<F: PrimeField> {
    lc: LinearCombination<F>,
    val: Option<F>,
    max_val: F,
    cs: ConstraintSystemRef<F>,
}

impl<F: PrimeField> R1CSVar<F> for Limb<F> {
    type Value = F;

    fn cs(&self) -> ConstraintSystemRef<F> {
        self.cs.clone()
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        self.val.ok_or(SynthesisError::AssignmentMissing)
    }
}

impl<F: PrimeField> Limb<F> {
    fn zero(cs: ConstraintSystemRef<F>) -> Self {
        Self {
            lc: lc!(),
            max_val: F::zero(),
            val: Some(F::zero()),
            cs,
        }
    }
    fn alloc_in_range(
        cs: ConstraintSystemRef<F>,
        limb_w: usize,
        val: Option<F>,
    ) -> (Self, Vec<Boolean<F>>) {
        let bitvals: Option<Vec<bool>> = val.map(|v| {
            v.into_repr()
                .to_bits_le()
                .into_iter()
                .take(limb_w)
                .collect()
        });
        let bits: Vec<Boolean<F>> = (0..limb_w)
            .map(|i| Boolean::new_witness(cs.clone(), || Ok(bitvals.as_ref().get()?[i])).unwrap())
            .collect();
        // TODO: don't discard bits?
        (Self::from_bits(&bits), bits)
    }
    fn from_bits(bits: &[Boolean<F>]) -> Self {
        let max_val = {
            let mut t = F::one();
            for _ in 0..bits.len() {
                t.double_in_place();
            }
            t - &F::one()
        };
        let val = bits.iter().rev().try_fold(F::zero(), |mut acc, b| {
            acc.double_in_place();
            Some(if b.value().ok()? { acc + F::one() } else { acc })
        });
        // if let Some(val) = &val {
        //     println!("val {}", val.into_repr());
        //     print!("bit ");
        //     for b in bits {
        //         print!("{}", if b.value().unwrap() { 1 } else { 0 });
        //     }
        //     println!("");
        // }
        Self {
            lc: bits
                .iter()
                .fold((lc!(), F::one()), |(acc, place), b| {
                    (acc + (place, &b.lc()), place.double())
                })
                .0,
            max_val,
            val,
            cs: bits[0].cs(),
        }
    }
    fn mult(&self, other: &Self) -> Self {
        let mut cs = self.cs.borrow_mut().unwrap();
        let val = self
            .val
            .as_ref()
            .and_then(|a| other.val.as_ref().map(|b| *a * b));
        // if let Some(val) = &val {
        //     println!("m val {}", val.into_repr());
        // }
        let product = cs.new_witness_variable(|| val.get()).unwrap();
        let lc = lc!() + product;
        cs.enforce_constraint(self.lc.clone(), other.lc.clone(), lc.clone())
            .unwrap();
        // TODO: check overflow
        let max_val = self.max_val * &other.max_val;
        Self {
            lc,
            val,
            max_val,
            cs: self.cs.clone(),
        }
    }
    fn add(&mut self, other: &Self) {
        self.val.as_mut().map(|sv| {
            other.val.as_ref().map(|ov| {
                *sv += ov;
            })
        });
        self.max_val += &other.max_val;
        self.lc.0.extend_from_slice(&other.lc);
    }
    /// Split this into checked bits based on the max_value
    fn to_bits(&self) -> Vec<Boolean<F>> {
        let n_bits = bits_needed(self.max_val);
        let (big_limb, bits) = Self::alloc_in_range(self.cs.clone(), n_bits, self.val);
        self.cs
            .enforce_constraint(lc!(), lc!(), lc!() + &big_limb.lc - &self.lc)
            .unwrap();
        bits
    }
    /// Return a pair (carry, limb) such that
    /// carry * B + limb = self, and limb is less than 2 ** limb_w
    fn carry(&self, limb_w: usize) -> (Self, Self) {
        let mut bits = self.to_bits();
        let high_bits = bits.split_off(limb_w);
        let low_bits = bits;
        // TODO: Don't lose bits?
        if high_bits.len() == 0 {
            (Self::zero(self.cs.clone()), Self::from_bits(&low_bits))
        } else {
            (Self::from_bits(&high_bits), Self::from_bits(&low_bits))
        }
    }
}

fn bits_needed<F: PrimeField>(f: F) -> usize {
    let mut repr = f.into_repr();
    let mut bits = 0;
    while !repr.is_zero() {
        repr.div2();
        bits += 1;
    }
    bits
}

struct LimbSeq<F: PrimeField> {
    limbs: Vec<Limb<F>>,
    limb_w: usize,
    cs: ConstraintSystemRef<F>,
}

fn ceil_div(n: usize, d: usize) -> usize {
    (n - 1) / d + 1
}

impl<F: PrimeField> LimbSeq<F> {
    fn zero(limb_w: usize, cs: ConstraintSystemRef<F>) -> Self {
        Self {
            limb_w,
            limbs: Vec::new(),
            cs,
        }
    }
    fn from_bits(limb_w: usize, bits: &[Boolean<F>]) -> Self {
        assert!(bits.len() > 0);
        let this = Self {
            limb_w,
            limbs: bits.chunks(limb_w).map(|c| Limb::from_bits(c)).collect(),
            cs: bits[0].cs().clone(),
        };
        assert_eq!(ceil_div(bits.len(), limb_w), this.limbs.len());
        this
    }
    fn add(mut self, other: &Self) -> Self {
        let n_limbs = std::cmp::max(self.limbs.len(), other.limbs.len());
        let cs = self.cs.clone();
        while self.limbs.len() < n_limbs {
            self.limbs.push(Limb::zero(cs.clone()));
        }
        for i in 0..other.limbs.len() {
            self.limbs[i].add(&other.limbs[i]);
        }
        self
    }
    fn mult(&self, other: &Self) -> Self {
        let n_limbs = (self.limbs.len() + other.limbs.len()).saturating_sub(1);
        let cs = self.cs.clone();
        let mut limbs = vec![Limb::zero(cs.clone()); n_limbs];
        for (i, sl) in self.limbs.iter().enumerate() {
            for (j, ol) in other.limbs.iter().enumerate() {
                limbs[i + j].add(&sl.mult(ol));
            }
        }
        Self {
            limb_w: self.limb_w,
            limbs,
            cs: self.cs.clone(),
        }
    }
    fn limb_max(&self) -> F {
        F::from(2u64).pow(&[self.limb_w as u64]) - F::one()
    }
    fn carry(&self) -> Self {
        let mut carry = Limb::zero(self.cs.clone());
        let mut limbs: Vec<Limb<F>> = self
            .limbs
            .iter()
            .map(|l| {
                let mut l = l.clone();
                l.add(&carry);
                let (new_carry, new_l) = l.carry(self.limb_w);
                carry = new_carry;
                new_l
            })
            .collect();
        while carry.max_val >= self.limb_max() {
            let (new_carry, new_l) = carry.carry(self.limb_w);
            limbs.push(new_l);
            carry = new_carry;
        }
        if carry.max_val > F::zero() {
            limbs.push(carry);
        }
        Self {
            limbs,
            limb_w: self.limb_w,
            cs: self.cs.clone(),
        }
    }
    fn reduce<FT: PrimeField>(&self) -> Vec<Boolean<F>> {
        todo!()
    }
}

fn ulog2(n: usize) -> usize {
    std::mem::size_of::<usize>() * 8 - n.leading_zeros() as usize
}

fn limb_width<P: TEModelParameters>(ip_size: usize) -> usize
where
    P::BaseField: PrimeField,
{
    let base_size = <P::BaseField as PrimeField>::size_in_bits();
    let target_size = <P::ScalarField as PrimeField>::size_in_bits();
    let base_cap = base_size - 1;
    let margin = 4 + ulog2(ip_size);
    let space_needed = margin + target_size * 2;
    let limbs = ceil_div(space_needed, base_cap);
    let limb_w = ceil_div(target_size, limbs);
    println!(
        "To fit {} bits in {} with a {}-IP, use {} limbs of size {}",
        target_size, base_size, ip_size, limbs, limb_w
    );
    limb_w
}

pub fn ip_alloc_compute<P: TEModelParameters>(
    cs: ConstraintSystemRef<P::BaseField>,
    n: usize,
    a: Option<Vec<P::ScalarField>>,
    b: Option<Vec<P::ScalarField>>,
) -> AllocatedIpComputation<P::BaseField>
where
    P::BaseField: PrimeField,
{
    let a_bits = alloc_vec_vec_bits::<P, _>(ns!(cs, "a_alloc").cs(), n, a);
    let b_bits = alloc_vec_vec_bits::<P, _>(ns!(cs, "b_alloc").cs(), n, b);
    println!(
        "post-alloc cs/n: {}",
        cs.num_constraints() as f64 / n as f64
    );
    let limb_w = limb_width::<P>(n);
    let a_limbs: Vec<LimbSeq<P::BaseField>> = a_bits
        .iter()
        .map(|b| LimbSeq::from_bits(limb_w, b))
        .collect();
    let b_limbs: Vec<LimbSeq<P::BaseField>> = b_bits
        .iter()
        .map(|b| LimbSeq::from_bits(limb_w, b))
        .collect();
    let ip_limbs: LimbSeq<P::BaseField> = a_limbs
        .iter()
        .zip(&b_limbs)
        .fold(LimbSeq::zero(limb_w, cs.clone()), |acc, (a, b)| {
            acc.add(&a.mult(b))
        });
    println!(
        "pre-reduce cs/n: {}",
        cs.num_constraints() as f64 / n as f64
    );
    let c = cs.num_constraints();
    let _ip_limbs_carried = ip_limbs.carry();
    println!("carry cs: {}", cs.num_constraints() - c);
    //let ip_bits = ip_limbs.reduce::<P::ScalarField>();
    AllocatedIpComputation {
        a_bits,
        b_bits,
        ip_bits: vec![],
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use ark_ec::AffineCurve;
    use ark_ec::ModelParameters;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_relations::r1cs::{ConstraintLayer, OptimizationGoal, TracingMode};
    use tracing_subscriber::layer::SubscriberExt;

    fn msm_test<P: TEModelParameters>(m: usize)
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
        //let pts: Vec<_> = (0..len).map(|_| GroupAffine::<P>::rand(rng)).collect();
        //let pts: Vec<_> = (0..2).map(|_| GroupAffine::<P>::rand(rng)).collect();
        let a: Vec<_> = (0..m).map(|_| P::ScalarField::rand(rng)).collect();
        let b: Vec<_> = (0..m).map(|_| P::ScalarField::rand(rng)).collect();
        //let a: Vec<_> = (0..m).map(|_| P::ScalarField::from(5u64)).collect();
        //let b: Vec<_> = (0..m).map(|_| P::ScalarField::from(5u64)).collect();
        let _r = ip_alloc_compute::<P>(cs.clone(), m, Some(a), Some(b));
        cs.finalize();
        assert!(cs.is_satisfied().unwrap());
        //for c in cs.constraint_names().unwrap() {
        //    println!("  {}", c);
        //}
        println!("Constraints: {}", cs.num_constraints());
        println!("Witness vars: {}", cs.num_witness_variables());
        println!("Instance vars: {}", cs.num_instance_variables());
        let constraints_per_m = cs.num_constraints() as f64 / m as f64;
        println!("m: {}, Constraints per m: {}", m, constraints_per_m,);
    }

    #[test]
    fn jubjub() {
        println!("Base bits: {}", <<ark_ed_on_bls12_381::EdwardsParameters as ModelParameters>::BaseField as PrimeField>::size_in_bits());
        println!("Scalar bits: {}", <<ark_ed_on_bls12_381::EdwardsParameters as ModelParameters>::ScalarField as PrimeField>::size_in_bits());
        msm_test::<ark_ed_on_bls12_381::EdwardsParameters>(10);
        msm_test::<ark_ed_on_bls12_381::EdwardsParameters>(100);
    }
}
