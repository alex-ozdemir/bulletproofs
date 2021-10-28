use ark_ec::{
    group::Group, models::short_weierstrass_jacobian::GroupProjective as SWGroupProjective,
    models::twisted_edwards_extended::GroupProjective as TEGroupProjective, ModelParameters,
    ProjectiveCurve, SWModelParameters, TEModelParameters,
};
use ark_ff::prelude::*;
use ark_r1cs_std::groups::curves::{
    short_weierstrass::non_zero_affine::NonZeroAffineVar as SwNzAffVar,
    twisted_edwards::AffineVar as TEAffineVar,
};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    bits::ToBitsGadget,
    boolean::Boolean,
    eq::EqGadget,
    fields::fp::FpVar,
    groups::CurveVar,
    select::CondSelectGadget,
    R1CSVar,
};
use ark_relations::r1cs::{Namespace, SynthesisError};
use derivative::Derivative;
use std::fmt::Debug;
use std::iter::successors;
use std::marker::PhantomData;

use ark_std::{end_timer, start_timer};

use crate::util::CollectIter;

macro_rules! timed {
    ($label:expr, $val:expr) => {{
        let timer = start_timer!($label);
        let val = $val;
        end_timer!(timer);
        val
    }};
}

pub trait TEPair {
    type P1: TEModelParameters;
    type G2: Group<ScalarField = <Self::P1 as ModelParameters>::BaseField>;
}

/// A pair (G1, G2) where the base field of G1 is the scalar field of G2.
///
///
/// We call G1's scalar field the *top field*.
/// We call the common field the *link field*.
///
/// Furthermore, we have:
/// * a known-scalar MSM gadget for G1 points.
/// * a known-point MSM gadget for G1 points.
/// *
pub trait Pair {
    type TopField: PrimeField;
    type LinkField: PrimeField;
    type P1: ModelParameters<BaseField = Self::LinkField>;
    type G1: ProjectiveCurve<ScalarField = Self::TopField, BaseField = Self::LinkField>
        + AffCoords<BaseField = Self::LinkField>;
    type G1Var: EqGadget<Self::LinkField> + Debug + R1CSVar<Self::LinkField>;
    type G1IncompleteOps: IncompleteOpsGadget<Self::LinkField, Self::G1, Self::G1Var>;
    type G2: Group<ScalarField = Self::LinkField>;
    //fn known_point_msm(
    //    scalar_bits: Vec<Vec<Boolean<Self::LinkField>>>,
    //    points: &[Self::G1],
    //) -> Self::G1Var;
    // fn known_scalar_msm(
    //     scalars: Vec<<Self::P1 as ModelParameters>::ScalarField>,
    //     points: &[Self::G1Var],
    // ) -> Self::G1Var;
}

pub trait AffCoords {
    type BaseField: Field;
    fn get_xy(&self) -> (Self::BaseField, Self::BaseField);
}

/// Gadget for an incomplete binary operation.
pub trait IncompleteOpsGadget<F: Field, G: Clone, GVar: Debug> {
    /// Add two points that must
    /// * be non-equal
    /// * be non-zero
    /// * yield a non-zero result
    /// Ensures conditions 1 and 3.
    fn add(a: &GVar, b: &GVar) -> GVar;
    /// Add a point to itself that must
    /// * yield a non-zero result
    fn double(a: &GVar) -> GVar;
    /// Add a constant point to itself
    fn constant_double(a: &G) -> G;
    /// If `b`, then add `x1` to `x0`, o.w., return `x0`.
    fn conditional_constant_add(b: &Boolean<F>, x0: GVar, x1: &G) -> GVar;

    /// From constant
    fn alloc_constant(cs: impl Into<Namespace<F>>, a: &G) -> Result<GVar, SynthesisError>;

    /// for ommiting checks that it is on the curve.
    fn new_variable(
        cs: impl Into<Namespace<F>>,
        //cs: impl Into<Namespace<<G::BaseField as Field>::BasePrimeField>>,
        f: impl FnOnce() -> Result<G, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<GVar, SynthesisError>;

    fn enforce_on_curve(pt: &GVar) -> Result<(), SynthesisError>;

    /// Computes `base_point + scalar_bits * scalar_point`,
    /// where `scalar_bits` is a little-endian (LSB at index 0).
    ///
    /// ## Incompleteness
    /// Let P be the base point, Q bit the scalar point, and b[i] a bits.
    ///
    /// Assumes that for all j, $P + \sum_{i=0}^j b[i] * 2^i * Q$
    /// is non-zero and is not equal to $2^{i+1} * Q$.
    ///
    /// This can be ensured by randomizing P independently of Q and the bits.
    /// The incompletenes probability is then at most 2n/|F|, where n is the number of bits and F
    /// is the field size.
    fn incomplete_fma(
        base_point: GVar,
        scalar_point: &G,
        scalar_bits: &[Boolean<F>],
    ) -> Result<GVar, SynthesisError> {
        let n = scalar_bits.len();
        let mut acc = base_point;
        let point_powers: Vec<G> = std::iter::successors(Some((*scalar_point).clone()), |pt| {
            Some(Self::constant_double(pt))
        })
        .take(n)
        .collect();
        for i in 0..n {
            acc = Self::conditional_constant_add(&scalar_bits[i], acc, &point_powers[i]);
        }
        Ok(acc)
    }
    fn precomputed_base_multiscalar_mul_le<'a, T: ?Sized, I>(
        cs: Namespace<F>,
        acc_point: &G,
        bases: &[G],
        scalars: I,
    ) -> Result<GVar, SynthesisError>
    where
        T: 'a + ToBitsGadget<F>,
        I: Iterator<Item = &'a T>,
    {
        let mut result = Self::alloc_constant(cs, acc_point)?;
        // Compute Σᵢ(bitᵢ * baseᵢ) for all i.
        for (bits, base) in scalars.zip(bases.iter()) {
            let bits = bits.to_bits_le()?;
            result = Self::incomplete_fma(result, base, &bits)?;
        }
        Ok(result)
    }
}

pub mod models {
    use super::{SWCycleChain1, SWCycleChain2, SWCycleParameters, TEPair};
    pub struct JubJubPair;

    impl TEPair for JubJubPair {
        type P1 = ark_ed_on_bls12_381::EdwardsParameters;
        type G2 = ark_bls12_381::G1Projective;
    }

    pub struct PastaCycle;
    impl SWCycleParameters for PastaCycle {
        type P1 = ark_pallas::PallasParameters;
        type P2 = ark_vesta::VestaParameters;
        type G1 = ark_pallas::Projective;
        type G2 = ark_vesta::Projective;
    }

    /// Pasta-on-Vesta
    pub type PastaPair = SWCycleChain1<PastaCycle>;
    /// Vesta-on-Pallas
    pub type VellasPair = SWCycleChain2<PastaCycle>;
}

#[derive(Derivative)]
#[derivative(Default(bound = ""))]
pub struct TECompleteOps<F: PrimeField, P: ModelParameters<BaseField = F> + TEModelParameters>(
    pub PhantomData<(F, P)>,
);

impl<F: PrimeField, P: ModelParameters<BaseField = F> + TEModelParameters>
    IncompleteOpsGadget<F, TEGroupProjective<P>, TEAffineVar<P, FpVar<F>>> for TECompleteOps<F, P>
{
    fn add(a: &TEAffineVar<P, FpVar<F>>, b: &TEAffineVar<P, FpVar<F>>) -> TEAffineVar<P, FpVar<F>> {
        a.clone() + b
    }
    fn double(a: &TEAffineVar<P, FpVar<F>>) -> TEAffineVar<P, FpVar<F>> {
        a.double().unwrap()
    }
    fn constant_double(a: &TEGroupProjective<P>) -> TEGroupProjective<P> {
        Group::double(a)
    }
    fn conditional_constant_add(
        _b: &Boolean<F>,
        _x0: TEAffineVar<P, FpVar<F>>,
        _x1: &TEGroupProjective<P>,
    ) -> TEAffineVar<P, FpVar<F>> {
        // We stub out the MSM, so this does not matter.
        unimplemented!()
    }

    fn enforce_on_curve(_pt: &TEAffineVar<P, FpVar<F>>) -> Result<(), SynthesisError> {
        // TODO
        Ok(())
    }

    fn new_variable(
        cs: impl Into<Namespace<<P::BaseField as Field>::BasePrimeField>>,
        f: impl FnOnce() -> Result<TEGroupProjective<P>, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<TEAffineVar<P, FpVar<F>>, SynthesisError> {
        // TODO: breaks if removed!
        TEAffineVar::new_variable_omit_on_curve_check(cs, f, mode)
    }
    fn alloc_constant(
        cs: impl Into<Namespace<<P::BaseField as Field>::BasePrimeField>>,
        a: &TEGroupProjective<P>,
    ) -> Result<TEAffineVar<P, FpVar<F>>, SynthesisError> {
        AllocVar::new_constant(cs, a.clone())
    }
    fn precomputed_base_multiscalar_mul_le<'a, T: ?Sized, I>(
        cs: Namespace<F>,
        acc_point: &TEGroupProjective<P>,
        bases: &[TEGroupProjective<P>],
        scalars: I,
    ) -> Result<TEAffineVar<P, FpVar<F>>, SynthesisError>
    where
        T: 'a + ToBitsGadget<F>,
        I: Iterator<Item = &'a T>,
    {
        let t = start_timer!(|| "pb_msm");
        let point_powers = timed!(|| "point powers", compute_point_powers(bases));
        let r = TEAffineVar::<P, FpVar<F>>::precomputed_base_multiscalar_mul_le(
            &point_powers,
            scalars,
        )?;
        end_timer!(t);
        let acc_point = Self::alloc_constant(cs, acc_point)?;
        Ok(r + acc_point)
    }
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

impl<P: TEModelParameters> AffCoords for TEGroupProjective<P> {
    type BaseField = P::BaseField;
    fn get_xy(&self) -> (P::BaseField, P::BaseField) {
        let aff = self.clone().into_affine();
        (aff.x, aff.y)
    }
}

impl<P: TEPair> Pair for P
where
    <P::P1 as ModelParameters>::BaseField: PrimeField,
{
    type TopField = <P::P1 as ModelParameters>::ScalarField;
    type LinkField = <P::G2 as Group>::ScalarField;
    type P1 = P::P1;
    type G1 = TEGroupProjective<P::P1>;
    type G1Var = TEAffineVar<P::P1, FpVar<Self::LinkField>>;
    type G1IncompleteOps = TECompleteOps<Self::LinkField, P::P1>;
    type G2 = P::G2;
}

#[derive(Derivative)]
#[derivative(Default(bound = ""))]
pub struct SWIncompleteAffOps<F: PrimeField, P: ModelParameters<BaseField = F> + SWModelParameters>(
    pub PhantomData<(F, P)>,
);

impl<F: PrimeField, P: ModelParameters<BaseField = F> + SWModelParameters>
    IncompleteOpsGadget<F, SWGroupProjective<P>, SwNzAffVar<P, FpVar<F>>>
    for SWIncompleteAffOps<F, P>
{
    fn add(a: &SwNzAffVar<P, FpVar<F>>, b: &SwNzAffVar<P, FpVar<F>>) -> SwNzAffVar<P, FpVar<F>> {
        // slows us down substantially, for some reason...
        #[cfg(debug_assertions)]
        a.value()
            .map(|av| {
                b.value().map(|bv| {
                    assert!(!av.is_zero());
                    assert!(!bv.is_zero());
                    assert!(!(av + bv).is_zero());
                })
            })
            .ok();
        a.x.enforce_not_equal(&b.x).unwrap();
        a.add_unchecked(b).unwrap()
    }
    fn constant_double(x1: &SWGroupProjective<P>) -> SWGroupProjective<P> {
        x1.clone() + x1.clone()
    }
    fn double(a: &SwNzAffVar<P, FpVar<F>>) -> SwNzAffVar<P, FpVar<F>> {
        a.double().unwrap()
    }
    fn conditional_constant_add(
        b: &Boolean<F>,
        x0: SwNzAffVar<P, FpVar<F>>,
        x1: &SWGroupProjective<P>,
    ) -> SwNzAffVar<P, FpVar<F>> {
        let ns = x0.cs();
        let constant = Self::alloc_constant(ns, x1).unwrap();
        let sum = Self::add(&x0, &constant);
        CondSelectGadget::conditionally_select(&b, &sum, &x0).unwrap()
    }

    fn enforce_on_curve(pt: &SwNzAffVar<P, FpVar<F>>) -> Result<(), SynthesisError> {
        let x = pt.x.clone();
        let y = pt.y.clone();
        let y2 = y.clone() * &y;
        let x3 = x.clone() * &x * &x;
        let rhs = x3 + x.clone() * P::COEFF_A + P::COEFF_B;
        y2.enforce_equal(&rhs)
    }

    fn new_variable(
        cs: impl Into<Namespace<<P::BaseField as Field>::BasePrimeField>>,
        f: impl FnOnce() -> Result<SWGroupProjective<P>, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<SwNzAffVar<P, FpVar<F>>, SynthesisError> {
        let f_res = f().map(|p| p.into_affine());
        let ns = cs.into();
        if let Ok(a) = f_res.as_ref() {
            assert!(!a.is_zero());
        }
        let x = FpVar::new_variable(ns.clone(), || f_res.map(|a| a.x), mode)?;
        let y = FpVar::new_variable(ns.clone(), || f_res.map(|a| a.y), mode)?;
        if let (Ok(x), Ok(y)) = (x.value(), y.value()) {
            assert_eq!(
                (x.clone() * &x * &x) + P::COEFF_A * x + P::COEFF_B,
                y.clone() * &y
            );
        }
        Ok(SwNzAffVar::new(x, y))
    }
    fn alloc_constant(
        cs: impl Into<Namespace<<P::BaseField as Field>::BasePrimeField>>,
        a: &SWGroupProjective<P>,
    ) -> Result<SwNzAffVar<P, FpVar<F>>, SynthesisError> {
        assert!(!a.is_zero());
        let aff = a.into_affine();
        let ns = cs.into();
        let x = FpVar::new_constant(ns.clone(), aff.x)?;
        let y = FpVar::new_constant(ns, aff.y)?;
        Ok(SwNzAffVar::new(x, y))
    }
    fn precomputed_base_multiscalar_mul_le<'a, T: ?Sized, I>(
        cs: Namespace<F>,
        acc_point: &SWGroupProjective<P>,
        points: &[SWGroupProjective<P>],
        scalars: I,
    ) -> Result<SwNzAffVar<P, FpVar<F>>, SynthesisError>
    where
        T: 'a + ToBitsGadget<F>,
        I: Iterator<Item = &'a T>,
    {
        let bits_per_scalar = P::ScalarField::size_in_bits();
        // Get the points that we want to multiply by bits.
        let bit_points = points
            .iter()
            .flat_map(|pt| {
                successors(Some(pt.clone()), |prev| Some(ProjectiveCurve::double(prev)))
                    .take(bits_per_scalar)
            })
            .vcollect();
        // Get the bits
        let bits = scalars.flat_map(|s| s.to_bits_le().unwrap()).vcollect();
        assert_eq!(bit_points.len(), bits.len());
        // We're going to compute the MSM using windowed conditional addition.
        //
        // That is, for a window of n bits,
        //
        // Now we want to compute a bit-msm.
        //
        // Our incomplete addition gadget requires 3 constraints.
        //
        // The following table shows cost.
        //
        // n | cs (mux) | cs w/ 2 mux | cs w/ op | cs/bit
        // --+----------+-------------+----------+-------
        // 1 |        0 |           0 |        3 |   3.00
        // 2 |        1 |           2 |        5 |   2.50
        // 3 |        2 |           4 |        7 |   2.33  (this one)
        // 4 |        4 |           8 |       11 |   2.75
        let const_ = Self::alloc_constant(cs.clone(), acc_point)?;
        let mut double_acc = acc_point.clone();
        double_acc *= P::ScalarField::from(2u32);
        let mut result = const_.clone();
        let mut n_chunks = 0u64;
        let n = 3;
        for (ps, bs) in bit_points.chunks(n).zip(bits.chunks(n)) {
            n_chunks += 1;
            assert_eq!(ps.len(), bs.len());
            let m = ps.len();
            let mut points = vec![double_acc.clone(); 1 << m];
            for (i, p) in ps.iter().enumerate() {
                for j in 0..points.len() {
                    if (j >> i) & 1 == 1 {
                        points[j] += p;
                    }
                }
            }
            let to_add = Self::constant_lookup(bs, &points);
            result = Self::add(&result, &to_add);
        }
        if n_chunks > 0 {
            double_acc *= P::ScalarField::from(n_chunks);
            let shift = Self::alloc_constant(cs.clone(), &double_acc)?;
            result = result.sub_unchecked(&shift)?;
        }
        Ok(result)
    }
}
impl<F: PrimeField, P: ModelParameters<BaseField = F> + SWModelParameters>
    SWIncompleteAffOps<F, P>
{
    /// bits are little-endian (LSB at index 0)
    ///
    /// Supports 1, 2, and 3 bits
    fn constant_lookup(
        bits: &[Boolean<F>],
        table: &[SWGroupProjective<P>],
    ) -> SwNzAffVar<P, FpVar<F>> {
        debug_assert_eq!(table.len(), 1 << bits.len());
        let atable = table.iter().map(|p| p.into_affine()).vcollect();
        let (x, y) = match bits.len() {
            1 => (
                constant_lookup_1bit_fpvar(bits, atable.iter().map(|pt| &pt.x)),
                constant_lookup_1bit_fpvar(bits, atable.iter().map(|pt| &pt.y)),
            ),
            2 => (
                constant_lookup_2bit_fpvar(bits, atable.iter().map(|pt| &pt.x)),
                constant_lookup_2bit_fpvar(bits, atable.iter().map(|pt| &pt.y)),
            ),
            3 => (
                constant_lookup_3bit_fpvar(bits, atable.iter().map(|pt| &pt.x)),
                constant_lookup_3bit_fpvar(bits, atable.iter().map(|pt| &pt.y)),
            ),
            n => panic!("Unsupport table bit size {}", n),
        };
        let r = SwNzAffVar::new(x, y);
        r
    }
}

/// bits are little-endian (LSB at index 0)
fn constant_lookup_3bit_fpvar<'a, F: PrimeField>(
    bits: &[Boolean<F>],
    mut table: impl Iterator<Item = &'a F>,
) -> FpVar<F> {
    debug_assert_eq!(bits.len(), 3);
    let b0: FpVar<F> = bits[0].clone().into();
    let b1: FpVar<F> = bits[1].clone().into();
    let b2: FpVar<F> = bits[2].clone().into();
    let t0 = table.next().expect("wrong number of consts");
    let t1 = table.next().expect("wrong number of consts");
    let t2 = table.next().expect("wrong number of consts");
    let t3 = table.next().expect("wrong number of consts");
    let t4 = table.next().expect("wrong number of consts");
    let t5 = table.next().expect("wrong number of consts");
    let t6 = table.next().expect("wrong number of consts");
    let t7 = table.next().expect("wrong number of consts");
    debug_assert!(table.next().is_none(), "too many consts");
    // Real multiplication
    let b01 = b0.clone() * &b1;

    let a210 = b01.clone() * (*t7 - t6 - t5 + t4 - t3 + t2 + t1 - t0);
    let a21 = b1.clone() * (*t6 - t4 - t2 + t0);
    let a20 = b0.clone() * (*t5 - t4 - t1 + t0);
    let a2 = *t4 - t0;

    let a10 = b01 * (*t3 - t2 - t1 + t0);
    let a1 = b1 * (*t2 - t0);
    let a0 = b0 * (*t1 - t0);
    let a = t0;
    // Real multiplication
    (a210 + a21 + a20 + a2) * b2 + (a10 + a1 + a0 + *a)
}

/// bits are little-endian (LSB at index 0)
fn constant_lookup_2bit_fpvar<'a, F: PrimeField>(
    bits: &[Boolean<F>],
    mut table: impl Iterator<Item = &'a F>,
) -> FpVar<F> {
    debug_assert_eq!(bits.len(), 2);
    let b0: FpVar<F> = bits[0].clone().into();
    let b1: FpVar<F> = bits[1].clone().into();
    let t0 = table.next().expect("wrong number of consts");
    let t1 = table.next().expect("wrong number of consts");
    let t2 = table.next().expect("wrong number of consts");
    let t3 = table.next().expect("wrong number of consts");
    debug_assert!(table.next().is_none(), "too many consts");
    // Real multiplication
    let b01 = b0.clone() * &b1;

    let a10 = b01.clone() * (*t3 - t2 - t1 + t0);
    let a1 = b1.clone() * (*t2 - t0);
    let a0 = b0.clone() * (*t1 - t0);
    let a = t0;

    a10 + a1 + a0 + *a
}

/// bits are little-endian (LSB at index 0)
fn constant_lookup_1bit_fpvar<'a, F: PrimeField>(
    bits: &[Boolean<F>],
    mut table: impl Iterator<Item = &'a F>,
) -> FpVar<F> {
    debug_assert_eq!(bits.len(), 1);
    let b0: FpVar<F> = bits[0].clone().into();
    let t0 = table.next().expect("wrong number of consts");
    let t1 = table.next().expect("wrong number of consts");
    debug_assert!(table.next().is_none(), "too many consts");
    b0.clone() * (*t1 - t0) + *t0
}

/// A pair (G1, G2)
/// where the base field of G1 is the scalar field of G2,
/// and vice-versa
///
/// Furthermore, we have:
/// * a known-scalar MSM gadget for G1 points.
/// * a known-point MSM gadget for G1 points.
/// *
pub trait TwoCycle {
    type ScalarField1: PrimeField;
    type ScalarField2: PrimeField;
    type P1: ModelParameters<BaseField = Self::ScalarField2>;
    type G1: ProjectiveCurve<ScalarField = Self::ScalarField1, BaseField = Self::ScalarField2>
        + AffCoords<BaseField = Self::ScalarField2>;

    type G1Var: EqGadget<Self::ScalarField2> + Debug + R1CSVar<Self::ScalarField2>;
    type G1IncompleteOps: IncompleteOpsGadget<Self::ScalarField2, Self::G1, Self::G1Var>;
    type P2: ModelParameters<BaseField = Self::ScalarField1>;
    type G2: ProjectiveCurve<ScalarField = Self::ScalarField2, BaseField = Self::ScalarField1>
        + AffCoords<BaseField = Self::ScalarField1>;
    type G2Var: EqGadget<Self::ScalarField1> + Debug + R1CSVar<Self::ScalarField2>;
    type G2IncompleteOps: IncompleteOpsGadget<Self::ScalarField1, Self::G2, Self::G2Var>;
}

pub trait SWCycleParameters {
    type P1: SWModelParameters;
    type P2: SWModelParameters;
    type G1: Group<ScalarField = <Self::P2 as ModelParameters>::BaseField>;
    type G2: Group<ScalarField = <Self::P1 as ModelParameters>::BaseField>;
}

impl<P: SWModelParameters> AffCoords for SWGroupProjective<P> {
    type BaseField = P::BaseField;
    fn get_xy(&self) -> (P::BaseField, P::BaseField) {
        let aff = self.clone().into_affine();
        (aff.x, aff.y)
    }
}

pub struct SWCycleChain1<C: SWCycleParameters>(pub PhantomData<C>);
impl<C: SWCycleParameters> Pair for SWCycleChain1<C>
where
    <C::P1 as ModelParameters>::BaseField: PrimeField,
{
    type TopField = <<C as SWCycleParameters>::P1 as ModelParameters>::ScalarField;
    type LinkField = <<C as SWCycleParameters>::G2 as Group>::ScalarField;
    type P1 = <C as SWCycleParameters>::P1;
    type G1 = SWGroupProjective<<C as SWCycleParameters>::P1>;
    type G1Var = SwNzAffVar<<C as SWCycleParameters>::P1, FpVar<Self::LinkField>>;
    type G1IncompleteOps = SWIncompleteAffOps<Self::LinkField, <C as SWCycleParameters>::P1>;
    type G2 = <C as SWCycleParameters>::G2;
}

pub struct SWCycleChain2<C: SWCycleParameters>(pub PhantomData<C>);
impl<C: SWCycleParameters> Pair for SWCycleChain2<C>
where
    <C::P2 as ModelParameters>::BaseField: PrimeField,
{
    type TopField = <<C as SWCycleParameters>::P2 as ModelParameters>::ScalarField;
    type LinkField = <<C as SWCycleParameters>::G1 as Group>::ScalarField;
    type P1 = <C as SWCycleParameters>::P2;
    type G1 = SWGroupProjective<<C as SWCycleParameters>::P2>;
    type G1Var = SwNzAffVar<<C as SWCycleParameters>::P2, FpVar<Self::LinkField>>;
    type G1IncompleteOps = SWIncompleteAffOps<Self::LinkField, <C as SWCycleParameters>::P2>;
    type G2 = <C as SWCycleParameters>::G1;
}

#[cfg(test)]
mod test {
    use super::*;
    use ark_relations::{
        ns,
        r1cs::{
            self, ConstraintLayer, ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef,
            OptimizationGoal, TracingMode,
        },
    };
    use rand::Rng;
    use tracing_subscriber::layer::SubscriberExt;

    struct Add<C: Pair> {
        xs: Vec<C::G1>,
    }

    impl<C: Pair> Add<C> {
        fn result(&self) -> C::G1 {
            self.xs.iter().sum()
        }
        pub fn sample_from_length<R: Rng + ?Sized>(rng: &mut R, length: usize) -> Self {
            Self {
                xs: (0..length).map(|_| C::G1::rand(rng)).collect(),
            }
        }
    }

    impl<C: Pair> ConstraintSynthesizer<C::LinkField> for Add<C> {
        fn generate_constraints(self, cs: ConstraintSystemRef<C::LinkField>) -> r1cs::Result<()> {
            let mut pts = self
                .xs
                .iter()
                .map(|pt| {
                    C::G1IncompleteOps::new_variable(
                        ns!(cs, "t alloc"),
                        || Ok(pt.clone()),
                        AllocationMode::Witness,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            let result = C::G1IncompleteOps::new_variable(
                ns!(cs, "t alloc"),
                || Ok(self.result()),
                AllocationMode::Witness,
            )?;
            let mut acc = pts.pop().unwrap();
            while pts.len() > 0 {
                acc =
                    <C::G1IncompleteOps as IncompleteOpsGadget<C::LinkField, C::G1, C::G1Var>>::add(
                        &pts.pop().unwrap(),
                        &acc,
                    );
            }
            acc.enforce_equal(&result).unwrap();
            Ok(())
        }
    }

    fn test_add<C: Pair>(m: usize) {
        let rng = &mut ark_std::test_rng();
        let cir = Add::<C>::sample_from_length(rng, m);
        let mut layer = ConstraintLayer::default();
        layer.mode = TracingMode::OnlyConstraints;
        let subscriber = tracing_subscriber::Registry::default().with(layer);
        let _guard = tracing::subscriber::set_default(subscriber);
        let cs: ConstraintSystemRef<C::LinkField> = ConstraintSystem::new_ref();
        cs.set_optimization_goal(OptimizationGoal::Constraints);
        cir.generate_constraints(cs.clone()).unwrap();
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
    fn test_add_bls() {
        test_add::<crate::curves::models::JubJubPair>(1);
        test_add::<crate::curves::models::JubJubPair>(10);
        test_add::<crate::curves::models::JubJubPair>(100);
    }

    #[test]
    fn test_add_pallas() {
        test_add::<crate::curves::SWCycleChain1<crate::curves::models::PastaCycle>>(1);
        test_add::<crate::curves::SWCycleChain1<crate::curves::models::PastaCycle>>(10);
        test_add::<crate::curves::SWCycleChain1<crate::curves::models::PastaCycle>>(100);
    }

    #[test]
    fn test_add_vesta() {
        test_add::<crate::curves::SWCycleChain2<crate::curves::models::PastaCycle>>(1);
        test_add::<crate::curves::SWCycleChain2<crate::curves::models::PastaCycle>>(10);
        test_add::<crate::curves::SWCycleChain2<crate::curves::models::PastaCycle>>(100);
    }

    fn test_add_constraint_count<C: Pair>(constraints: usize) {
        let rng = &mut ark_std::test_rng();
        let mut layer = ConstraintLayer::default();
        layer.mode = TracingMode::OnlyConstraints;
        let subscriber = tracing_subscriber::Registry::default().with(layer);
        let _guard = tracing::subscriber::set_default(subscriber);
        let cs: ConstraintSystemRef<C::LinkField> = ConstraintSystem::new_ref();
        cs.set_optimization_goal(OptimizationGoal::Constraints);
        let a = C::G1IncompleteOps::new_variable(
            ns!(cs, "a"),
            || Ok(C::G1::rand(rng)),
            AllocationMode::Witness,
        )
        .unwrap();
        let b = C::G1IncompleteOps::new_variable(
            ns!(cs, "b"),
            || Ok(C::G1::rand(rng)),
            AllocationMode::Witness,
        )
        .unwrap();
        let _sum = C::G1IncompleteOps::add(&a, &b);
        cs.finalize();
        assert_eq!(cs.num_constraints(), constraints);
    }

    #[test]
    fn jubjub_add() {
        test_add_constraint_count::<crate::curves::models::JubJubPair>(6);
    }
    #[test]
    fn vellas_add() {
        test_add_constraint_count::<crate::curves::models::VellasPair>(4);
    }
    #[test]
    fn pasta_add() {
        test_add_constraint_count::<crate::curves::models::PastaPair>(4);
    }
}
