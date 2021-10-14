use ark_ec::{
    group::Group, models::short_weierstrass_jacobian::GroupAffine as SWGroupAffine,
    models::twisted_edwards_extended::GroupProjective as TEGroupProjective, ModelParameters,
    ProjectiveCurve, SWModelParameters, TEModelParameters,
};
use ark_ff::prelude::*;
use ark_r1cs_std::groups::curves::{
    short_weierstrass::non_zero_affine::NonZeroAffineVar as SwNzAffVar,
    short_weierstrass::AffineVar as SWAffineVar, twisted_edwards::AffineVar as TEAffineVar,
};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    bits::ToBitsGadget,
    boolean::Boolean,
    eq::EqGadget,
    fields::fp::FpVar,
    groups::CurveVar,
    select::CondSelectGadget,
};
use ark_relations::r1cs::{Namespace, SynthesisError};
use derivative::Derivative;
use std::borrow::Borrow;
use std::marker::PhantomData;

use ark_std::{end_timer, start_timer};

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
pub trait TwoChain {
    type TopField: PrimeField;
    type LinkField: PrimeField;
    type P1: ModelParameters<BaseField = Self::LinkField>;
    type G1: ProjectiveCurve<ScalarField = Self::TopField, BaseField = Self::LinkField>
        + AffCoords<BaseField = Self::LinkField>;
    type G1Var: EqGadget<Self::LinkField>;
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
pub trait IncompleteOpsGadget<F: Field, G: Clone, GVar> {
    /// Add two points that must
    /// * be non-equal
    /// * be non-zero
    /// * yield a non-zero result
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
    fn new_variable_omit_on_curve_check(
        cs: impl Into<Namespace<F>>,
        //cs: impl Into<Namespace<<G::BaseField as Field>::BasePrimeField>>,
        f: impl FnOnce() -> Result<G, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<GVar, SynthesisError>;

    /// Computes `base_point + scalar_bits * scalar_point`,
    /// where `scalar_bits` is a little-endian (MSB first).
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
            acc = Self::conditional_constant_add(&scalar_bits[n - i - 1], acc, &point_powers[i]);
        }
        Ok(acc)
    }
    fn precomputed_base_multiscalar_mul_le<'a, T: ?Sized, I>(
        acc_point: GVar,
        bases: &[G],
        scalars: I,
    ) -> Result<GVar, SynthesisError>
    where
        T: 'a + ToBitsGadget<F>,
        I: Iterator<Item = &'a T>,
    {
        let mut result = acc_point;
        // Compute Σᵢ(bitᵢ * baseᵢ) for all i.
        for (bits, base) in scalars.zip(bases.iter()) {
            let bits = bits.to_bits_le()?;
            result = Self::incomplete_fma(result, base, &bits)?;
        }
        Ok(result)
    }
}

pub mod models {
    use super::TEPair;
    pub struct JubJubPair;

    impl TEPair for JubJubPair {
        type P1 = ark_ed_on_bls12_381::EdwardsParameters;
        type G2 = ark_bls12_381::G1Projective;
    }
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
        b: &Boolean<F>,
        x0: TEAffineVar<P, FpVar<F>>,
        x1: &TEGroupProjective<P>,
    ) -> TEAffineVar<P, FpVar<F>> {
        // We stub out the MSM, so this does not matter.
        todo!()
    }

    fn new_variable_omit_on_curve_check(
        cs: impl Into<Namespace<<P::BaseField as Field>::BasePrimeField>>,
        f: impl FnOnce() -> Result<TEGroupProjective<P>, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<TEAffineVar<P, FpVar<F>>, SynthesisError> {
        TEAffineVar::new_variable_omit_on_curve_check(cs, f, mode)
    }
    fn alloc_constant(
        cs: impl Into<Namespace<<P::BaseField as Field>::BasePrimeField>>,
        a: &TEGroupProjective<P>,
    ) -> Result<TEAffineVar<P, FpVar<F>>, SynthesisError> {
        AllocVar::new_constant(cs, a.clone())
    }
    fn precomputed_base_multiscalar_mul_le<'a, T: ?Sized, I>(
        acc_point: TEAffineVar<P, FpVar<F>>,
        bases: &[TEGroupProjective<P>],
        scalars: I,
    ) -> Result<TEAffineVar<P, FpVar<F>>, SynthesisError>
    where
        T: 'a + ToBitsGadget<F>,
        I: Iterator<Item = &'a T>,
    {
        let t = start_timer!(|| "pb_msm");
        let point_powers = timed!(|| "point powers", compute_point_powers(bases));
        let r = TEAffineVar::<P, FpVar<F>>::precomputed_base_multiscalar_mul_le(&point_powers, scalars)?;
        end_timer!(t);
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

impl<P: TEPair> TwoChain for P
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
    IncompleteOpsGadget<F, SWGroupAffine<P>, SwNzAffVar<P, FpVar<F>>> for SWIncompleteAffOps<F, P>
{
    fn add(a: &SwNzAffVar<P, FpVar<F>>, b: &SwNzAffVar<P, FpVar<F>>) -> SwNzAffVar<P, FpVar<F>> {
        todo!()
    }
    fn constant_double(
        x1: &SWGroupAffine<P>,
    )-> SWGroupAffine<P>
    {
        todo!()
    }
    fn double(a: &SwNzAffVar<P, FpVar<F>>) -> SwNzAffVar<P, FpVar<F>> {
        todo!()
    }
    fn conditional_constant_add(
        b: &Boolean<F>,
        x0: SwNzAffVar<P, FpVar<F>>,
        x1: &SWGroupAffine<P>,
    ) -> SwNzAffVar<P, FpVar<F>> {
        todo!()
    }
    fn new_variable_omit_on_curve_check(
        cs: impl Into<Namespace<<P::BaseField as Field>::BasePrimeField>>,
        f: impl FnOnce() -> Result<SWGroupAffine<P>, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<SwNzAffVar<P, FpVar<F>>, SynthesisError> {
        let f_res = f();
        let ns = cs.into();
        let x = FpVar::new_variable(ns.clone(), || f_res.map(|a| a.x), mode)?;
        let y = FpVar::new_variable(ns, || f_res.map(|a| a.y), mode)?;
        Ok(SwNzAffVar::new(x, y))
    }
    fn alloc_constant(
        cs: impl Into<Namespace<<P::BaseField as Field>::BasePrimeField>>,
        a: &SWGroupAffine<P>,
    ) -> Result<SwNzAffVar<P, FpVar<F>>, SynthesisError> {
        let ns = cs.into();
        let x = FpVar::new_constant(ns.clone(), a.x)?;
        let y = FpVar::new_constant(ns, a.y)?;
        Ok(SwNzAffVar::new(x, y))
    }
}
