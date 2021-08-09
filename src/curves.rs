use ark_ec::{
    group::Group, models::twisted_edwards_extended::GroupProjective, ModelParameters,
    ProjectiveCurve, TEModelParameters,
};
use ark_ff::prelude::*;
use ark_r1cs_std::groups::curves::twisted_edwards::AffineVar;
use ark_r1cs_std::{alloc::AllocationMode, fields::fp::FpVar, groups::CurveVar};
use ark_relations::r1cs::{Namespace, SynthesisError};
use derivative::Derivative;
use std::marker::PhantomData;

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
    type G1Var: CurveVar<Self::G1, Self::LinkField>;
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
pub trait IncompleteOpsGadget<F: Field, G: ProjectiveCurve, GVar: CurveVar<G, F>> {
    /// Add two points that must
    /// * be non-equal
    /// * be non-zero
    /// * yield a non-zero result
    fn add(a: &GVar, b: &GVar) -> GVar;
    /// Add a point to itself that must
    /// * yield a non-zero result
    fn double(a: &GVar) -> GVar;

    /// for ommiting checks that it is on the curve.
    fn new_variable_omit_on_curve_check(
        cs: impl Into<Namespace<<G::BaseField as Field>::BasePrimeField>>,
        f: impl FnOnce() -> Result<G, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<GVar, SynthesisError>;
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
pub struct TECompleteOps<
    F: PrimeField,
    P: ModelParameters<BaseField = F> + TEModelParameters,
    //GVar: CurveVar<GroupProjective<P>, F>,
>(pub PhantomData<(F, P)>);

impl<
        F: PrimeField,
        P: ModelParameters<BaseField = F> + TEModelParameters,
        //GVar: CurveVar<GroupProjective<P>, F>,
    > IncompleteOpsGadget<F, GroupProjective<P>, AffineVar<P, FpVar<F>>> for TECompleteOps<F, P>
{
    fn add(a: &AffineVar<P, FpVar<F>>, b: &AffineVar<P, FpVar<F>>) -> AffineVar<P, FpVar<F>> {
        a.clone() + b
    }
    fn double(a: &AffineVar<P, FpVar<F>>) -> AffineVar<P, FpVar<F>> {
        a.double().unwrap()
    }
    fn new_variable_omit_on_curve_check(
        cs: impl Into<Namespace<<P::BaseField as Field>::BasePrimeField>>,
        f: impl FnOnce() -> Result<GroupProjective<P>, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<AffineVar<P, FpVar<F>>, SynthesisError> {
        AffineVar::new_variable_omit_on_curve_check(cs, f, mode)
    }
}

impl<P: TEModelParameters> AffCoords for GroupProjective<P> {
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
    type G1 = GroupProjective<P::P1>;
    type G1Var = AffineVar<P::P1, FpVar<Self::LinkField>>;
    type G1IncompleteOps = TECompleteOps<Self::LinkField, P::P1>;
    type G2 = P::G2;
}
