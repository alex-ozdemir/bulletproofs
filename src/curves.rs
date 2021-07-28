use ark_ec::{group::Group, TEModelParameters, ModelParameters};

pub trait TEPair {
    type P1: TEModelParameters;
    type G2: Group<ScalarField=<Self::P1 as ModelParameters>::BaseField>;
}

pub mod models {
    use super::TEPair;
    pub struct JubJubPair;

    impl TEPair for JubJubPair {
        type P1 = ark_ed_on_bls12_381::EdwardsParameters;
        type G2 = ark_bls12_381::G1Projective;
    }
}
