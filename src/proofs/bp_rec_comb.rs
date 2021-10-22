use crate::{
    reductions::combinator::{RepeatWhile, Sequence, TrueReductionToProof},
    reductions::{bp_2ary_step::Bp2aryStep, ipa_send::SendIpa},
    relations::ipa::{IpaInstance, IpaRelation},
    Proof,
};
use ark_ec::group::Group;

/// Build the classic bullet-proofs protocol
pub fn bp<G: Group>() -> impl Proof<IpaRelation<G>> {
    TrueReductionToProof::new(Sequence::new(
        RepeatWhile::new(Bp2aryStep::default(), |x: &IpaInstance<G>| {
            x.gens.vec_size > 1
        }),
        SendIpa::default(),
    ))
}

#[cfg(test)]
mod test {
    use super::bp;
    use crate::test_ipa;
    #[test]
    fn test_bls() {
        type G = ark_bls12_381::G1Projective;
        let bp_pf = bp::<G>();
        test_ipa(vec![1, 2, 4, 8, 16], 4, bp_pf);
    }
}
