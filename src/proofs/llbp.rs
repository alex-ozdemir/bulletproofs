use crate::{
    curves::TEPair,
    reductions::combinator::{RepeatWhile, Sequence, True, TrueReductionToProof},
    reductions::{
        bp_2ary_step::Bp2aryStep, bp_unroll_to_com_r1cs::UnrollToComR1cs,
        com_r1cs_to_ipa::ComR1csToIpa, ipa_send::SendIpa, ipa_to_bp_unroll::IpaToBpUnroll,
    },
    relations::ipa::{IpaInstance, IpaRelation},
    Proof, Reduction,
};
use ark_ec::{group::Group, twisted_edwards_extended::GroupProjective, ModelParameters};
use ark_ff::PrimeField;

/// Build the classic bullet-proofs protocol
pub fn llbp<P: TEPair>(k: usize, r: usize) -> impl Proof<IpaRelation<GroupProjective<P::P1>>>
where
    <P::P1 as ModelParameters>::BaseField: PrimeField,
{
    TrueReductionToProof::new(Sequence::new(ipa_to_ipa_via_snark::<P>(k, r), classic_bp()))
}

fn classic_bp<G: Group>() -> impl Reduction<From = IpaRelation<G>, To = True> {
    Sequence::new(
        RepeatWhile::new(Bp2aryStep::default(), |x: &IpaInstance<G>| {
            x.gens.vec_size > 1
        }),
        SendIpa::default(),
    )
}
fn ipa_to_ipa_via_snark<P: TEPair>(
    k: usize,
    r: usize,
) -> impl Reduction<From = IpaRelation<GroupProjective<P::P1>>, To = IpaRelation<P::G2>>
where
    <P::P1 as ModelParameters>::BaseField: PrimeField,
{
    Sequence::new(
        Sequence::new(IpaToBpUnroll::<P>::new(k, r), UnrollToComR1cs::default()),
        ComR1csToIpa::default(),
    )
}

#[cfg(test)]
mod test {
    use super::llbp;
    use crate::{curves::models::JubJubPair, test::test_ipa};
    #[test]
    fn test_bls() {
        let bp_pf = llbp::<JubJubPair>(8, 2);
        test_ipa(vec![1024], 1, bp_pf);
    }
}
