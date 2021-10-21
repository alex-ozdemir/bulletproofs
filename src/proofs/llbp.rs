use crate::{
    curves::TwoChain,
    reductions::combinator::{RepeatWhile, Sequence, TrueReductionToProof},
    reductions::{
        bp_2ary_step::Bp2aryStep, bp_unroll_to_com_r1cs::UnrollToComR1cs,
        com_r1cs_to_ipa::ComR1csToIpa, ipa_send::SendIpa, ipa_to_bp_unroll::IpaToBpUnroll,
    },
    relations::ipa::{IpaInstance, IpaRelation},
    Proof,
};

/// Build an IPA protocol which
/// * does `r` rounds of committed `k`-ary recursion,
/// * SNARKs the unrolled relation so far,
/// * compiles the SNARK to an IPA in a new curve, and
/// * proves that via the classic bulletproofs.
///
/// Defined using [crate::Reduction] combinators.
pub fn llbp<C: TwoChain>(k: usize, r: usize) -> impl Proof<IpaRelation<C::G1>>
{
    TrueReductionToProof::new(Sequence::new(
        Sequence::new(
            Sequence::new(IpaToBpUnroll::<C>::new(k, r), UnrollToComR1cs::default()),
            ComR1csToIpa::default(),
        ),
        Sequence::new(
            RepeatWhile::new(Bp2aryStep::default(), |x: &IpaInstance<C::G2>| {
                x.gens.vec_size > 1
            }),
            SendIpa::default(),
        ),
    ))
}

#[cfg(test)]
mod test {
    use super::llbp;
    use crate::{curves::models::{JubJubPair, VellasPair, PastaPair}, test::test_ipa};
    #[test]
    #[ignore]
    fn test_jubjub() {
        let bp_pf = llbp::<JubJubPair>(8, 2);
        test_ipa(vec![1024], 1, bp_pf);
    }
    #[test]
    #[ignore]
    fn test_pasta() {
        let bp_pf = llbp::<PastaPair>(8, 2);
        test_ipa(vec![1024], 1, bp_pf);
    }
    #[test]
    #[ignore]
    fn test_vellas() {
        let bp_pf = llbp::<VellasPair>(8, 2);
        test_ipa(vec![1024], 1, bp_pf);
    }
}
