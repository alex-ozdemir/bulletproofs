use crate::{
    curves::Pair,
    proofs::bp_iter::Bp,
    reductions::combinator::{ProofToTrueReduction, Sequence, TrueReductionToProof},
    reductions::{
        bp_unroll_to_com_r1cs::UnrollToComR1cs, com_r1cs_to_ipa::ComR1csToIpa,
        ipa_to_bp_unroll::IpaToBpUnroll,
    },
    relations::ipa::IpaRelation,
    Proof,
};

/// Build an IPA protocol which
/// * does `r` rounds of committed `k`-ary recursion,
/// * SNARKs the unrolled relation so far,
/// * compiles the SNARK to an IPA in a new curve, and
/// * proves that via the classic bulletproofs.
///
/// Defined using [crate::Reduction] combinators.
pub fn llbp<C: Pair>(k: usize, r: usize) -> impl Proof<IpaRelation<C::G1>> {
    TrueReductionToProof::new(Sequence::new(
        Sequence::new(
            Sequence::new(IpaToBpUnroll::<C>::new(k, r), UnrollToComR1cs::default()),
            ComR1csToIpa::default(),
        ),
        ProofToTrueReduction::new(Bp::default()),
    ))
}

#[cfg(test)]
mod test {
    use super::llbp;
    use crate::{
        curves::models::{JubJubPair, PastaPair, VellasPair},
        test_ipa,
    };
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
