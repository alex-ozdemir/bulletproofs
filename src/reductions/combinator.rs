use crate::{Reduction, Relation, FiatShamirRng};

struct Sequence<R1: Reduction, R2: Reduction> {
    r1: R1,
    r2: R2,
}

impl<R1: Reduction, R2: Reduction<From = R1::To>> Reduction for Sequence<R1, R2> {
    type From = R1::From;
    type To = R2::To;
    type Proof = (R1::Proof, R2::Proof);
    fn prove(
        &self,
        x: &<Self::From as Relation>::Inst,
        w: &<Self::From as Relation>::Wit,
        fs: &mut FiatShamirRng,
    ) -> (
        Self::Proof,
        <Self::To as Relation>::Inst,
        <Self::To as Relation>::Wit,
    ) {
        let (pf_1, x_1, w_1) = self.r1.prove(x, w, fs);
        let (pf_2, x_2, w_2) = self.r2.prove(&x_1, &w_1, fs);
        ((pf_1, pf_2), x_2, w_2)
    }
    fn verify(
        &self,
        x: &<Self::From as Relation>::Inst,
        (ref pf_1, ref pf_2): &Self::Proof,
        fs: &mut FiatShamirRng,
    ) -> <Self::To as Relation>::Inst {
        let x_1 = self.r1.verify(x, pf_1, fs);
        let x_2 = self.r2.verify(&x_1, pf_2, fs);
        x_2
    }
}

struct RepeatWhile<R: Relation, R1: Reduction<From=R, To=R>, While: Fn(&R::Inst) -> bool> {
    r: R1,
    while_: While,
}

impl<R: Relation, R1: Reduction<From=R, To=R>, While: Fn(&R::Inst) -> bool> Reduction for RepeatWhile<R, R1, While>
where R::Inst: Clone,
      R::Wit: Clone,
      R1::Proof: Clone,
{
    type From = R1::From;
    type To = R1::To;
    type Proof = Vec<R1::Proof>;
    fn prove(
        &self,
        x: &<Self::From as Relation>::Inst,
        w: &<Self::From as Relation>::Wit,
        fs: &mut FiatShamirRng,
    ) -> (
        Self::Proof,
        <Self::To as Relation>::Inst,
        <Self::To as Relation>::Wit,
    ) {
        let mut x = (*x).clone();
        let mut w = (*w).clone();
        let mut pfs = Vec::new();
        while (self.while_)(&x) {
            let (pf, xx, ww) = self.r.prove(&x, &w, fs);
            x = xx;
            w = ww;
            pfs.push(pf);
        }
        (pfs, x, w)
    }
    fn verify(
        &self,
        x: &<Self::From as Relation>::Inst,
        pfs: &Self::Proof,
        fs: &mut FiatShamirRng,
    ) -> <Self::To as Relation>::Inst {
        let mut x = (*x).clone();
        let mut pfs = (*pfs).clone();
        pfs.reverse();
        while (self.while_)(&x) {
            let pf = pfs.pop().expect("V expected another proof");
            let xx = self.r.verify(&x, &pf, fs);
            x = xx;
        }
        assert_eq!(pfs.len(), 0, "Too many proofs");
        x
    }
}
