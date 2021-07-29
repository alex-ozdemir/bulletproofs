use crate::{FiatShamirRng, Reduction, Relation, Proof};
use std::marker::PhantomData;

pub struct Sequence<R1: Reduction, R2: Reduction> {
    r1: R1,
    r2: R2,
}

impl<R1: Reduction, R2: Reduction> Sequence<R1, R2> {
    pub fn new(r1: R1, r2: R2) -> Self {
        Self { r1, r2 }
    }
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

pub struct RepeatWhile<R: Relation, R1: Reduction<From = R, To = R>, While: Fn(&R::Inst) -> bool> {
    r: R1,
    while_: While,
}

impl<R: Relation, R1: Reduction<From = R, To = R>, While: Fn(&R::Inst) -> bool>
    RepeatWhile<R, R1, While>
{
    pub fn new(r: R1, while_: While) -> Self {
        Self { r, while_ }
    }
}

impl<R: Relation, R1: Reduction<From = R, To = R>, While: Fn(&R::Inst) -> bool> Reduction
    for RepeatWhile<R, R1, While>
where
    R::Inst: Clone,
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

pub struct True;

impl Relation for True {
    type Inst = ();
    type Wit = ();
    fn check(_: &Self::Inst, _: &Self::Wit) {
        // always holds
    }
}

pub struct TrueReductionToProof<R: Relation, P: Reduction<From = R, To = True>>(
    pub P,
    pub PhantomData<R>,
);

impl<R: Relation, P: Reduction<From = R, To = True>> TrueReductionToProof<R, P> {
    pub fn new(pf: P) -> Self {
        Self(pf, Default::default())
    }
}

impl<R: Relation, P: Reduction<From = R, To = True>> Proof<R> for TrueReductionToProof<R, P> {
    type Proof = <P as Reduction>::Proof;
    fn prove(
        &self,
        x: &<R as Relation>::Inst,
        w: &<R as Relation>::Wit,
        fs: &mut FiatShamirRng,
    ) -> Self::Proof {
        self.0.prove(x, w, fs).0
    }
    fn verify(&self, x: &<R as Relation>::Inst, pf: &Self::Proof, fs: &mut FiatShamirRng) {
        self.0.verify(x, pf, fs);
    }
}

