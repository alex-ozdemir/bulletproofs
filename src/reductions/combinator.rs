use crate::{FiatShamirRng, Proof, Reduction, Relation};
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
    type Params = (R1::Params, R2::Params);
    type Proof = (R1::Proof, R2::Proof);
    fn prove(
        &self,
        pp: &Self::Params,
        x: &<Self::From as Relation>::Inst,
        w: &<Self::From as Relation>::Wit,
        fs: &mut FiatShamirRng,
    ) -> (
        Self::Proof,
        <Self::To as Relation>::Inst,
        <Self::To as Relation>::Wit,
    ) {
        let (pf_1, x_1, w_1) = self.r1.prove(&pp.0, x, w, fs);
        let (pf_2, x_2, w_2) = self.r2.prove(&pp.1, &x_1, &w_1, fs);
        ((pf_1, pf_2), x_2, w_2)
    }
    fn verify(
        &self,
        pp: &Self::Params,
        x: &<Self::From as Relation>::Inst,
        (ref pf_1, ref pf_2): &Self::Proof,
        fs: &mut FiatShamirRng,
    ) -> <Self::To as Relation>::Inst {
        let x_1 = self.r1.verify(&pp.0, x, pf_1, fs);
        let x_2 = self.r2.verify(&pp.1, &x_1, pf_2, fs);
        x_2
    }
    fn proof_size(p: &Self::Proof) -> usize {
        R1::proof_size(&p.0) + R2::proof_size(&p.1)
    }

    fn setup<R: rand::Rng>(&self, c1: &<Self::From as Relation>::Cfg, rng: &mut R) -> Self::Params {
        let p1 = self.r1.setup(c1, rng);
        let c2 = self.r1.map_params(c1);
        let p2 = self.r2.setup(&c2, rng);
        (p1, p2)
    }

    fn map_params(&self, c: &<Self::From as Relation>::Cfg) -> <Self::To as Relation>::Cfg {
        self.r2.map_params(&self.r1.map_params(c))
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
    type Params = R1::Params;
    type Proof = Vec<R1::Proof>;
    fn prove(
        &self,
        pp: &Self::Params,
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
            let (pf, xx, ww) = self.r.prove(&pp, &x, &w, fs);
            x = xx;
            w = ww;
            pfs.push(pf);
        }
        (pfs, x, w)
    }
    fn verify(
        &self,
        pp: &Self::Params,
        x: &<Self::From as Relation>::Inst,
        pfs: &Self::Proof,
        fs: &mut FiatShamirRng,
    ) -> <Self::To as Relation>::Inst {
        let mut x = (*x).clone();
        let mut pfs = (*pfs).clone();
        pfs.reverse();
        while (self.while_)(&x) {
            let pf = pfs.pop().expect("V expected another proof");
            let xx = self.r.verify(pp, &x, &pf, fs);
            x = xx;
        }
        assert_eq!(pfs.len(), 0, "Too many proofs");
        x
    }
    fn proof_size(p: &Self::Proof) -> usize {
        p.iter().map(|pi| R1::proof_size(pi)).sum()
    }

    fn setup<Rn: rand::Rng>(
        &self,
        c: &<Self::From as Relation>::Cfg,
        rng: &mut Rn,
    ) -> Self::Params {
        self.r.setup(c, rng)
    }

    fn map_params(&self, c: &<Self::From as Relation>::Cfg) -> <Self::To as Relation>::Cfg {
        // Not really right...
        self.r.map_params(c)
    }
}

pub struct True;

impl Relation for True {
    type Cfg = ();
    type Inst = ();
    type Wit = ();
    fn check(_: &Self::Inst, _: &Self::Wit) {
        // always holds
    }
    fn check_cfg(_: &Self::Cfg, _: &Self::Inst) {
        // always okay
    }
    fn size(_x: &Self::Inst) -> Self::Cfg {
        ()
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
    type Params = <P as Reduction>::Params;
    type Proof = <P as Reduction>::Proof;
    fn prove(
        &self,
        pp: &Self::Params,
        x: &<R as Relation>::Inst,
        w: &<R as Relation>::Wit,
        fs: &mut FiatShamirRng,
    ) -> Self::Proof {
        self.0.prove(pp, x, w, fs).0
    }
    fn verify(
        &self,
        pp: &Self::Params,
        x: &<R as Relation>::Inst,
        pf: &Self::Proof,
        fs: &mut FiatShamirRng,
    ) {
        self.0.verify(pp, x, pf, fs);
    }
    fn proof_size(p: &Self::Proof) -> usize {
        P::proof_size(p)
    }
    fn setup<Rn: rand::Rng>(&self, c: &R::Cfg, rng: &mut Rn) -> Self::Params {
        self.0.setup(c, rng)
    }
}

pub struct ProofToTrueReduction<R: Relation, P: Proof<R>>(pub P, pub PhantomData<R>);

impl<R: Relation, P: Proof<R>> ProofToTrueReduction<R, P> {
    pub fn new(pf: P) -> Self {
        Self(pf, Default::default())
    }
}

impl<R: Relation, P: Proof<R>> Reduction for ProofToTrueReduction<R, P> {
    type Params = <P as Proof<R>>::Params;
    type From = R;
    type To = True;
    type Proof = <P as Proof<R>>::Proof;
    fn prove(
        &self,
        pp: &Self::Params,
        x: &<R as Relation>::Inst,
        w: &<R as Relation>::Wit,
        fs: &mut FiatShamirRng,
    ) -> (
        Self::Proof,
        <Self::To as Relation>::Inst,
        <Self::To as Relation>::Wit,
    ) {
        (self.0.prove(pp, x, w, fs), (), ())
    }
    fn verify(
        &self,
        pp: &Self::Params,
        x: &<R as Relation>::Inst,
        pf: &Self::Proof,
        fs: &mut FiatShamirRng,
    ) {
        self.0.verify(pp, x, pf, fs);
    }
    fn proof_size(p: &Self::Proof) -> usize {
        P::proof_size(p)
    }

    fn setup<Rn: rand::Rng>(&self, c: &<R as Relation>::Cfg, rng: &mut Rn) -> Self::Params {
        self.0.setup(c, rng)
    }

    fn map_params(&self, _: &<R as Relation>::Cfg) -> <True as Relation>::Cfg {
        ()
    }
}
