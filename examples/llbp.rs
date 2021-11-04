use ark_bp::{
    constraints,
    curves::models::{JubJubPair, PastaPair, VellasPair},
    curves::Pair,
    ipa_size,
    proofs::bp_iter::Bp,
    proofs::llbp::llbp,
    test_ipa,
};
use structopt::clap::arg_enum;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(name = "llbp", about = "LLBP benchmarking")]
struct Opt {
    /// Vector length
    #[structopt()]
    n: usize,

    /// Challenges per round
    #[structopt()]
    k: usize,

    /// Rounds before recursion
    #[structopt()]
    r: usize,

    /// Curve 2-chain
    #[structopt(short, long, default_value = "pasta")]
    curve: PairName,

    /// Mode
    #[structopt(short, long, default_value = "check")]
    mode: Mode,

    /// Proof system to use
    #[structopt(short, long, default_value = "llbp")]
    proof: Proof,
}

arg_enum! {
    #[derive(Debug)]
    enum PairName {
        Pasta,
        Vellas,
        Jubjub,
    }
}

arg_enum! {
    #[derive(Debug)]
    enum Mode {
        Check,
        Constraints,
        Size,
    }
}

arg_enum! {
    #[derive(Debug)]
    enum Proof {
        Bp,
        Llbp,
    }
}

fn main() {
    env_logger::init();
    let opt = Opt::from_args();
    match opt.proof {
        Proof::Bp => match opt.mode {
            Mode::Check => match opt.curve {
                PairName::Pasta => test_ipa(vec![opt.n], 1, Bp::<<PastaPair as Pair>::G1>::default()),
                PairName::Vellas => test_ipa(vec![opt.n], 1, Bp::<<VellasPair as Pair>::G1>::default()),
                PairName::Jubjub => test_ipa(vec![opt.n], 1, Bp::<<JubJubPair as Pair>::G1>::default()),
            }
            Mode::Constraints => panic!("Cannot count constraints for standard bulletproofs. There are no constraints involved!"),
            Mode::Size => {
                println!(
                    "Size: {}",
                    match opt.curve {
                        PairName::Pasta => ipa_size(opt.n, Bp::<<PastaPair as Pair>::G1>::default()),
                        PairName::Vellas => ipa_size(opt.n, Bp::<<VellasPair as Pair>::G1>::default()),
                        PairName::Jubjub => ipa_size(opt.n, Bp::<<JubJubPair as Pair>::G1>::default()),
                    }
                )
            }
        },
        Proof::Llbp => match opt.mode {
            Mode::Check => match opt.curve {
                PairName::Pasta => test_ipa(vec![opt.n], 1, llbp::<PastaPair>(opt.k, opt.r)),
                PairName::Vellas => test_ipa(vec![opt.n], 1, llbp::<VellasPair>(opt.k, opt.r)),
                PairName::Jubjub => test_ipa(vec![opt.n], 1, llbp::<JubJubPair>(opt.k, opt.r)),
            },
            Mode::Constraints => {
                println!(
                    "Size: {}",
                    match opt.curve {
                        PairName::Pasta => constraints::<PastaPair>(opt.n, opt.k, opt.r),
                        PairName::Vellas => constraints::<PastaPair>(opt.n, opt.k, opt.r),
                        PairName::Jubjub => constraints::<PastaPair>(opt.n, opt.k, opt.r),
                    }
                );
            }
            Mode::Size => {
                println!(
                    "Size: {}",
                    match opt.curve {
                        PairName::Pasta => ipa_size(opt.n, llbp::<PastaPair>(opt.k, opt.r)),
                        PairName::Vellas => ipa_size(opt.n, llbp::<VellasPair>(opt.k, opt.r)),
                        PairName::Jubjub => ipa_size(opt.n, llbp::<JubJubPair>(opt.k, opt.r)),
                    }
                );
            }
        },
    }
}
