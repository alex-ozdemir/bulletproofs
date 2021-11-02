use ark_bp::{
    constraints,
    curves::models::{JubJubPair, PastaPair, VellasPair},
    ipa_size,
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
    curve: Pair,

    /// Mode
    #[structopt(short, long, default_value = "check")]
    mode: Mode,
}

arg_enum! {
    #[derive(Debug)]
    enum Pair {
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

fn main() {
    env_logger::init();
    let opt = Opt::from_args();
    match opt.mode {
        Mode::Check => match opt.curve {
            Pair::Pasta => test_ipa(vec![opt.n], 1, llbp::<PastaPair>(opt.k, opt.r)),
            Pair::Vellas => test_ipa(vec![opt.n], 1, llbp::<VellasPair>(opt.k, opt.r)),
            Pair::Jubjub => test_ipa(vec![opt.n], 1, llbp::<JubJubPair>(opt.k, opt.r)),
        },
        Mode::Constraints => {
            println!(
                "Size: {}",
                match opt.curve {
                    Pair::Pasta => constraints::<PastaPair>(opt.n, opt.k, opt.r),
                    Pair::Vellas => constraints::<PastaPair>(opt.n, opt.k, opt.r),
                    Pair::Jubjub => constraints::<PastaPair>(opt.n, opt.k, opt.r),
                }
            );
        }
        Mode::Size => {
            println!(
                "Size: {}",
                match opt.curve {
                    Pair::Pasta => ipa_size(opt.n, llbp::<PastaPair>(opt.k, opt.r)),
                    Pair::Vellas => ipa_size(opt.n, llbp::<VellasPair>(opt.k, opt.r)),
                    Pair::Jubjub => ipa_size(opt.n, llbp::<JubJubPair>(opt.k, opt.r)),
                }
            );
        }
    }
}
