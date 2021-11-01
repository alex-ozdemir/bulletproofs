use ark_bp::{curves::models::{JubJubPair, PastaPair, VellasPair}, test_ipa, proofs::llbp::llbp};
use structopt::StructOpt;
use structopt::clap::arg_enum;

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
}

arg_enum! {
    #[derive(Debug)]
    enum Pair {
        Pasta,
        Vellas,
        Jubjub,
    }
}

fn main() {
    env_logger::init();
    let opt = Opt::from_args();
    match opt.curve {
        Pair::Pasta => test_ipa(vec![opt.n], 1, llbp::<PastaPair>(opt.k, opt.r)),
        Pair::Vellas => test_ipa(vec![opt.n], 1, llbp::<VellasPair>(opt.k, opt.r)),
        Pair::Jubjub => test_ipa(vec![opt.n], 1, llbp::<JubJubPair>(opt.k, opt.r)),
    }
}
