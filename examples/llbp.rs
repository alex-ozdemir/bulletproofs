use ark_bp::{
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

    /// print proof size and exit
    #[structopt(short, long)]
    size: bool,
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
    if opt.size {
        println!(
            "Size: {}",
            match opt.curve {
                Pair::Pasta => ipa_size(opt.n, llbp::<PastaPair>(opt.k, opt.r)),
                Pair::Vellas => ipa_size(opt.n, llbp::<VellasPair>(opt.k, opt.r)),
                Pair::Jubjub => ipa_size(opt.n, llbp::<JubJubPair>(opt.k, opt.r)),
            }
        );
    } else {
        match opt.curve {
            Pair::Pasta => test_ipa(vec![opt.n], 1, llbp::<PastaPair>(opt.k, opt.r)),
            Pair::Vellas => test_ipa(vec![opt.n], 1, llbp::<VellasPair>(opt.k, opt.r)),
            Pair::Jubjub => test_ipa(vec![opt.n], 1, llbp::<JubJubPair>(opt.k, opt.r)),
        }
    }
}
