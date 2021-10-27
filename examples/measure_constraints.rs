use ark_bp::{
    curves::models::{JubJubPair, PastaPair, VellasPair},
    r1cs::measure_constraints,
};
use structopt::clap::arg_enum;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(name = "measure_constraints", about = "Constraint benchmarking")]
struct Opt {
    /// Fixed-scalar MSM size
    #[structopt()]
    k: usize,

    /// IP vector size
    #[structopt()]
    m: usize,

    /// Curve 2-chain
    #[structopt(short, long, default_value = "jubjub")]
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
    let opt = Opt::from_args();
    let rng = &mut rand::thread_rng();
    let cs = match opt.curve {
        Pair::Pasta => measure_constraints::<PastaPair, _>(opt.k, opt.m, rng),
        Pair::Vellas => measure_constraints::<VellasPair, _>(opt.k, opt.m, rng),
        Pair::Jubjub => measure_constraints::<JubJubPair, _>(opt.k, opt.m, rng),
    };
    println!("{}", cs);
}
