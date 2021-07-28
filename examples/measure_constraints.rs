use ark_bp::{r1cs::measure_constraints, curves::models::JubJubPair};
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
}


fn main() {
    let opt = Opt::from_args();
    let rng = &mut rand::thread_rng();
    let cs = measure_constraints::<JubJubPair, _>(opt.k, opt.m, rng);
    println!("{}", cs);
}
