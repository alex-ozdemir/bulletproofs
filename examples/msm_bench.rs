use ark_bp::util::CollectIter;
use ark_ec::group::Group;
use ark_ff::UniformRand;
use structopt::clap::arg_enum;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(name = "msm_bench", about = "Msm benchmarking")]
struct Opt {
    /// MSM size
    #[structopt()]
    n: usize,

    /// Curve
    #[structopt(short, long, default_value = "pallas")]
    curve: Curve,

    /// Alg
    #[structopt(short, long, default_value = "naive")]
    msm: Msm,
}

arg_enum! {
    #[derive(Debug)]
    enum Curve {
        Pallas,
        Vesta,
    }
}
arg_enum! {
    #[derive(Debug)]
    enum Msm {
        Pippenger,
        BosCoster,
        Naive,
    }
}

fn msm_bench<G: Group, F: FnOnce(Vec<G>, Vec<G::ScalarField>) -> G>(n: usize, f: F) -> f64 {
    let rng = &mut ark_std::test_rng();
    let gs = (0..n).map(|_| G::rand(rng)).vcollect();
    let xs = (0..n)
        .map(|_| <G as Group>::ScalarField::rand(rng))
        .vcollect();
    let start = std::time::Instant::now();
    let _r = f(gs, xs);
    let end = std::time::Instant::now();
    (end - start).as_secs_f64()
}

fn main() {
    let opt = Opt::from_args();
    let seconds = match (opt.curve, opt.msm) {
        (Curve::Pallas, Msm::Naive) => {
            msm_bench::<ark_pallas::Projective, _>(opt.n, |gs, xs| ark_bp::util::msm::msm(&gs, &xs))
        }
        (Curve::Vesta, Msm::Naive) => {
            msm_bench::<ark_vesta::Projective, _>(opt.n, |gs, xs| ark_bp::util::msm::msm(&gs, &xs))
        }
        (Curve::Pallas, Msm::BosCoster) => {
            msm_bench::<ark_pallas::Projective, _>(opt.n, |gs, xs| {
                ark_bp::util::msm::bos_coster_msm(&gs, &xs)
            })
        }
        (Curve::Vesta, Msm::BosCoster) => msm_bench::<ark_vesta::Projective, _>(opt.n, |gs, xs| {
            ark_bp::util::msm::bos_coster_msm(&gs, &xs)
        }),
        (Curve::Pallas, Msm::Pippenger) => {
            msm_bench::<ark_pallas::Projective, _>(opt.n, |gs, xs| {
                ark_bp::util::msm::pippenger_msm(&gs, &xs)
            })
        }
        (Curve::Vesta, Msm::Pippenger) => msm_bench::<ark_vesta::Projective, _>(opt.n, |gs, xs| {
            ark_bp::util::msm::pippenger_msm(&gs, &xs)
        }),
    };
    println!("{}", seconds);
}
