//! Generalized IPA relation
//!
//! A traditional IPA relation is
//!
//!     p = <a, gen_a> + <b, gen_b> + <a, b> * q
//!
//! where `(p, gen_a, gen_b, q)` is the instance and `(a, b)` is the witness.
//!
//! A genealized IPA relation is
//!
//!     p + <s, t> = <a, gen_a> + <b, gen_b> + <a,b> * q AND c = commit(t)
//!
//! where `(p, gen_a, gen_b, q, s, c)` is the instance and `(a, b, t)` is the witness.

use super::{IpaInstance, IpaWitness};
