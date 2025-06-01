use super::bigint::U254;

pub mod utils;
pub mod fq;
pub mod fq2;
// pub mod fq6;
// pub mod fq12;

pub trait Fp254Impl {
    const N_BITS: usize = U254::N_BITS;
    const MODULUS: &'static str;
}
