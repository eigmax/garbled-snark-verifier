use crate::circuits::bn254::fp254impl::Fp254Impl;

pub struct Fr;

impl Fp254Impl for Fr {
    const MODULUS: &'static str = "21888242871839275222246405745257275088548364400416034343698204186575808495617";
    const N_BITS: usize = 254;
}
