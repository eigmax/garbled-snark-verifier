use num_bigint::BigUint;

use crate::circuits::bn254::fp254impl::Fp254Impl;

pub struct Fr;

impl Fp254Impl for Fr {
    const MODULUS: &'static str =
        "21888242871839275222246405745257275088548364400416034343698204186575808495617";
    const MONTGOMERY_M_INVERSE: &'static str = 
        "5441563794177615591428663161977496376097281981129373443346157590346630955009";
   const MONTGOMERY_R_INVERSE: &'static str = 
        "17773755579518009376303681366703133516854333631346829854655645366227550102839";        
    const N_BITS: usize = 254;

    fn half_modulus() -> BigUint {
        BigUint::from(ark_bn254::Fr::from(1) / ark_bn254::Fr::from(2))
    }

    fn one_third_modulus() -> BigUint {
        BigUint::from(ark_bn254::Fr::from(1) / ark_bn254::Fr::from(3))
    }
    fn two_third_modulus() -> BigUint {
        BigUint::from(ark_bn254::Fr::from(2) / ark_bn254::Fr::from(3))
    }
}
