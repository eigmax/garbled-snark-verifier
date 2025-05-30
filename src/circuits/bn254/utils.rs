use num_bigint::BigUint;
use rand::{rng, Rng};
use crate::circuits::bn254::fq::Fq;

pub fn random_fq() -> ark_bn254::Fq {
    let u = BigUint::from_bytes_le(&rng().random::<[u8; 32]>()) % Fq::modulus_as_biguint();
    ark_bn254::Fq::from(u)
}

pub fn bits_from_fq(u: ark_bn254::Fq) -> Vec<bool> {
    let mut bytes = BigUint::from(u).to_bytes_le();
    for _ in bytes.len()..32 {
        bytes.push(0_u8);
    }
    let mut bits = Vec::new();
    for byte in bytes {
        for i in 0..8 {
            bits.push(((byte >> i) & 1) == 1)
        }
    }
    bits.pop();
    bits.pop();
    bits
}

pub fn fq_from_bits(bits: Vec<bool>) -> ark_bn254::Fq {
    let zero = BigUint::ZERO;
    let one = BigUint::from(1_u8);
    let mut u = zero.clone();
    for bit in bits.iter().rev() {
        u = u.clone() + u.clone() + if *bit {one.clone()} else {zero.clone()};
    }
    ark_bn254::Fq::from(u)
}

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn test_random_fq() {
        let u = random_fq();
        println!("u: {:?}", u);
        let b = bits_from_fq(u.clone());
        let v = fq_from_bits(b);
        println!("v: {:?}", v);
        assert_eq!(u, v);
    }
}
