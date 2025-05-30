use num_bigint::BigUint;
use rand::{rng, Rng};
use crate::circuits::{bigint::U254, bn254::fq::Fq};

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

pub fn random_fq2() -> ark_bn254::Fq2 {
    let u = BigUint::from_bytes_le(&rng().random::<[u8; 32]>()) % Fq::modulus_as_biguint();
    let v = BigUint::from_bytes_le(&rng().random::<[u8; 32]>()) % Fq::modulus_as_biguint();
    ark_bn254::Fq2::new(ark_bn254::Fq::from(u), ark_bn254::Fq::from(v))
}

pub fn bits_from_fq2(u: ark_bn254::Fq2) -> Vec<bool> {
    let mut bytes = BigUint::from(u.c0).to_bytes_le();
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
    let mut bytes = BigUint::from(u.c1).to_bytes_le();
    for _ in bytes.len()..32 {
        bytes.push(0_u8);
    }
    for byte in bytes {
        for i in 0..8 {
            bits.push(((byte >> i) & 1) == 1)
        }
    }
    bits.pop();
    bits.pop();
    bits
}

pub fn fq2_from_bits(bits: Vec<bool>) -> ark_bn254::Fq2 {
    let zero = BigUint::ZERO;
    let one = BigUint::from(1_u8);
    let mut u = zero.clone();
    let mut v = zero.clone();
    let bits1 = &bits[0..U254::N_BITS];
    let bits2 = &bits[U254::N_BITS..U254::N_BITS*2];
    for bit in bits1.iter().rev() {
        u = u.clone() + u.clone() + if *bit {one.clone()} else {zero.clone()};
    }
    for bit in bits2.iter().rev() {
        v = v.clone() + v.clone() + if *bit {one.clone()} else {zero.clone()};
    }
    ark_bn254::Fq2::new(ark_bn254::Fq::from(u), ark_bn254::Fq::from(v))
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

    #[test]
    fn test_random_fq2() {
        let u = random_fq2();
        println!("u: {:?}", u);
        let b = bits_from_fq2(u.clone());
        let v = fq2_from_bits(b);
        println!("v: {:?}", v);
        assert_eq!(u, v);
    }
}
