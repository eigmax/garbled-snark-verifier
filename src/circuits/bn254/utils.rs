use ark_ff::UniformRand;
use ark_std::rand::SeedableRng;
use num_bigint::BigUint;
use rand::{rng, Rng};
use rand_chacha::ChaCha20Rng;
use crate::circuits::bn254::fp254impl::Fp254Impl;
use crate::circuits::bn254::fr::Fr;
use crate::circuits::bn254::g1::G1Projective;
use crate::circuits::bn254::{fq::Fq, fq2::Fq2, fq6::Fq6, fq12::Fq12};
use crate::bag::*;
use super::g2::G2Projective;

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

pub fn wires_for_fq() -> Wires {
    (0..Fq::N_BITS).map(|_| { Rc::new(RefCell::new(Wire::new())) }).collect()
}

pub fn wires_set_from_fq(u: ark_bn254::Fq) -> Wires {
    bits_from_fq(u)[0..Fq::N_BITS].iter().map(|bit| {
        let wire = Rc::new(RefCell::new(Wire::new()));
        wire.borrow_mut().set(*bit);
        wire
    }).collect()
}

pub fn fq_from_wires(wires: Wires) -> ark_bn254::Fq {
    fq_from_bits(wires.iter().map(|wire| {wire.borrow().get_value()}).collect())
}

pub fn random_fq2() -> ark_bn254::Fq2 {
    ark_bn254::Fq2::new(random_fq(), random_fq())
}

pub fn bits_from_fq2(u: ark_bn254::Fq2) -> Vec<bool> {
    let mut bits = Vec::new();
    bits.extend(bits_from_fq(u.c0));
    bits.extend(bits_from_fq(u.c1));
    bits
}

pub fn fq2_from_bits(bits: Vec<bool>) -> ark_bn254::Fq2 {
    let bits1 = &bits[0..Fq::N_BITS].to_vec();
    let bits2 = &bits[Fq::N_BITS..Fq::N_BITS*2].to_vec();
    ark_bn254::Fq2::new(fq_from_bits(bits1.clone()), fq_from_bits(bits2.clone()))
}

pub fn wires_for_fq2() -> Wires {
    (0..Fq2::N_BITS).map(|_| { Rc::new(RefCell::new(Wire::new())) }).collect()
}

pub fn wires_set_from_fq2(u: ark_bn254::Fq2) -> Wires {
    bits_from_fq2(u)[0..Fq2::N_BITS].iter().map(|bit| {
        let wire = Rc::new(RefCell::new(Wire::new()));
        wire.borrow_mut().set(*bit);
        wire
    }).collect()
}

pub fn fq2_from_wires(wires: Wires) -> ark_bn254::Fq2 {
    fq2_from_bits(wires.iter().map(|wire| {wire.borrow().get_value()}).collect())
}

pub fn random_fq6() -> ark_bn254::Fq6 {
    ark_bn254::Fq6::new(random_fq2(), random_fq2(), random_fq2())
}

pub fn bits_from_fq6(u: ark_bn254::Fq6) -> Vec<bool> {
    let mut bits = Vec::new();
    bits.extend(bits_from_fq2(u.c0));
    bits.extend(bits_from_fq2(u.c1));
    bits.extend(bits_from_fq2(u.c2));
    bits
}

pub fn fq6_from_bits(bits: Vec<bool>) -> ark_bn254::Fq6 {
    let bits1 = &bits[0..Fq2::N_BITS].to_vec();
    let bits2 = &bits[Fq2::N_BITS..Fq2::N_BITS*2].to_vec();
    let bits3 = &bits[Fq2::N_BITS*2..Fq2::N_BITS*3].to_vec();
    ark_bn254::Fq6::new(fq2_from_bits(bits1.clone()), fq2_from_bits(bits2.clone()), fq2_from_bits(bits3.clone()))
}

pub fn wires_for_fq6() -> Wires {
    (0..Fq6::N_BITS).map(|_| { Rc::new(RefCell::new(Wire::new())) }).collect()
}

pub fn wires_set_from_fq6(u: ark_bn254::Fq6) -> Wires {
    bits_from_fq6(u)[0..Fq6::N_BITS].iter().map(|bit| {
        let wire = Rc::new(RefCell::new(Wire::new()));
        wire.borrow_mut().set(*bit);
        wire
    }).collect()
}

pub fn fq6_from_wires(wires: Wires) -> ark_bn254::Fq6 {
    fq6_from_bits(wires.iter().map(|wire| {wire.borrow().get_value()}).collect())
}

pub fn random_fq12() -> ark_bn254::Fq12 {
    ark_bn254::Fq12::new(random_fq6(), random_fq6())
}

pub fn bits_from_fq12(u: ark_bn254::Fq12) -> Vec<bool> {
    let mut bits = Vec::new();
    bits.extend(bits_from_fq6(u.c0));
    bits.extend(bits_from_fq6(u.c1));
    bits
}

pub fn fq12_from_bits(bits: Vec<bool>) -> ark_bn254::Fq12 {
    let bits1 = &bits[0..Fq6::N_BITS].to_vec();
    let bits2 = &bits[Fq6::N_BITS..Fq6::N_BITS*2].to_vec();
    ark_bn254::Fq12::new(fq6_from_bits(bits1.clone()), fq6_from_bits(bits2.clone()))
}

pub fn wires_for_fq12() -> Wires {
    (0..Fq12::N_BITS).map(|_| { Rc::new(RefCell::new(Wire::new())) }).collect()
}

pub fn wires_set_from_fq12(u: ark_bn254::Fq12) -> Wires {
    bits_from_fq12(u)[0..Fq12::N_BITS].iter().map(|bit| {
        let wire = Rc::new(RefCell::new(Wire::new()));
        wire.borrow_mut().set(*bit);
        wire
    }).collect()
}

pub fn fq12_from_wires(wires: Wires) -> ark_bn254::Fq12 {
    fq12_from_bits(wires.iter().map(|wire| {wire.borrow().get_value()}).collect())
}

pub fn random_g1p() -> ark_bn254::G1Projective {
    let mut prng = ChaCha20Rng::seed_from_u64(rng().random());
    ark_bn254::G1Projective::rand(&mut prng)
}

pub fn bits_from_g1p(u: ark_bn254::G1Projective) -> Vec<bool> {
    let mut bits = Vec::new();
    bits.extend(bits_from_fq(u.x));
    bits.extend(bits_from_fq(u.y));
    bits.extend(bits_from_fq(u.z));
    bits
}

pub fn g1p_from_bits(bits: Vec<bool>) -> ark_bn254::G1Projective {
    let bits1 = &bits[0..Fq::N_BITS].to_vec();
    let bits2 = &bits[Fq::N_BITS..Fq::N_BITS*2].to_vec();
    let bits3 = &bits[Fq::N_BITS*2..Fq::N_BITS*3].to_vec();
    ark_bn254::G1Projective::new(fq_from_bits(bits1.clone()), fq_from_bits(bits2.clone()), fq_from_bits(bits3.clone()))
}

pub fn wires_for_g1p() -> Wires {
    (0..G1Projective::N_BITS).map(|_| { Rc::new(RefCell::new(Wire::new())) }).collect()
}

pub fn wires_set_from_g1p(u: ark_bn254::G1Projective) -> Wires {
    bits_from_g1p(u)[0..G1Projective::N_BITS].iter().map(|bit| {
        let wire = Rc::new(RefCell::new(Wire::new()));
        wire.borrow_mut().set(*bit);
        wire
    }).collect()
}

pub fn g1p_from_wires(wires: Wires) -> ark_bn254::G1Projective {
    g1p_from_bits(wires.iter().map(|wire| {wire.borrow().get_value()}).collect())
}

pub fn random_fr() -> ark_bn254::Fr {
    let u = BigUint::from_bytes_le(&rng().random::<[u8; 32]>()) % Fr::modulus_as_biguint();
    ark_bn254::Fr::from(u)
}

pub fn bits_from_fr(u: ark_bn254::Fr) -> Vec<bool> {
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

pub fn fr_from_bits(bits: Vec<bool>) -> ark_bn254::Fr {
    let zero = BigUint::ZERO;
    let one = BigUint::from(1_u8);
    let mut u = zero.clone();
    for bit in bits.iter().rev() {
        u = u.clone() + u.clone() + if *bit {one.clone()} else {zero.clone()};
    }
    ark_bn254::Fr::from(u)
}

pub fn wires_for_fr() -> Wires {
    (0..Fr::N_BITS).map(|_| { Rc::new(RefCell::new(Wire::new())) }).collect()
}

pub fn wires_set_from_fr(u: ark_bn254::Fr) -> Wires {
    bits_from_fr(u)[0..Fr::N_BITS].iter().map(|bit| {
        let wire = Rc::new(RefCell::new(Wire::new()));
        wire.borrow_mut().set(*bit);
        wire
    }).collect()
}

pub fn fr_from_wires(wires: Wires) -> ark_bn254::Fr {
    fr_from_bits(wires.iter().map(|wire| {wire.borrow().get_value()}).collect())
}

pub fn random_g2p() -> ark_bn254::G2Projective {
    let mut prng = ChaCha20Rng::seed_from_u64(rng().random());
    ark_bn254::G2Projective::rand(&mut prng)
}

pub fn bits_from_g2p(u: ark_bn254::G2Projective) -> Vec<bool> {
    let mut bits = Vec::new();
    bits.extend(bits_from_fq2(u.x));
    bits.extend(bits_from_fq2(u.y));
    bits.extend(bits_from_fq2(u.z));
    bits
}

pub fn g2p_from_bits(bits: Vec<bool>) -> ark_bn254::G2Projective {
    let bits1 = &bits[0..Fq2::N_BITS].to_vec();
    let bits2 = &bits[Fq2::N_BITS..Fq2::N_BITS*2].to_vec();
    let bits3 = &bits[Fq2::N_BITS*2..Fq2::N_BITS*3].to_vec();
    ark_bn254::G2Projective::new(fq2_from_bits(bits1.clone()), fq2_from_bits(bits2.clone()), fq2_from_bits(bits3.clone()))
}

pub fn wires_for_g2p() -> Wires {
    (0..G2Projective::N_BITS).map(|_| { Rc::new(RefCell::new(Wire::new())) }).collect()
}

pub fn wires_set_from_g2p(u: ark_bn254::G2Projective) -> Wires {
    bits_from_g2p(u)[0..G2Projective::N_BITS].iter().map(|bit| {
        let wire = Rc::new(RefCell::new(Wire::new()));
        wire.borrow_mut().set(*bit);
        wire
    }).collect()
}

pub fn g2p_from_wires(wires: Wires) -> ark_bn254::G2Projective {
    g2p_from_bits(wires.iter().map(|wire| {wire.borrow().get_value()}).collect())
}

pub fn bits_from_g2a(u: ark_bn254::G2Affine) -> Vec<bool> {
    let mut bits = Vec::new();
    bits.extend(bits_from_fq2(u.x));
    bits.extend(bits_from_fq2(u.y));
    bits
}

pub fn wires_set_from_g2a(u: ark_bn254::G2Affine) -> Wires {
    bits_from_g2a(u)[0..2*Fq2::N_BITS].iter().map(|bit| {
        let wire = Rc::new(RefCell::new(Wire::new()));
        wire.borrow_mut().set(*bit);
        wire
    }).collect()
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

    #[test]
    fn test_random_fq6() {
        let u = random_fq6();
        println!("u: {:?}", u);
        let b = bits_from_fq6(u.clone());
        let v = fq6_from_bits(b);
        println!("v: {:?}", v);
        assert_eq!(u, v);
    }

    #[test]
    fn test_random_fq12() {
        let u = random_fq12();
        println!("u: {:?}", u);
        let b = bits_from_fq12(u.clone());
        let v = fq12_from_bits(b);
        println!("v: {:?}", v);
        assert_eq!(u, v);
    }

    #[test]
    fn test_random_fr() {
        let u = random_fr();
        println!("u: {:?}", u);
        let b = bits_from_fr(u.clone());
        let v = fr_from_bits(b);
        println!("v: {:?}", v);
        assert_eq!(u, v);
    }

    #[test]
    fn test_random_g1p() {
        let u = random_g1p();
        println!("u: {:?}", u);
        let b = bits_from_g1p(u.clone());
        let v = g1p_from_bits(b);
        println!("v: {:?}", v);
        assert_eq!(u, v);
    }

    #[test]
    fn test_random_g2p() {
        let u = random_g2p();
        println!("u: {:?}", u);
        let b = bits_from_g2p(u.clone());
        let v = g2p_from_bits(b);
        println!("v: {:?}", v);
        assert_eq!(u, v);
    }
}
