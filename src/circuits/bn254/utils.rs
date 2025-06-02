use num_bigint::BigUint;
use rand::{rng, Rng};
use crate::circuits::bn254::{fq::Fq, fq2::Fq2, fq6::Fq6};
use crate::bag::*;

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
}
