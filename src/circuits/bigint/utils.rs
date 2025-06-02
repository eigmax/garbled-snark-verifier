use std::str::FromStr;
use num_bigint::BigUint;
use rand::{rng, Rng};
use crate::bag::*;
use super::U254;

pub fn random_biguint() -> BigUint {
    BigUint::from_bytes_le(&rng().random::<[u8; 32]>())
}

pub fn random_u254() -> BigUint {
    BigUint::from_bytes_le(&rand::rng().random::<[u8; 32]>()) % BigUint::from_str("2").unwrap().pow(254)
}

pub fn bits_from_biguint(u: BigUint) -> Vec<bool> {
    let mut bytes = u.to_bytes_le();
    for _ in bytes.len()..32 {
        bytes.push(0_u8);
    }
    let mut bits = Vec::new();
    for byte in bytes {
        for i in 0..8 {
            bits.push(((byte >> i) & 1) == 1)
        }
    }
    bits
}

pub fn biguint_from_bits(bits: Vec<bool>) -> BigUint {
    let zero = BigUint::ZERO;
    let one = BigUint::from(1_u8);
    let mut u = zero.clone();
    for bit in bits.iter().rev() {
        u = u.clone() + u.clone() + if *bit {one.clone()} else {zero.clone()};
    }
    u
}

pub fn wires_for_u254() -> Wires {
    (0..U254::N_BITS).map(|_| { Rc::new(RefCell::new(Wire::new())) }).collect()
}

pub fn wires_set_from_u254(u: BigUint) -> Wires {
    bits_from_biguint(u)[0..U254::N_BITS].iter().map(|bit| {
        let wire = Rc::new(RefCell::new(Wire::new()));
        wire.borrow_mut().set(*bit);
        wire
    }).collect()
}

pub fn biguint_from_wires(wires: Wires) -> BigUint {
    biguint_from_bits(wires.iter().map(|wire| {wire.borrow().get_value()}).collect())
}

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn test_random_biguint() {
        let u = random_biguint();
        println!("u: {:?}", u);
        let b = bits_from_biguint(u.clone());
        let v = biguint_from_bits(b);
        println!("v: {:?}", v);
        assert_eq!(u, v);
    }
}
