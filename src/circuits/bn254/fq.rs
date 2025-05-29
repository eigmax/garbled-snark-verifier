use std::str::FromStr;
use num_bigint::BigUint;
use crate::bag::*;
use super::Fp254Impl;

pub struct Fq;

impl Fp254Impl for Fq {
    const MODULUS: &'static str = "21888242871839275222246405745257275088696311157297823662689037894645226208583";
}

impl Fq {
    pub fn modulus_as_biguint() -> BigUint {
        BigUint::from_str(Self::MODULUS).unwrap()
    }

    pub fn add(input_wires: Vec<Rc<RefCell<Wire>>>) -> (Vec<Rc<RefCell<Wire>>>, Vec<Gate>) {
        todo!()
    }

    pub fn mul(input_wires: Vec<Rc<RefCell<Wire>>>) -> (Vec<Rc<RefCell<Wire>>>, Vec<Gate>) {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use num_bigint::BigUint;
    use rand::{Rng};
    use super::*;

    fn random_fq() -> ark_bn254::Fq {
        let u = BigUint::from_bytes_le(&rand::rng().random::<[u8; 32]>()) % Fq::modulus_as_biguint();
        ark_bn254::Fq::from(u)
    }

    fn bits_from_fq(u: ark_bn254::Fq) -> Vec<bool> {
        let bytes = BigUint::from(u).to_bytes_le();
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

    fn fq_from_bits(bits: Vec<bool>) -> ark_bn254::Fq {
        let zero = BigUint::ZERO;
        let one = BigUint::from(1_u8);
        let mut u = zero.clone();
        for bit in bits.iter().rev() {
            u = u.clone() + u.clone() + if *bit {one.clone()} else {zero.clone()};
        }
        ark_bn254::Fq::from(u)
    }

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
    fn test_fq_add() {
        let a = random_fq();
        let b = random_fq();
        let c = a + b;
        let mut input_wires = Vec::new();
        for bit in bits_from_fq(a) {
            let wire = Rc::new(RefCell::new(Wire::new()));
            wire.borrow_mut().set(bit);
            input_wires.push(wire)
        }
        for bit in bits_from_fq(b) {
            let wire = Rc::new(RefCell::new(Wire::new()));
            wire.borrow_mut().set(bit);
            input_wires.push(wire)
        }
        let (output_wires, gates) = Fq::add(input_wires);
        for mut gate in gates {
            gate.evaluate();
        }
        let d = fq_from_bits(output_wires.iter().map(|output_wire| { output_wire.borrow().get_value() }).collect());
        assert_eq!(c, d);
    }
}
