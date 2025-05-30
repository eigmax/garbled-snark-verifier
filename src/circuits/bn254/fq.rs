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
    use crate::circuits::bn254::utils::tests::{bits_from_fq, fq_from_bits, random_fq};
    use super::*;

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
