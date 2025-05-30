use std::str::FromStr;
use num_bigint::BigUint;
use crate::{bag::*, circuits::bigint::{utils::bits_from_biguint, U254}};
use super::Fp254Impl;

pub struct Fq;

impl Fp254Impl for Fq {
    const MODULUS: &'static str = "21888242871839275222246405745257275088696311157297823662689037894645226208583";
}

impl Fq {
    pub fn modulus_as_biguint() -> BigUint {
        BigUint::from_str(Self::MODULUS).unwrap()
    }

    pub fn modulus_as_bits() -> Vec<bool> {
        bits_from_biguint(Fq::modulus_as_biguint())
    }

    pub fn negative_modulus_as_biguint() -> BigUint {
        let p = Fq::modulus_as_biguint();
        let a = BigUint::from_str("2").unwrap().pow(U254::N_BITS.try_into().unwrap());
        a-p
    }

    pub fn negative_modulus_as_bits() -> Vec<bool> {
        bits_from_biguint(Fq::negative_modulus_as_biguint())
    }

    pub fn add(input_wires: Vec<Rc<RefCell<Wire>>>) -> (Vec<Rc<RefCell<Wire>>>, Vec<Gate>) {
        assert_eq!(input_wires.len(),2*U254::N_BITS);
        let mut circuit_gates = Vec::new();
        let (mut wires_1 , gates_1) = U254::add(input_wires);
        let u = wires_1.pop().unwrap();
        let c = Fq::negative_modulus_as_biguint();
        let (mut wires_2 , gates_2) = U254::add_constant(wires_1.clone(), c);
        wires_2.pop();
        let not_u = Rc::new(RefCell::new(Wire::new()));
        let gate_3 = Gate::new(u.clone(), u.clone(), not_u.clone(), "inv".to_string());
        let mut p_wires = Vec::new();
        for bit in Fq::modulus_as_bits() {
            let wire_p = Rc::new(RefCell::new(Wire::new()));
            wire_p.borrow_mut().set(bit);
            p_wires.push(wire_p);
        }
        p_wires.pop();
        p_wires.pop();
        p_wires.extend(wires_1.clone());
        let (v, gates_4) = U254::greater_than(p_wires);
        let selector = Rc::new(RefCell::new(Wire::new()));
        let gate_5 = Gate::new(not_u.clone(), v[0].clone(), selector.clone(), "and".to_string());
        wires_1.extend(wires_2);
        let not_selector = Rc::new(RefCell::new(Wire::new()));
        let gate_x = Gate::new(selector.clone(), selector.clone(), not_selector.clone(), "inv".to_string());
        // wires_1.push(not_selector);
        wires_1.push(selector);
        let (output_wires, gates_6) = U254::select(wires_1);
        circuit_gates.extend(gates_1);
        circuit_gates.extend(gates_2);
        circuit_gates.push(gate_3);
        circuit_gates.extend(gates_4);
        circuit_gates.push(gate_5);
        circuit_gates.push(gate_x);
        circuit_gates.extend(gates_6);
        (output_wires, circuit_gates)
    }

    pub fn mul(input_wires: Vec<Rc<RefCell<Wire>>>) -> (Vec<Rc<RefCell<Wire>>>, Vec<Gate>) {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use crate::circuits::bn254::utils::{bits_from_fq, fq_from_bits, random_fq};
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