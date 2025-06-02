use std::str::FromStr;
use ark_ff::{AdditiveGroup, Field};
use num_bigint::BigUint;
use crate::{bag::*, circuits::{bigint::{utils::bits_from_biguint, U254}, bn254::utils::{bits_from_fq, wires_for_fq}}};
use super::Fp254Impl;

pub struct Fq;

impl Fp254Impl for Fq {
    const MODULUS: &'static str = "21888242871839275222246405745257275088696311157297823662689037894645226208583";
}

impl Fq {
    pub const N_BITS: usize = 254;
    
    pub fn modulus_as_biguint() -> BigUint {
        BigUint::from_str(Self::MODULUS).unwrap()
    }

    pub fn modulus_as_bits() -> Vec<bool> {
        bits_from_biguint(Fq::modulus_as_biguint())
    }

    pub fn not_modulus_as_biguint() -> BigUint {
        let p = Fq::modulus_as_biguint();
        let a = BigUint::from_str("2").unwrap().pow(U254::N_BITS.try_into().unwrap());
        a-p
    }

    pub fn not_modulus_as_bits() -> Vec<bool> {
        bits_from_biguint(Fq::not_modulus_as_biguint())
    }

    pub fn self_or_zero(a: Wires, s: Wirex) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let result = wires_for_fq();
        for i in 0..U254::N_BITS {
            circuit.add(Gate::new(a[i].clone(), s.clone(), result[i].clone(), "and".to_string()));
        }
        circuit.add_wires(result);
        circuit
    }

    pub fn add(a: Wires, b: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        assert_eq!(b.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let mut wires_1 = circuit.extend(U254::add(a, b));
        let u = wires_1.pop().unwrap();
        let c = Fq::not_modulus_as_biguint();
        let mut wires_2 = circuit.extend(U254::add_constant(wires_1.clone(), c));
        wires_2.pop();
        let not_u = Rc::new(RefCell::new(Wire::new()));
        circuit.add(Gate::new(u.clone(), u.clone(), not_u.clone(), "not".to_string()));
        let v = circuit.extend(U254::less_than_constant(wires_1.clone(), Fq::modulus_as_biguint()))[0].clone();
        let s = Rc::new(RefCell::new(Wire::new()));
        circuit.add(Gate::new(not_u.clone(), v.clone(), s.clone(), "and".to_string()));
        let wires_3 = circuit.extend(U254::select(wires_1, wires_2, s));
        circuit.add_wires(wires_3);
        circuit
    }

    pub fn add_constant(a: Wires, b: ark_bn254::Fq) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        if b == ark_bn254::Fq::ZERO {
            circuit.add_wires(a);
            return circuit;
        }

        let mut wires_1 = circuit.extend(U254::add_constant(a.clone(), BigUint::from(b)));
        let u = wires_1.pop().unwrap();
        let c = Fq::not_modulus_as_biguint();
        let mut wires_2 = circuit.extend(U254::add_constant(wires_1.clone(), c));
        wires_2.pop();
        let not_u = Rc::new(RefCell::new(Wire::new()));
        circuit.add(Gate::new(u.clone(), u.clone(), not_u.clone(), "not".to_string()));
        let v = circuit.extend(U254::less_than_constant(wires_1.clone(), Fq::modulus_as_biguint()))[0].clone();
        let s = Rc::new(RefCell::new(Wire::new()));
        circuit.add(Gate::new(not_u.clone(), v.clone(), s.clone(), "and".to_string()));
        let wires_3 = circuit.extend(U254::select(wires_1, wires_2, s));
        circuit.add_wires(wires_3);
        circuit
    }

    pub fn neg(a: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let not_a = wires_for_fq();
        for i in 0..U254::N_BITS {
            circuit.add(Gate::new(a[i].clone(), a[i].clone(), not_a[i].clone(), "not".to_string()));
        }

        let wires = circuit.extend(Fq::add_constant(not_a, ark_bn254::Fq::from(1) - ark_bn254::Fq::from(Fq::not_modulus_as_biguint())));
        circuit.add_wires(wires);
        circuit
    }

    pub fn sub(a: Wires, b: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        assert_eq!(b.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let neg_b = circuit.extend(Fq::neg(b));
        let result = circuit.extend(Fq::add(a, neg_b));
        circuit.add_wires(result);
        circuit
    }

    pub fn double(a: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let shift_wire = Rc::new(RefCell::new(Wire::new()));
        shift_wire.borrow_mut().set(false);
        let mut aa = a.clone();
        let u = aa.pop().unwrap();
        let mut shifted_wires = vec![shift_wire];
        shifted_wires.extend(aa);
        let c = Fq::not_modulus_as_biguint();
        let mut wires_2 = circuit.extend(U254::add_constant(shifted_wires.clone(), c));
        wires_2.pop();
        let not_u = Rc::new(RefCell::new(Wire::new()));
        circuit.add(Gate::new(u.clone(), u.clone(), not_u.clone(), "not".to_string()));
        let v = circuit.extend(U254::less_than_constant(shifted_wires.clone(), Fq::modulus_as_biguint()))[0].clone();
        let s = Rc::new(RefCell::new(Wire::new()));
        circuit.add(Gate::new(not_u.clone(), v.clone(), s.clone(), "and".to_string()));
        let result = circuit.extend(U254::select(shifted_wires, wires_2, s));
        circuit.add_wires(result);
        circuit
    }

    pub fn triple(a: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_2 = circuit.extend(Fq::double(a.clone()));
        let a_3 = circuit.extend(Fq::add(a_2, a));
        circuit.add_wires(a_3);
        circuit
    }

    pub fn mul(a: Wires, b: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        assert_eq!(b.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_or_zero = circuit.extend(Fq::self_or_zero(a.clone(), b[U254::N_BITS - 1].clone()));
        let mut result = a_or_zero.clone();
        for b_wire in b.iter().rev().skip(1) {
            let result_double = circuit.extend(Fq::double(result.clone()));
            let a_or_zero_i = circuit.extend(Fq::self_or_zero(a.clone(), b_wire.clone()));
            result = circuit.extend(Fq::add(result_double, a_or_zero_i));
        }
        circuit.add_wires(result);
        circuit
    }

    pub fn mul_by_constant(a: Wires, b: ark_bn254::Fq) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        if b == ark_bn254::Fq::ONE {
            circuit.add_wires(a);
            return circuit;
        }

        let b_bits = bits_from_fq(b);
        let mut i = U254::N_BITS - 1;
        while !b_bits[i] {
            i -= 1;
        }

        let mut result = a.clone();
        for b_bit in b_bits.iter().rev().skip(U254::N_BITS - i) {
            let result_double = circuit.extend(Fq::double(result.clone()));
            if *b_bit {
                result = circuit.extend(Fq::add(a.clone(), result_double));
            }
            else {
                result = result_double;
            }
        }
        circuit.add_wires(result);
        circuit
    }

    pub fn square(a: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_or_zero = circuit.extend(Fq::self_or_zero(a.clone(), a[U254::N_BITS - 1].clone()));
        let mut result = a_or_zero.clone();
        for a_wire in a.iter().rev().skip(1) {
            let result_double = circuit.extend(Fq::double(result.clone()));
            let a_or_zero_i = circuit.extend(Fq::self_or_zero(a.clone(), a_wire.clone()));
            result = circuit.extend(Fq::add(result_double, a_or_zero_i));
        }
        circuit.add_wires(result);
        circuit
    }
}

#[cfg(test)]
mod tests {
    use crate::circuits::bn254::utils::{fq_from_wires, random_fq, wires_set_from_fq};
    use super::*;

    #[test]
    fn test_fq_add() {
        let a = random_fq();
        let b = random_fq();
        let circuit = Fq::add(wires_set_from_fq(a.clone()), wires_set_from_fq(b.clone()));
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq_from_wires(circuit.0);
        assert_eq!(c, a + b);
    }

    #[test]
    fn test_fq_add_constant() {
        let a = random_fq();
        let b = random_fq();
        let circuit = Fq::add_constant(wires_set_from_fq(a.clone()), b.clone());
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq_from_wires(circuit.0);
        assert_eq!(c, a + b);
    }

    #[test]
    fn test_fq_neg() {
        let a = random_fq();
        let circuit = Fq::neg(wires_set_from_fq(a.clone()));
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq_from_wires(circuit.0);
        assert_eq!(c, -a);
    }

    #[test]
    fn test_fq_sub() {
        let a = random_fq();
        let b = random_fq();
        let circuit = Fq::sub(wires_set_from_fq(a.clone()), wires_set_from_fq(b.clone()));
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq_from_wires(circuit.0);
        assert_eq!(c, a - b);
    }

    #[test]
    fn test_fq_double() {
        let a = random_fq();
        let circuit = Fq::double(wires_set_from_fq(a.clone()));
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq_from_wires(circuit.0);
        assert_eq!(c, a + a);
    }

    #[test]
    fn test_fq_triple() {
        let a = random_fq();
        let circuit = Fq::triple(wires_set_from_fq(a.clone()));
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq_from_wires(circuit.0);
        assert_eq!(c, a + a + a);
    }

    #[test]
    fn test_fq_mul() {
        let a = random_fq();
        let b = random_fq();
        let circuit = Fq::mul(wires_set_from_fq(a.clone()), wires_set_from_fq(b.clone()));
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq_from_wires(circuit.0);
        assert_eq!(c, a * b);
    }

    #[test]
    fn test_fq_mul_by_constant() {
        let a = random_fq();
        let b = random_fq();
        let circuit = Fq::mul_by_constant(wires_set_from_fq(a.clone()), b.clone());
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq_from_wires(circuit.0);
        assert_eq!(c, a * b);
    }

    #[test]
    fn test_fq_square() {
        let a = random_fq();
        let circuit = Fq::square(wires_set_from_fq(a.clone()));
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq_from_wires(circuit.0);
        assert_eq!(c, a * a);
    }
}
