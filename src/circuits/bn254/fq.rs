use std::str::FromStr;
use ark_ff::{AdditiveGroup, Field};
use num_bigint::BigUint;
use crate::{bag::*, circuits::{bigint::{utils::bits_from_biguint, U254}, bn254::utils::{bits_from_fq, wires_for_fq, wires_set_from_fq}}};
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
        let a = BigUint::from_str("2").unwrap().pow(Self::N_BITS.try_into().unwrap());
        a-p
    }

    pub fn not_modulus_as_bits() -> Vec<bool> {
        bits_from_biguint(Fq::not_modulus_as_biguint())
    }

    pub fn self_or_zero(a: Wires, s: Wirex) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let result = wires_for_fq();
        for i in 0..Self::N_BITS {
            circuit.add(Gate::and(a[i].clone(), s.clone(), result[i].clone()));
        }
        circuit.add_wires(result);
        circuit
    }

    pub fn equal(a: Wires, b: Wires) -> Circuit {
        U254::equal(a, b)
    }

    pub fn equal_constant(a: Wires, b: ark_bn254::Fq) -> Circuit {
        U254::equal_constant(a, BigUint::from(b))
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
        circuit.add(Gate::not(u.clone(), not_u.clone()));
        let v = circuit.extend(U254::less_than_constant(wires_1.clone(), Fq::modulus_as_biguint()))[0].clone();
        let s = Rc::new(RefCell::new(Wire::new()));
        circuit.add(Gate::and(not_u.clone(), v.clone(), s.clone()));
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
        circuit.add(Gate::not(u.clone(), not_u.clone()));
        let v = circuit.extend(U254::less_than_constant(wires_1.clone(), Fq::modulus_as_biguint()))[0].clone();
        let s = Rc::new(RefCell::new(Wire::new()));
        circuit.add(Gate::and(not_u.clone(), v.clone(), s.clone()));
        let wires_3 = circuit.extend(U254::select(wires_1, wires_2, s));
        circuit.add_wires(wires_3);
        circuit
    }

    pub fn neg(a: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let not_a = wires_for_fq();
        for i in 0..Self::N_BITS {
            circuit.add(Gate::not(a[i].clone(), not_a[i].clone()));
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
        let x = a[0].clone();
        let not_x = Rc::new(RefCell::new(Wire::new()));
        circuit.add(Gate::not(x.clone(), not_x.clone())); 
        circuit.add(Gate::and(x.clone(), not_x.clone(), shift_wire.clone())); 
        let mut aa = a.clone();
        let u = aa.pop().unwrap();
        let mut shifted_wires = vec![shift_wire];
        shifted_wires.extend(aa);
        let c = Fq::not_modulus_as_biguint();
        let mut wires_2 = circuit.extend(U254::add_constant(shifted_wires.clone(), c));
        wires_2.pop();
        let not_u = Rc::new(RefCell::new(Wire::new()));
        circuit.add(Gate::not(u.clone(), not_u.clone()));
        let v = circuit.extend(U254::less_than_constant(shifted_wires.clone(), Fq::modulus_as_biguint()))[0].clone();
        let s = Rc::new(RefCell::new(Wire::new()));
        circuit.add(Gate::and(not_u.clone(), v.clone(), s.clone()));
        let result = circuit.extend(U254::select(shifted_wires, wires_2, s));
        circuit.add_wires(result);
        circuit
    }

    pub fn half(a: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let selector = a[0].clone();
        let wires_1 = circuit.extend(U254::half(a.clone()));
        let wires_2 =  circuit.extend(Fq::add_constant(wires_1.clone(), ark_bn254::Fq::from( ark_bn254::Fq::from(1))/ ark_bn254::Fq::from(2) ));
        let result = circuit.extend(U254::select(wires_2, wires_1, selector));
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

        let a_or_zero = circuit.extend(Fq::self_or_zero(a.clone(), b[Self::N_BITS - 1].clone()));
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
        let mut i = Self::N_BITS - 1;
        while !b_bits[i] {
            i -= 1;
        }

        let mut result = a.clone();
        for b_bit in b_bits.iter().rev().skip(Self::N_BITS - i) {
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

        let a_or_zero = circuit.extend(Fq::self_or_zero(a.clone(), a[Self::N_BITS - 1].clone()));
        let mut result = a_or_zero.clone();
        for a_wire in a.iter().rev().skip(1) {
            let result_double = circuit.extend(Fq::double(result.clone()));
            let a_or_zero_i = circuit.extend(Fq::self_or_zero(a.clone(), a_wire.clone()));
            result = circuit.extend(Fq::add(result_double, a_or_zero_i));
        }
        circuit.add_wires(result);
        circuit
    }

    pub fn inverse(a: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let wires_1 = circuit.extend(U254::odd_part(a.clone()));
        let odd_part = wires_1[0..Fq::N_BITS].to_vec();
        let mut even_part = wires_1[Fq::N_BITS..2*Fq::N_BITS].to_vec();

        // initialize value for wires 
        let neg_odd_part = circuit.extend(Fq::neg(odd_part.clone()));
        let mut u = circuit.extend(Fq::half(neg_odd_part));
        let mut v = odd_part;
        let mut k = wires_set_from_fq(ark_bn254::Fq::ONE);
        let mut r = wires_set_from_fq(ark_bn254::Fq::ONE);
        let mut s = wires_set_from_fq(ark_bn254::Fq::from(2));

        for _ in 0..2*Fq::N_BITS {
            let x1x = u[0].clone();
            let x2x = v[0].clone();
            let x1 = Rc::new(RefCell::new(Wire::new()));
            let x2 = Rc::new(RefCell::new(Wire::new()));
            circuit.add(Gate::not(x1x.clone(), x1.clone()));
            circuit.add(Gate::not(x2x.clone(), x2.clone()));
            let x3 = circuit.extend(U254::greater_than(u.clone(), v.clone()))[0].clone();

            let p1 = x1.clone();
            let not_x1 = Rc::new(RefCell::new(Wire::new()));
            circuit.add(Gate::not(x1.clone(), not_x1.clone()));
            let p2 = Rc::new(RefCell::new(Wire::new()));
            circuit.add(Gate::and(not_x1.clone(), x2.clone(), p2.clone()));
            let p3 = Rc::new(RefCell::new(Wire::new()));
            let not_x2= Rc::new(RefCell::new(Wire::new()));
            circuit.add(Gate::not(x2, not_x2.clone()));
            let wires_2 = Rc::new(RefCell::new(Wire::new()));
            circuit.add(Gate::and(not_x1.clone(), not_x2.clone(), wires_2.clone()));
            circuit.add(Gate::and(wires_2.clone(), x3.clone(), p3.clone()));
            let p4 = Rc::new(RefCell::new(Wire::new()));
            let not_x3= Rc::new(RefCell::new(Wire::new()));
            circuit.add(Gate::not(x3.clone(), not_x3.clone()));
            circuit.add(Gate::and(wires_2, not_x3, p4.clone()));

            //part1 
            let u1 = circuit.extend(Fq::half(u.clone()));
            let v1 = v.clone();
            let r1 = r.clone();
            let s1 = circuit.extend(Fq::double(s.clone()));
            let k1 = circuit.extend(Fq::add_constant(k.clone(), ark_bn254::Fq::ONE));

            // part2 
            let u2 = u.clone();
            let v2 = circuit.extend(Fq::half(v.clone()));
            let r2 = circuit.extend(Fq::double(r.clone()));
            let s2 = s.clone();
            let k2 = circuit.extend(Fq::add_constant(k.clone(), ark_bn254::Fq::ONE));

            // part3
            let u3 = circuit.extend(Fq::sub(u1.clone(), v2.clone()));
            let v3 = v.clone();
            let r3 = circuit.extend(Fq::add(r.clone(), s.clone()));
            let s3 = circuit.extend(Fq::double(s.clone()));
            let k3 = circuit.extend(Fq::add_constant(k.clone(), ark_bn254::Fq::ONE));

            // part4
            let u4 = u.clone();
            let v4 = circuit.extend(Fq::sub(v2.clone(), u1.clone()));
            let r4 = circuit.extend(Fq::double(r.clone()));
            let s4 = circuit.extend(Fq::add(r.clone(), s.clone()));
            let k4 = circuit.extend(Fq::add_constant(k.clone(), ark_bn254::Fq::ONE));

            // calculate new u 
            let wire_u_1 = circuit.extend(Fq::self_or_zero(u1.clone(), p1.clone()));
            let wire_u_2 = circuit.extend(Fq::self_or_zero(u2.clone(), p2.clone()));
            let wire_u_3 = circuit.extend(Fq::self_or_zero(u3.clone(), p3.clone()));
            let wire_u_4 = circuit.extend(Fq::self_or_zero(u4.clone(), p4.clone()));

            let add_u_1 = circuit.extend(Fq::add(wire_u_1, wire_u_2));
            let add_u_2 = circuit.extend(Fq::add(add_u_1, wire_u_3));
            let new_u = circuit.extend(Fq::add(add_u_2, wire_u_4));

            // calculate new v 
            let wire_v_1 = circuit.extend(Fq::self_or_zero(v1.clone(), p1.clone()));
            let wire_v_2 = circuit.extend(Fq::self_or_zero(v2.clone(), p2.clone()));
            let wire_v_3 = circuit.extend(Fq::self_or_zero(v3.clone(), p3.clone()));
            let wire_v_4 = circuit.extend(Fq::self_or_zero(v4.clone(), p4.clone()));

            let add_v_1 = circuit.extend(Fq::add(wire_v_1, wire_v_2));
            let add_v_2 = circuit.extend(Fq::add(add_v_1, wire_v_3));
            let new_v = circuit.extend(Fq::add(add_v_2, wire_v_4));

            // calculate new r
            let wire_r_1 = circuit.extend(Fq::self_or_zero(r1.clone(), p1.clone()));
            let wire_r_2 = circuit.extend(Fq::self_or_zero(r2.clone(), p2.clone()));
            let wire_r_3 = circuit.extend(Fq::self_or_zero(r3.clone(), p3.clone()));
            let wire_r_4 = circuit.extend(Fq::self_or_zero(r4.clone(), p4.clone()));

            let add_r_1 = circuit.extend(Fq::add(wire_r_1, wire_r_2));
            let add_r_2 = circuit.extend(Fq::add(add_r_1, wire_r_3));
            let new_r = circuit.extend(Fq::add(add_r_2, wire_r_4));

            // calculate new s
            let wire_s_1 = circuit.extend(Fq::self_or_zero(s1.clone(), p1.clone()));
            let wire_s_2 = circuit.extend(Fq::self_or_zero(s2.clone(), p2.clone()));
            let wire_s_3 = circuit.extend(Fq::self_or_zero(s3.clone(), p3.clone()));
            let wire_s_4 = circuit.extend(Fq::self_or_zero(s4.clone(), p4.clone()));

            let add_s_1 = circuit.extend(Fq::add(wire_s_1, wire_s_2));
            let add_s_2 = circuit.extend(Fq::add(add_s_1, wire_s_3));
            let new_s = circuit.extend(Fq::add(add_s_2, wire_s_4));

            // calculate new k
            let wire_k_1 = circuit.extend(Fq::self_or_zero(k1.clone(), p1.clone()));
            let wire_k_2 = circuit.extend(Fq::self_or_zero(k2.clone(), p2.clone()));
            let wire_k_3 = circuit.extend(Fq::self_or_zero(k3.clone(), p3.clone()));
            let wire_k_4 = circuit.extend(Fq::self_or_zero(k4.clone(), p4.clone()));

            let add_k_1 = circuit.extend(Fq::add(wire_k_1, wire_k_2));
            let add_k_2 = circuit.extend(Fq::add(add_k_1, wire_k_3));
            let new_k = circuit.extend(Fq::add(add_k_2, wire_k_4));

            // set new values 

            let v_equals_one = circuit.extend(U254::equal_constant(v.clone(), BigUint::from_str("1").unwrap()))[0].clone();
            u = circuit.extend(U254::select(u, new_u, v_equals_one.clone()));
            v = circuit.extend(U254::select(v.clone(), new_v, v_equals_one.clone()));
            r = circuit.extend(U254::select(r, new_r, v_equals_one.clone()));
            s = circuit.extend(U254::select(s.clone(), new_s, v_equals_one.clone()));
            k = circuit.extend(U254::select(k, new_k, v_equals_one.clone()));
        }

        // divide result by even part
        for _ in 0..Fq::N_BITS{
            let updated_s = circuit.extend(Fq::half(s.clone()));
            let updated_even_part = circuit.extend(Fq::half(even_part.clone()));
            let selector = circuit.extend(Fq::equal_constant(even_part.clone(), ark_bn254::Fq::ONE))[0].clone();
            s = circuit.extend(U254::select(s.clone(), updated_s, selector.clone()));
            even_part= circuit.extend(U254::select(even_part, updated_even_part, selector.clone()));
        }

        // divide result by 2^k
        for _ in 0..2*Fq::N_BITS{
            let updated_s = circuit.extend(Fq::half(s.clone()));
            let updated_k = circuit.extend(Fq::add_constant(k.clone(),   ark_bn254::Fq::from(-1)));
            let selector = circuit.extend(Fq::equal_constant(k.clone(), ark_bn254::Fq::ZERO));
            s = circuit.extend(U254::select(s, updated_s, selector[0].clone()));
            k = circuit.extend(U254::select(k, updated_k, selector[0].clone()));
        }
        circuit.add_wires(s.clone());
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
    fn test_fq_half() {
        let a = random_fq();
        let circuit = Fq::half(wires_set_from_fq(a.clone()));
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq_from_wires(circuit.0);
        assert_eq!(c + c , a);
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

    #[test]
    fn test_fq_inverse() {
        let a = random_fq();
        let circuit = Fq::inverse(wires_set_from_fq(a.clone()));
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq_from_wires(circuit.0);
        assert_eq!(c*a , ark_bn254::Fq::ONE);
    }
}
