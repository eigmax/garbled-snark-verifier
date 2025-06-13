use std::iter::zip;
use crate::{bag::*, circuits::bn254::{fp254impl::Fp254Impl, fq::Fq, fq2::Fq2, fq6::Fq6}};
use ark_ff::{Field, Fp12Config};

pub struct Fq12;

impl Fq12 {
    pub const N_BITS: usize = 2 * Fq6::N_BITS;

    pub fn as_montgomery(a: ark_bn254::Fq12) -> ark_bn254::Fq12 {
        ark_bn254::Fq12::new(Fq6::as_montgomery(a.c0), Fq6::as_montgomery(a.c1))
    }

    pub fn equal_constant(a: Wires, b: ark_bn254::Fq12) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a0 = a[0*Fq::N_BITS..1*Fq::N_BITS].to_vec();
        let a1 = a[1*Fq::N_BITS..2*Fq::N_BITS].to_vec();
        let a2 = a[2*Fq::N_BITS..3*Fq::N_BITS].to_vec();
        let a3 = a[3*Fq::N_BITS..4*Fq::N_BITS].to_vec();
        let a4 = a[4*Fq::N_BITS..5*Fq::N_BITS].to_vec();
        let a5 = a[5*Fq::N_BITS..6*Fq::N_BITS].to_vec();
        let a6 = a[6*Fq::N_BITS..7*Fq::N_BITS].to_vec();
        let a7 = a[7*Fq::N_BITS..8*Fq::N_BITS].to_vec();
        let a8 = a[8*Fq::N_BITS..9*Fq::N_BITS].to_vec();
        let a9 = a[9*Fq::N_BITS..10*Fq::N_BITS].to_vec();
        let a10 = a[10*Fq::N_BITS..11*Fq::N_BITS].to_vec();
        let a11 = a[11*Fq::N_BITS..12*Fq::N_BITS].to_vec();

        let mut results = Vec::new();

        for (x, y) in zip([a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11], b.to_base_prime_field_elements()) {
            let result = circuit.extend(Fq::equal_constant(x, y))[0].clone();
            results.push(result);
        }

        let mut wire = results[0].clone();

        for next in results[1..].to_vec() {
            let new_wire = Rc::new(RefCell::new(Wire::new()));
            circuit.add(Gate::and(wire, next, new_wire.clone()));
            wire = new_wire;
        }

        circuit.add_wire(wire);

        circuit
    }

    pub fn equal_constant_evaluate(a: Wires, b: ark_bn254::Fq12) -> (Wires, GateCount) {
        let circuit = Fq12::equal_constant(a, b);
        let n = circuit.gate_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        (circuit.0, n)
    }

    pub fn add(a: Wires, b: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        assert_eq!(b.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq6::N_BITS].to_vec();
        let a_c1 = a[Fq6::N_BITS..2*Fq6::N_BITS].to_vec();
        let b_c0 = b[0..Fq6::N_BITS].to_vec();
        let b_c1 = b[Fq6::N_BITS..2*Fq6::N_BITS].to_vec();

        let wires_1 = circuit.extend(Fq6::add(a_c0, b_c0));
        let wires_2 = circuit.extend(Fq6::add(a_c1, b_c1));
        circuit.add_wires(wires_1);
        circuit.add_wires(wires_2);
        circuit
    }

    pub fn neg(a: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq6::N_BITS].to_vec();
        let a_c1 = a[Fq6::N_BITS..2*Fq6::N_BITS].to_vec();

        let wires_1 = circuit.extend(Fq6::neg(a_c0));
        let wires_2 = circuit.extend(Fq6::neg(a_c1));
        circuit.add_wires(wires_1);
        circuit.add_wires(wires_2);
        circuit
    }

    pub fn sub(a: Wires, b: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        assert_eq!(b.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq6::N_BITS].to_vec();
        let a_c1 = a[Fq6::N_BITS..2*Fq6::N_BITS].to_vec();
        let b_c0 = b[0..Fq6::N_BITS].to_vec();
        let b_c1 = b[Fq6::N_BITS..2*Fq6::N_BITS].to_vec();

        let wires_1 = circuit.extend(Fq6::sub(a_c0, b_c0));
        let wires_2 = circuit.extend(Fq6::sub(a_c1, b_c1));
        circuit.add_wires(wires_1);
        circuit.add_wires(wires_2);
        circuit
    }

    pub fn double(a: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq6::N_BITS].to_vec();
        let a_c1 = a[Fq6::N_BITS..2*Fq6::N_BITS].to_vec();

        let wires_1 = circuit.extend(Fq6::double(a_c0));
        let wires_2 = circuit.extend(Fq6::double(a_c1));
        circuit.add_wires(wires_1);
        circuit.add_wires(wires_2);
        circuit
    }

    pub fn mul(a: Wires, b: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        assert_eq!(b.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq6::N_BITS].to_vec();
        let a_c1 = a[Fq6::N_BITS..2*Fq6::N_BITS].to_vec();
        let b_c0 = b[0..Fq6::N_BITS].to_vec();
        let b_c1 = b[Fq6::N_BITS..2*Fq6::N_BITS].to_vec();

        let wires_1 = circuit.extend(Fq6::add(a_c0.clone(), a_c1.clone()));
        let wires_2 = circuit.extend(Fq6::add(b_c0.clone(), b_c1.clone()));
        let wires_3 = circuit.extend(Fq6::mul(a_c0.clone(), b_c0.clone()));
        let wires_4 = circuit.extend(Fq6::mul(a_c1.clone(), b_c1.clone()));
        let wires_5 = circuit.extend(Fq6::add(wires_3.clone(), wires_4.clone()));
        let wires_6 = circuit.extend(Fq6::mul_by_nonresidue(wires_4.clone()));
        let wires_7 = circuit.extend(Fq6::add(wires_6.clone(), wires_3.clone()));
        let wires_8 = circuit.extend(Fq6::mul(wires_1.clone(), wires_2.clone()));
        let wires_9 = circuit.extend(Fq6::sub(wires_8.clone(), wires_5.clone()));
        circuit.add_wires(wires_7);
        circuit.add_wires(wires_9);
        circuit
    }

    pub fn mul_montgomery(a: Wires, b: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        assert_eq!(b.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq6::N_BITS].to_vec();
        let a_c1 = a[Fq6::N_BITS..2*Fq6::N_BITS].to_vec();
        let b_c0 = b[0..Fq6::N_BITS].to_vec();
        let b_c1 = b[Fq6::N_BITS..2*Fq6::N_BITS].to_vec();

        let wires_1 = circuit.extend(Fq6::add(a_c0.clone(), a_c1.clone()));
        let wires_2 = circuit.extend(Fq6::add(b_c0.clone(), b_c1.clone()));
        let wires_3 = circuit.extend(Fq6::mul_montgomery(a_c0.clone(), b_c0.clone()));
        let wires_4 = circuit.extend(Fq6::mul_montgomery(a_c1.clone(), b_c1.clone()));
        let wires_5 = circuit.extend(Fq6::add(wires_3.clone(), wires_4.clone()));
        let wires_6 = circuit.extend(Fq6::mul_by_nonresidue(wires_4.clone()));
        let wires_7 = circuit.extend(Fq6::add(wires_6.clone(), wires_3.clone()));
        let wires_8 = circuit.extend(Fq6::mul_montgomery(wires_1.clone(), wires_2.clone()));
        let wires_9 = circuit.extend(Fq6::sub(wires_8.clone(), wires_5.clone()));
        circuit.add_wires(wires_7);
        circuit.add_wires(wires_9);
        circuit
    }

    pub fn mul_evaluate(a: Wires, b: Wires) -> (Wires, GateCount) {
        let circuit = Fq12::mul(a, b);
        let n = circuit.gate_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        (circuit.0, n)
    }

    pub fn mul_by_constant(a: Wires, b: ark_bn254::Fq12) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq6::N_BITS].to_vec();
        let a_c1 = a[Fq6::N_BITS..2*Fq6::N_BITS].to_vec();

        let wires_1 = circuit.extend(Fq6::add(a_c0.clone(), a_c1.clone()));
        let wires_2 = circuit.extend(Fq6::mul_by_constant(a_c0.clone(), b.c0.clone()));
        let wires_3 = circuit.extend(Fq6::mul_by_constant(a_c1.clone(), b.c1.clone()));
        let wires_4 = circuit.extend(Fq6::add(wires_2.clone(), wires_3.clone()));
        let wires_5 = circuit.extend(Fq6::mul_by_nonresidue(wires_3.clone()));
        let wires_6 = circuit.extend(Fq6::add(wires_5.clone(), wires_2.clone()));
        let wires_7 = circuit.extend(Fq6::mul_by_constant(wires_1.clone(), b.c0 + b.c1));
        let wires_8 = circuit.extend(Fq6::sub(wires_7.clone(), wires_4.clone()));
        circuit.add_wires(wires_6);
        circuit.add_wires(wires_8);
        circuit
    }

    pub fn mul_by_34(a: Wires, c3: Wires, c4: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        assert_eq!(c3.len(), Fq2::N_BITS);
        assert_eq!(c4.len(), Fq2::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq6::N_BITS].to_vec();
        let a_c1 = a[Fq6::N_BITS..2*Fq6::N_BITS].to_vec();

        let wires_1 = circuit.extend(Fq6::mul_by_01(a_c1.clone(), c3.clone(), c4.clone()));
        let wires_2 = circuit.extend(Fq6::mul_by_nonresidue(wires_1.clone()));
        let c0 = circuit.extend(Fq6::add(wires_2.clone(), a_c0.clone()));
        let wires_3 = circuit.extend(Fq6::add(a_c0.clone(), a_c1.clone()));
        let wires_4 = circuit.extend(Fq2::add_constant(c3.clone(), ark_bn254::Fq2::ONE));
        let wires_5 = circuit.extend(Fq6::mul_by_01(wires_3.clone(), wires_4.clone(), c4.clone()));
        let wires_6 = circuit.extend(Fq6::add(wires_1, a_c0));
        let c1 = circuit.extend(Fq6::sub(wires_5, wires_6));
        circuit.add_wires(c0);
        circuit.add_wires(c1);
        circuit
    }

    pub fn mul_by_034(a: Wires, c0: Wires, c3: Wires, c4: Wires)-> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        assert_eq!(c0.len(), Fq2::N_BITS);
        assert_eq!(c3.len(), Fq2::N_BITS);
        assert_eq!(c4.len(), Fq2::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq6::N_BITS].to_vec();
        let a_c1 = a[Fq6::N_BITS..2*Fq6::N_BITS].to_vec();

        let wires_1 = circuit.extend(Fq6::mul_by_01(a_c1.clone(), c3.clone(), c4.clone()));
        let wires_2 = circuit.extend(Fq6::mul_by_nonresidue(wires_1.clone()));
        let wires_3 = circuit.extend(Fq6::mul_by_fq2(a_c0.clone(), c0.clone()));
        let new_c0 = circuit.extend(Fq6::add(wires_2.clone(), wires_3.clone()));
        let wires_4 = circuit.extend(Fq6::add(a_c0.clone(), a_c1.clone()));
        let wires_5 = circuit.extend(Fq2::add(c3.clone(), c0.clone()));
        let wires_6 = circuit.extend(Fq6::mul_by_01(wires_4.clone(), wires_5.clone(), c4.clone()));
        let wires_7 = circuit.extend(Fq6::add(wires_1, wires_3));
        let new_c1 = circuit.extend(Fq6::sub(wires_6, wires_7));

        circuit.add_wires(new_c0);
        circuit.add_wires(new_c1);
        circuit
    }

    pub fn mul_by_034_constant4(a: Wires, c0: Wires, c3: Wires, c4: ark_bn254::Fq2)-> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        assert_eq!(c0.len(), Fq2::N_BITS);
        assert_eq!(c3.len(), Fq2::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq6::N_BITS].to_vec();
        let a_c1 = a[Fq6::N_BITS..2*Fq6::N_BITS].to_vec();

        let wires_1 = circuit.extend(Fq6::mul_by_01_constant1(a_c1.clone(), c3.clone(), c4.clone()));
        let wires_2 = circuit.extend(Fq6::mul_by_nonresidue(wires_1.clone()));
        let wires_3 = circuit.extend(Fq6::mul_by_fq2(a_c0.clone(), c0.clone()));
        let new_c0 = circuit.extend(Fq6::add(wires_2.clone(), wires_3.clone()));
        let wires_4 = circuit.extend(Fq6::add(a_c0.clone(), a_c1.clone()));
        let wires_5 = circuit.extend(Fq2::add(c3.clone(), c0.clone()));
        let wires_6 = circuit.extend(Fq6::mul_by_01_constant1(wires_4.clone(), wires_5.clone(), c4.clone()));
        let wires_7 = circuit.extend(Fq6::add(wires_1, wires_3));
        let new_c1 = circuit.extend(Fq6::sub(wires_6, wires_7));

        circuit.add_wires(new_c0);
        circuit.add_wires(new_c1);
        circuit
    }

    pub fn square(a: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();
        let a_c0 = a[0..Fq6::N_BITS].to_vec();
        let a_c1 = a[Fq6::N_BITS..2*Fq6::N_BITS].to_vec();
        let wires_1 = circuit.extend(Fq6::add(a_c0.clone(), a_c1.clone()));
        let wires_2 = circuit.extend(Fq6::square(a_c0.clone()));
        let wires_3 = circuit.extend(Fq6::square(a_c1.clone()));
        let wires_4 = circuit.extend(Fq6::add(wires_2.clone(), wires_3.clone()));
        let wires_5 = circuit.extend(Fq6::mul_by_nonresidue(wires_3.clone()));
        let wires_6 = circuit.extend(Fq6::add(wires_5.clone(), wires_2.clone()));
        let wires_7 = circuit.extend(Fq6::mul(wires_1.clone(), wires_1.clone()));
        let wires_8 = circuit.extend(Fq6::sub(wires_7.clone(), wires_4.clone()));
        circuit.add_wires(wires_6);
        circuit.add_wires(wires_8);
        circuit
    }

    pub fn square_evaluate(a: Wires) -> (Wires, GateCount) {
        let circuit = Fq12::square(a);
        let n = circuit.gate_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        (circuit.0, n)
    }
  
    pub fn inverse(a: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();
        let a_c0 = a[0..Fq6::N_BITS].to_vec();
        let a_c1 = a[Fq6::N_BITS..2*Fq6::N_BITS].to_vec();
        let a_c0_square = circuit.extend(Fq6::square(a_c0.clone()));
        let a_c1_square = circuit.extend(Fq6::square(a_c1.clone()));
        let a_c1_square_beta = circuit.extend(Fq6::mul_by_nonresidue(a_c1_square.clone()));
        let norm = circuit.extend(Fq6::sub(a_c0_square, a_c1_square_beta));
        let inverse_norm = circuit.extend(Fq6::inverse(norm));
        let res_c0 = circuit.extend(Fq6::mul(a_c0, inverse_norm.clone()));
        let neg_a_c1 = circuit.extend(Fq6::neg(a_c1));
        let res_c1 = circuit.extend(Fq6::mul(inverse_norm, neg_a_c1));

        circuit.add_wires(res_c0);
        circuit.add_wires(res_c1);
        circuit
    }

    pub fn frobenius(a: Wires, i: usize) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq6::N_BITS].to_vec();
        let a_c1 = a[Fq6::N_BITS..2*Fq6::N_BITS].to_vec();

        let frobenius_a_c0 = circuit.extend(Fq6::frobenius(a_c0, i));
        let frobenius_a_c1 = circuit.extend(Fq6::frobenius(a_c1, i));

        let result = circuit.extend(Fq6::mul_by_constant_fq2(frobenius_a_c1, ark_bn254::Fq12Config::FROBENIUS_COEFF_FP12_C1[i % ark_bn254::Fq12Config::FROBENIUS_COEFF_FP12_C1.len()]));
        circuit.0.extend(frobenius_a_c0);
        circuit.0.extend(result);
        circuit
    }

    pub fn frobenius_evaluate(a: Wires, i: usize) -> (Wires, GateCount) {
        let circuit = Fq12::frobenius(a, i);
        let n = circuit.gate_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        (circuit.0, n)
    }

    pub fn conjugate(a: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq6::N_BITS].to_vec();
        let a_c1 = a[Fq6::N_BITS..2*Fq6::N_BITS].to_vec();

        let new_a_c1 = circuit.extend(Fq6::neg(a_c1));

        circuit.0.extend(a_c0);
        circuit.0.extend(new_a_c1);
        circuit
    }

    pub fn conjugate_evaluate(a: Wires) -> (Wires, GateCount) {
        let circuit = Fq12::conjugate(a);
        let n = circuit.gate_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        (circuit.0, n)
    }
}

#[cfg(test)]
mod tests {
    use ark_ff::Field;
    use serial_test::serial;
    use crate::circuits::bn254::utils::{fq12_from_wires, random_fq12, random_fq2, wires_set_from_fq12, wires_set_from_fq2};
    use super::*;

    #[test]
    fn test_fq12_equal_constant() {
        let a = random_fq12();
        let b = random_fq12();
        let circuit = Fq12::equal_constant(wires_set_from_fq12(a.clone()), b);
        circuit.gate_counts().print();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let result = circuit.0[0].clone().borrow().get_value();
        assert_eq!(result, a == b);

        let circuit = Fq12::equal_constant(wires_set_from_fq12(a.clone()), a);
        circuit.gate_counts().print();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let result = circuit.0[0].clone().borrow().get_value();
        assert!(result);
    }

    #[test]
    fn test_fq12_add() {
        let a = random_fq12();
        let b = random_fq12();
        let circuit = Fq12::add(wires_set_from_fq12(a.clone()), wires_set_from_fq12(b.clone()));
        circuit.gate_counts().print();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq12_from_wires(circuit.0);
        assert_eq!(c, a + b);
    }

    #[test]
    fn test_fq12_neg() {
        let a = random_fq12();
        let circuit = Fq12::neg(wires_set_from_fq12(a.clone()));
        circuit.gate_counts().print();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq12_from_wires(circuit.0);
        assert_eq!(c, -a);
    }

    #[test]
    fn test_fq12_sub() {
        let a = random_fq12();
        let b = random_fq12();
        let circuit = Fq12::sub(wires_set_from_fq12(a.clone()), wires_set_from_fq12(b.clone()));
        circuit.gate_counts().print();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq12_from_wires(circuit.0);
        assert_eq!(c, a - b);
    }

    #[test]
    fn test_fq12_double() {
        let a = random_fq12();
        let circuit = Fq12::double(wires_set_from_fq12(a.clone()));
        circuit.gate_counts().print();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq12_from_wires(circuit.0);
        assert_eq!(c, a + a);
    }

    #[test]
    #[serial]
    fn test_fq12_mul() {
        let a = random_fq12();
        let b = random_fq12();
        let circuit = Fq12::mul(wires_set_from_fq12(a.clone()), wires_set_from_fq12(b.clone()));
        circuit.gate_counts().print();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq12_from_wires(circuit.0);
        assert_eq!(c, a * b);
    }

    #[test]
    #[serial]
    fn test_fq12_mul_montgomery() {
        let a = random_fq12();
        let b = random_fq12();
        let circuit = Fq12::mul_montgomery(wires_set_from_fq12(Fq12::as_montgomery(a.clone())), wires_set_from_fq12(Fq12::as_montgomery(b.clone())));
        circuit.gate_counts().print();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq12_from_wires(circuit.0);
        assert_eq!(c, Fq12::as_montgomery(a * b));
    }

    #[test]
    #[serial]
    fn test_fq12_mul_by_constant() {
        let a = random_fq12();
        let b = random_fq12();
        let circuit = Fq12::mul_by_constant(wires_set_from_fq12(a.clone()), b.clone());
        circuit.gate_counts().print();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq12_from_wires(circuit.0);
        assert_eq!(c, a * b);
    }

    #[test]
    #[serial]
    fn test_fq12_mul_by_34() {
        let a = random_fq12();
        let c3 = random_fq2();
        let c4 = random_fq2();
        let circuit = Fq12::mul_by_34(wires_set_from_fq12(a.clone()), wires_set_from_fq2(c3.clone()), wires_set_from_fq2(c4.clone()));
        circuit.gate_counts().print();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq12_from_wires(circuit.0);
        let mut b = a;
        b.mul_by_034(&ark_bn254::Fq2::ONE, &c3, &c4);
        assert_eq!(c, b);
    }

    #[test]
    #[serial]
    fn test_fq12_mul_by_034() {
        let a = random_fq12();
        let c0 = random_fq2();
        let c3 = random_fq2();
        let c4 = random_fq2();
        let circuit = Fq12::mul_by_034(wires_set_from_fq12(a.clone()), wires_set_from_fq2(c0.clone()), wires_set_from_fq2(c3.clone()), wires_set_from_fq2(c4.clone()));
        circuit.gate_counts().print();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq12_from_wires(circuit.0);
        let mut b = a;
        b.mul_by_034(&c0, &c3, &c4);
        assert_eq!(c, b);
    }

    #[test]
    #[serial]
    fn test_fq12_square() {
        let a = random_fq12();
        let circuit = Fq12::square(wires_set_from_fq12(a.clone()));
        circuit.gate_counts().print();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq12_from_wires(circuit.0);
        assert_eq!(c, a * a);
    }

    #[test]
    #[serial]
    fn test_fq12_inverse() {
        let a = random_fq12();
        let circuit = Fq12::inverse(wires_set_from_fq12(a.clone()));
        circuit.gate_counts().print();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq12_from_wires(circuit.0);
        assert_eq!(c.inverse().unwrap(), a);
    }

    #[test]
    #[serial]
    fn test_fq12_frobenius() {
        let a = random_fq12();

        let circuit = Fq12::frobenius(wires_set_from_fq12(a.clone()), 0);
        circuit.gate_counts().print();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq12_from_wires(circuit.0);
        assert_eq!(c, a.frobenius_map(0));

        let circuit = Fq12::frobenius(wires_set_from_fq12(a.clone()), 1);
        circuit.gate_counts().print();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq12_from_wires(circuit.0);
        assert_eq!(c, a.frobenius_map(1));

        let circuit = Fq12::frobenius(wires_set_from_fq12(a.clone()), 2);
        circuit.gate_counts().print();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq12_from_wires(circuit.0);
        assert_eq!(c, a.frobenius_map(2));

        let circuit = Fq12::frobenius(wires_set_from_fq12(a.clone()), 3);
        circuit.gate_counts().print();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq12_from_wires(circuit.0);
        assert_eq!(c, a.frobenius_map(3));
    }

    #[test]
    fn test_fq12_conjugate() {
        let a = random_fq12();

        let circuit = Fq12::conjugate(wires_set_from_fq12(a.clone()));
        circuit.gate_counts().print();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let mut b = a.clone();
        b.conjugate_in_place();
        let c = fq12_from_wires(circuit.0);
        assert_eq!(c, b);
    }
}
