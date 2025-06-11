use ark_ff::{Field, Fp2Config};

use crate::{bag::*, circuits::bn254::{fp254impl::Fp254Impl, fq::Fq}};

pub struct Fq2;

impl Fq2 {
    pub const N_BITS: usize = 2 * Fq::N_BITS;

    pub fn add(a: Wires, b: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        assert_eq!(b.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq::N_BITS].to_vec();
        let a_c1 = a[Fq::N_BITS..2*Fq::N_BITS].to_vec();
        let b_c0 = b[0..Fq::N_BITS].to_vec();
        let b_c1 = b[Fq::N_BITS..2*Fq::N_BITS].to_vec();
        let wires_1 = circuit.extend(Fq::add(a_c0, b_c0));
        let wires_2 = circuit.extend(Fq::add(a_c1, b_c1));
        circuit.add_wires(wires_1);
        circuit.add_wires(wires_2);
        circuit
    }

    pub fn add_constant(a: Wires, b: ark_bn254::Fq2) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq::N_BITS].to_vec();
        let a_c1 = a[Fq::N_BITS..2*Fq::N_BITS].to_vec();

        let wires_1 = circuit.extend(Fq::add_constant(a_c0, b.c0));
        let wires_2 = circuit.extend(Fq::add_constant(a_c1, b.c1));
        circuit.add_wires(wires_1);
        circuit.add_wires(wires_2);
        circuit
    }

    pub fn neg(a: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq::N_BITS].to_vec();
        let a_c1 = a[Fq::N_BITS..2*Fq::N_BITS].to_vec();

        let wires_1 = circuit.extend(Fq::neg(a_c0));
        let wires_2 = circuit.extend(Fq::neg(a_c1));
        circuit.add_wires(wires_1);
        circuit.add_wires(wires_2);
        circuit
    }

    pub fn sub(a: Wires, b: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        assert_eq!(b.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq::N_BITS].to_vec();
        let a_c1 = a[Fq::N_BITS..2*Fq::N_BITS].to_vec();
        let b_c0 = b[0..Fq::N_BITS].to_vec();
        let b_c1 = b[Fq::N_BITS..2*Fq::N_BITS].to_vec();
        let wires_1 = circuit.extend(Fq::sub(a_c0, b_c0));
        let wires_2 = circuit.extend(Fq::sub(a_c1, b_c1));
        circuit.add_wires(wires_1);
        circuit.add_wires(wires_2);
        circuit
    }

    pub fn double(a: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq::N_BITS].to_vec();
        let a_c1 = a[Fq::N_BITS..2*Fq::N_BITS].to_vec();

        let wires_1 = circuit.extend(Fq::double(a_c0));
        let wires_2 = circuit.extend(Fq::double(a_c1));
        circuit.add_wires(wires_1);
        circuit.add_wires(wires_2);
        circuit
    }

    pub fn half(a: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq::N_BITS].to_vec();
        let a_c1 = a[Fq::N_BITS..2*Fq::N_BITS].to_vec();

        let wires_1 = circuit.extend(Fq::half(a_c0));
        let wires_2 = circuit.extend(Fq::half(a_c1));
        circuit.add_wires(wires_1);
        circuit.add_wires(wires_2);
        circuit
    }

    pub fn triple(a: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_2 = circuit.extend(Fq2::double(a.clone()));
        let a_3 = circuit.extend(Fq2::add(a_2, a));
        circuit.add_wires(a_3);
        circuit
    }

    pub fn mul(a: Wires, b: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        assert_eq!(b.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq::N_BITS].to_vec();
        let a_c1 = a[Fq::N_BITS..2*Fq::N_BITS].to_vec();
        let b_c0 = b[0..Fq::N_BITS].to_vec();
        let b_c1 = b[Fq::N_BITS..2*Fq::N_BITS].to_vec();

        let wires_1 = circuit.extend(Fq::add(a_c0.clone(), a_c1.clone()));
        let wires_2 = circuit.extend(Fq::add(b_c0.clone(), b_c1.clone()));
        let wires_3 = circuit.extend(Fq::mul(a_c0.clone(), b_c0.clone()));
        let wires_4 = circuit.extend(Fq::mul(a_c1.clone(), b_c1.clone()));
        let wires_5 = circuit.extend(Fq::add(wires_3.clone(), wires_4.clone()));
        let wires_6 = circuit.extend(Fq::sub(wires_3.clone(), wires_4.clone()));
        let wires_7 = circuit.extend(Fq::mul(wires_1.clone(), wires_2.clone()));
        let wires_8 = circuit.extend(Fq::sub(wires_7.clone(), wires_5.clone()));
        circuit.add_wires(wires_6);
        circuit.add_wires(wires_8);
        circuit
    }

    pub fn mul_by_constant(a: Wires, b: ark_bn254::Fq2) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        if b == ark_bn254::Fq2::ONE {
            circuit.add_wires(a);
            return circuit;
        }

        let a_c0 = a[0..Fq::N_BITS].to_vec();
        let a_c1 = a[Fq::N_BITS..2*Fq::N_BITS].to_vec();

        let wires_1 = circuit.extend(Fq::add(a_c0.clone(), a_c1.clone()));
        let wires_2 = circuit.extend(Fq::mul_by_constant(a_c0.clone(), b.c0.clone()));
        let wires_3 = circuit.extend(Fq::mul_by_constant(a_c1.clone(), b.c1.clone()));
        let wires_4 = circuit.extend(Fq::mul_by_constant(wires_1.clone(), b.c0 + b.c1));
        let wires_5 = circuit.extend(Fq::sub(wires_2.clone(), wires_3.clone()));
        let wires_6 = circuit.extend(Fq::add(wires_2.clone(), wires_3.clone()));
        let wires_7 = circuit.extend(Fq::sub(wires_4.clone(), wires_6.clone()));
        circuit.add_wires(wires_5);
        circuit.add_wires(wires_7);
        circuit
    }

    pub fn mul_by_constant_fq(a: Wires, b: ark_bn254::Fq) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq::N_BITS].to_vec();
        let a_c1 = a[Fq::N_BITS..2*Fq::N_BITS].to_vec();

        let wires_1 = circuit.extend(Fq::mul_by_constant(a_c0.clone(), b.clone()));
        let wires_2 = circuit.extend(Fq::mul_by_constant(a_c1.clone(), b.clone()));
        circuit.add_wires(wires_1);
        circuit.add_wires(wires_2);
        circuit
    }

    pub fn mul_by_nonresidue(a: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq::N_BITS].to_vec();
        let a_c1 = a[Fq::N_BITS..2*Fq::N_BITS].to_vec();

        let a0_3 = circuit.extend(Fq::triple(a_c0.clone()));
        let a0_9 = circuit.extend(Fq::triple(a0_3.clone()));

        let a1_3 = circuit.extend(Fq::triple(a_c1.clone()));
        let a1_9 = circuit.extend(Fq::triple(a1_3.clone()));

        let u = circuit.extend(Fq::sub(a0_9.clone(), a_c1.clone()));
        let v = circuit.extend(Fq::add(a1_9.clone(), a_c0.clone()));

        circuit.add_wires(u);
        circuit.add_wires(v);
        circuit
    }

    pub fn square(a: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq::N_BITS].to_vec();
        let a_c1 = a[Fq::N_BITS..2*Fq::N_BITS].to_vec();

        let wires_1 = circuit.extend(Fq::add(a_c0.clone(), a_c1.clone()));
        let wires_2 = circuit.extend(Fq::add(a_c0.clone(), a_c1.clone()));
        let wires_3 = circuit.extend(Fq::mul(a_c0.clone(), a_c0.clone()));
        let wires_4 = circuit.extend(Fq::mul(a_c1.clone(), a_c1.clone()));
        let wires_5 = circuit.extend(Fq::add(wires_3.clone(), wires_4.clone()));
        let wires_6 = circuit.extend(Fq::sub(wires_3.clone(), wires_4.clone()));
        let wires_7 = circuit.extend(Fq::mul(wires_1.clone(), wires_2.clone()));
        let wires_8 = circuit.extend(Fq::sub(wires_7.clone(), wires_5.clone()));
        circuit.add_wires(wires_6);
        circuit.add_wires(wires_8);
        circuit
    }

    pub fn frobenius(a: Wires, i: usize) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq::N_BITS].to_vec();
        let a_c1 = a[Fq::N_BITS..2*Fq::N_BITS].to_vec();

        let result = circuit.extend(Fq::mul_by_constant(a_c1, ark_bn254::Fq2Config::FROBENIUS_COEFF_FP2_C1[i % ark_bn254::Fq2Config::FROBENIUS_COEFF_FP2_C1.len()]));
        circuit.0.extend(a_c0);
        circuit.0.extend(result);
        circuit
    }

    pub fn div6(a: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq::N_BITS].to_vec();
        let a_c1 = a[Fq::N_BITS..2*Fq::N_BITS].to_vec();

        let wires_1 = circuit.extend(Fq::div6(a_c0));
        let wires_2 = circuit.extend(Fq::div6(a_c1));
        circuit.add_wires(wires_1);
        circuit.add_wires(wires_2);
        circuit
    }
}

#[cfg(test)]
mod tests {
    use ark_ff::{AdditiveGroup, Fp6Config};
    use crate::circuits::bn254::utils::{fq2_from_wires, random_fq, random_fq2, wires_set_from_fq2};
    use super::*;

    #[test]
    fn test_fq2_add() {
        let a = random_fq2();
        let b = random_fq2();
        let circuit = Fq2::add(wires_set_from_fq2(a.clone()), wires_set_from_fq2(b.clone()));
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq2_from_wires(circuit.0);
        assert_eq!(c, a + b);
    }

    #[test]
    fn test_fq2_neg() {
        let a = random_fq2();
        let circuit = Fq2::neg(wires_set_from_fq2(a.clone()));
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq2_from_wires(circuit.0);
        assert_eq!(c, -a);
    }

    #[test]
    fn test_fq2_sub() {
        let a = random_fq2();
        let b = random_fq2();
        let circuit = Fq2::sub(wires_set_from_fq2(a.clone()), wires_set_from_fq2(b.clone()));
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq2_from_wires(circuit.0);
        assert_eq!(c, a - b);
    }

    #[test]
    fn test_fq2_double() {
        let a = random_fq2();
        let circuit = Fq2::double(wires_set_from_fq2(a.clone()));
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq2_from_wires(circuit.0);
        assert_eq!(c, a + a);
    }

    #[test]
    fn test_fq2_triple() {
        let a = random_fq2();
        let circuit = Fq2::triple(wires_set_from_fq2(a.clone()));
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq2_from_wires(circuit.0);
        assert_eq!(c, a + a + a);
    }

    #[test]
    fn test_fq2_mul() {
        let a = random_fq2();
        let b = random_fq2();
        let circuit = Fq2::mul(wires_set_from_fq2(a.clone()), wires_set_from_fq2(b.clone()));
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq2_from_wires(circuit.0);
        assert_eq!(c, a * b);
    }

    #[test]
    fn test_fq2_mul_by_constant() {
        let a = random_fq2();
        let b = random_fq2();
        let circuit = Fq2::mul_by_constant(wires_set_from_fq2(a.clone()), b.clone());
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq2_from_wires(circuit.0);
        assert_eq!(c, a * b);
    }

    #[test]
    fn test_fq2_mul_by_constant_fq() {
        let a = random_fq2();
        let b = random_fq();
        let circuit = Fq2::mul_by_constant_fq(wires_set_from_fq2(a.clone()), b.clone());
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq2_from_wires(circuit.0);
        assert_eq!(c, a * ark_bn254::Fq2::new(b, ark_bn254::Fq::ZERO));
    }

    #[test]
    fn test_fq2_mul_by_nonresiude() {
        let a = random_fq2();
        let circuit = Fq2::mul_by_nonresidue(wires_set_from_fq2(a.clone()));
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq2_from_wires(circuit.0);
        assert_eq!(c, ark_bn254::Fq6Config::mul_fp2_by_nonresidue(a));
    }

    #[test]
    fn test_fq2_square() {
        let a = random_fq2();
        let circuit = Fq2::square(wires_set_from_fq2(a.clone()));
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq2_from_wires(circuit.0);
        assert_eq!(c, a * a);
    }

    #[test]
    fn test_fq2_frobenius() {
        let a = random_fq2();

        let circuit = Fq2::frobenius(wires_set_from_fq2(a.clone()), 0);
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq2_from_wires(circuit.0);
        assert_eq!(c, a.frobenius_map(0));

        let circuit = Fq2::frobenius(wires_set_from_fq2(a.clone()), 1);
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq2_from_wires(circuit.0);
        assert_eq!(c, a.frobenius_map(1));
    }

    #[test]
    fn test_fq2_div6() {
        let a = random_fq2();
        let circuit = Fq2::div6(wires_set_from_fq2(a.clone()));
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq2_from_wires(circuit.0);
        assert_eq!(c + c + c + c + c + c , a);
    }
}
