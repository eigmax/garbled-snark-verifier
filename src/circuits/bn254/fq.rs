use num_bigint::BigUint;
use crate::circuits::bn254::fp254impl::Fp254Impl;

pub struct Fq;

impl Fp254Impl for Fq {
    const MODULUS: &'static str =
        "21888242871839275222246405745257275088696311157297823662689037894645226208583";
    const MONTGOMERY_M_INVERSE: &'static str = 
        "4759646384140481320982610724935209484903937857060724391493050186936685796471";
    const MONTGOMERY_R_INVERSE: &'static str = 
        "18289368484950178621272022062020525048389989670507786348948026221581485535495";
    const N_BITS: usize = 254;

    fn half_modulus() -> BigUint {
        BigUint::from(ark_bn254::Fq::from(1) / ark_bn254::Fq::from(2))
    }

    fn one_third_modulus() -> BigUint {
        BigUint::from(ark_bn254::Fq::from(1) / ark_bn254::Fq::from(3))
    }
    
    fn two_third_modulus() -> BigUint {
        BigUint::from(ark_bn254::Fq::from(2) / ark_bn254::Fq::from(3))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuits::bn254::utils::{fq_from_wires, random_fq, wires_set_from_fq};
    use ark_ff::Field;

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
        assert_eq!(c + c, a);
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
        assert_eq!(c * a, ark_bn254::Fq::ONE);
    }

    #[test]
    fn test_fq_div6() {
        let a = random_fq();
        let circuit = Fq::div6(wires_set_from_fq(a.clone()));
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }

        let c = fq_from_wires(circuit.0);
        assert_eq!(c + c + c + c + c + c, a);
    }

    #[test]
    fn test_montgomery_mul() {
        for _ in 0..5 {
            let r = ark_bn254::Fq::from(Fq::montgomery_r_as_biguint());
            let a = random_fq();
            let b = random_fq();
            //let a = ark_bn254::Fq::from(BigUint::from(2_u8));
            //let b = ark_bn254::Fq::from(BigUint::from(3_u8));
            let mont_a = a * r;
            let mont_b = b * r;
            //println!("a = {}\nb = {}\nmont_a = {}\nmont_b = {}", a, b, mont_a, mont_b);
            let circuit = Fq::montgomery_mul(wires_set_from_fq(mont_a.clone()), wires_set_from_fq(mont_b.clone()));
            circuit.print_gate_type_counts();
            for mut gate in circuit.1 {
                gate.evaluate();
            }
            let c = fq_from_wires(circuit.0);
            //println!("c = {}", c);
            assert_eq!(c, a * b * r);
        }
    }
}
