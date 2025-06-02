use crate::{bag::*, circuits::bn254::fq6::Fq6};
use ark_ff::Fp12Config;

pub struct Fq12;

impl Fq12 {
    pub const N_BITS: usize = 2 * Fq6::N_BITS;

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

    // pub fn mul_by_constant(a: Wires, b: ark_bn254::Fq12) -> Circuit {
    //     assert_eq!(a.len(), Self::N_BITS);
    //     let mut circuit = Circuit::empty();

    //     let a_c0 = a[0..Fq6::N_BITS].to_vec();
    //     let a_c1 = a[Fq6::N_BITS..2*Fq6::N_BITS].to_vec();

    //     let wires_1 = circuit.extend(Fq6::add(a_c0.clone(), a_c1.clone()));
    //     let wires_2 = circuit.extend(Fq6::mul_by_constant(a_c0.clone(), b.c0.clone()));
    //     let wires_3 = circuit.extend(Fq6::mul_by_constant(a_c1.clone(), b.c1.clone()));
    //     let wires_4 = circuit.extend(Fq6::mul_by_constant(wires_1.clone(), b.c0 + b.c1));
    //     let wires_5 = circuit.extend(Fq6::sub(wires_2.clone(), wires_3.clone()));
    //     let wires_6 = circuit.extend(Fq6::add(wires_2.clone(), wires_3.clone()));
    //     let wires_7 = circuit.extend(Fq6::sub(wires_4.clone(), wires_6.clone()));
    //     circuit.add_wires(wires_5);
    //     circuit.add_wires(wires_7);
    //     circuit
    // }

    // pub fn square(a: Wires) -> Circuit {
    //     assert_eq!(a.len(), Self::N_BITS);
    //     let mut circuit = Circuit::empty();

    //     let a_c0 = a[0..Fq6::N_BITS].to_vec();
    //     let a_c1 = a[Fq6::N_BITS..2*Fq6::N_BITS].to_vec();

    //     let wires_1 = circuit.extend(Fq6::add(a_c0.clone(), a_c1.clone()));
    //     let wires_2 = circuit.extend(Fq6::add(a_c0.clone(), a_c1.clone()));
    //     let wires_3 = circuit.extend(Fq6::mul(a_c0.clone(), a_c0.clone()));
    //     let wires_4 = circuit.extend(Fq6::mul(a_c1.clone(), a_c1.clone()));
    //     let wires_5 = circuit.extend(Fq6::add(wires_3.clone(), wires_4.clone()));
    //     let wires_6 = circuit.extend(Fq6::sub(wires_3.clone(), wires_4.clone()));
    //     let wires_7 = circuit.extend(Fq6::mul(wires_1.clone(), wires_2.clone()));
    //     let wires_8 = circuit.extend(Fq6::sub(wires_7.clone(), wires_5.clone()));
    //     circuit.add_wires(wires_6);
    //     circuit.add_wires(wires_8);
    //     circuit
    // }

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
}

#[cfg(test)]
mod tests {
    use ark_ff::Field;
    use crate::circuits::bn254::utils::{fq12_from_wires, random_fq12, wires_set_from_fq12};
    use super::*;

    #[test]
    fn test_fq12_add() {
        let a = random_fq12();
        let b = random_fq12();
        let circuit = Fq12::add(wires_set_from_fq12(a.clone()), wires_set_from_fq12(b.clone()));
        println!("gate count: {:?}", circuit.1.len());
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
        println!("gate count: {:?}", circuit.1.len());
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
        println!("gate count: {:?}", circuit.1.len());
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
        println!("gate count: {:?}", circuit.1.len());
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq12_from_wires(circuit.0);
        assert_eq!(c, a + a);
    }

    #[test]
    fn test_fq12_mul() {
        let a = random_fq12();
        let b = random_fq12();
        let circuit = Fq12::mul(wires_set_from_fq12(a.clone()), wires_set_from_fq12(b.clone()));
        println!("gate count: {:?}", circuit.1.len());
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq12_from_wires(circuit.0);
        assert_eq!(c, a * b);
    }

    // #[test]
    // fn test_fq12_mul_by_constant() {
    //     let a = random_fq12();
    //     let b = random_fq12();
    //     let circuit = Fq12::mul_by_constant(wires_set_from_fq12(a.clone()), b.clone());
    //     println!("gate count: {:?}", circuit.1.len());
    //     for mut gate in circuit.1 {
    //         gate.evaluate();
    //     }
    //     let c = fq12_from_wires(circuit.0);
    //     assert_eq!(c, a * b);
    // }

    // #[test]
    // fn test_fq12_square() {
    //     let a = random_fq12();
    //     let circuit = Fq12::square(wires_set_from_fq12(a.clone()));
    //     println!("gate count: {:?}", circuit.1.len());
    //     for mut gate in circuit.1 {
    //         gate.evaluate();
    //     }
    //     let c = fq12_from_wires(circuit.0);
    //     assert_eq!(c, a * a);
    // }

    #[test]
    fn test_fq12_frobenius() {
        let a = random_fq12();

        let circuit = Fq12::frobenius(wires_set_from_fq12(a.clone()), 0);
        println!("gate count: {:?}", circuit.1.len());
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq12_from_wires(circuit.0);
        assert_eq!(c, a.frobenius_map(0));

        let circuit = Fq12::frobenius(wires_set_from_fq12(a.clone()), 1);
        println!("gate count: {:?}", circuit.1.len());
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq12_from_wires(circuit.0);
        assert_eq!(c, a.frobenius_map(1));
    }
}
