use crate::{bag::*, circuits::bn254::fq2::Fq2};

use super::fq::Fq;

pub struct Fq6;

impl Fq6 {
    pub const N_BITS: usize = 6 * Fq::N_BITS;

    pub fn add(a: Wires, b: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        assert_eq!(b.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq2::N_BITS].to_vec();
        let a_c1 = a[Fq2::N_BITS..2*Fq2::N_BITS].to_vec();
        let a_c2 = a[2*Fq2::N_BITS..3*Fq2::N_BITS].to_vec();
        let b_c0 = b[0..Fq2::N_BITS].to_vec();
        let b_c1 = b[Fq2::N_BITS..2*Fq2::N_BITS].to_vec();
        let b_c2 = b[2*Fq2::N_BITS..3*Fq2::N_BITS].to_vec();
        let wires_1 = circuit.extend(Fq2::add(a_c0, b_c0));
        let wires_2 = circuit.extend(Fq2::add(a_c1, b_c1));
        let wires_3 = circuit.extend(Fq2::add(a_c2, b_c2));
        circuit.add_wires(wires_1);
        circuit.add_wires(wires_2);
        circuit.add_wires(wires_3);
        circuit
    }

    pub fn neg(a: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq2::N_BITS].to_vec();
        let a_c1 = a[Fq2::N_BITS..2*Fq2::N_BITS].to_vec();
        let a_c2 = a[2*Fq2::N_BITS..3*Fq2::N_BITS].to_vec();

        let wires_1 = circuit.extend(Fq2::neg(a_c0));
        let wires_2 = circuit.extend(Fq2::neg(a_c1));
        let wires_3 = circuit.extend(Fq2::neg(a_c2));
        circuit.add_wires(wires_1);
        circuit.add_wires(wires_2);
        circuit.add_wires(wires_3);
        circuit
    }

    pub fn sub(a: Wires, b: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        assert_eq!(b.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq2::N_BITS].to_vec();
        let a_c1 = a[Fq2::N_BITS..2*Fq2::N_BITS].to_vec();
        let a_c2 = a[2*Fq2::N_BITS..3*Fq2::N_BITS].to_vec();
        let b_c0 = b[0..Fq2::N_BITS].to_vec();
        let b_c1 = b[Fq2::N_BITS..2*Fq2::N_BITS].to_vec();
        let b_c2 = b[2*Fq2::N_BITS..3*Fq2::N_BITS].to_vec();
        let wires_1 = circuit.extend(Fq2::sub(a_c0, b_c0));
        let wires_2 = circuit.extend(Fq2::sub(a_c1, b_c1));
        let wires_3 = circuit.extend(Fq2::sub(a_c2, b_c2));
        circuit.add_wires(wires_1);
        circuit.add_wires(wires_2);
        circuit.add_wires(wires_3);
        circuit
    }

    pub fn double(a: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq2::N_BITS].to_vec();
        let a_c1 = a[Fq2::N_BITS..2*Fq2::N_BITS].to_vec();
        let a_c2 = a[2*Fq2::N_BITS..3*Fq2::N_BITS].to_vec();

        let wires_1 = circuit.extend(Fq2::double(a_c0));
        let wires_2 = circuit.extend(Fq2::double(a_c1));
        let wires_3 = circuit.extend(Fq2::double(a_c2));
        circuit.add_wires(wires_1);
        circuit.add_wires(wires_2);
        circuit.add_wires(wires_3);
        circuit
    }

    // pub fn mul(a: Wires, b: Wires) -> Circuit {
    //     assert_eq!(a.len(), Self::N_BITS);
    //     assert_eq!(b.len(), Self::N_BITS);
    //     let mut circuit = Circuit::empty();

    //     let a_c0 = a[0..Fq2::N_BITS].to_vec();
    //     let a_c1 = a[Fq2::N_BITS..2*Fq2::N_BITS].to_vec();
    //     let a_c2 = a[2*Fq2::N_BITS..3*Fq2::N_BITS].to_vec();
    //     let b_c0 = a[0..Fq2::N_BITS].to_vec();
    //     let b_c1 = a[Fq2::N_BITS..2*Fq2::N_BITS].to_vec();
    //     let b_c2 = a[2*Fq2::N_BITS..3*Fq2::N_BITS].to_vec();
    
    //     let wires_1 = circuit.extend(Fq2::add(a_c0.clone(), a_c1.clone()));
    //     let wires_2 = circuit.extend(Fq2::add(b_c0.clone(), b_c1.clone()));
    //     let wires_3 = circuit.extend(Fq2::mul(a_c0.clone(), b_c0.clone()));
    //     let wires_4 = circuit.extend(Fq2::mul(a_c1.clone(), b_c1.clone()));
    //     let wires_5 = circuit.extend(Fq2::add(wires_3.clone(), wires_4.clone()));
    //     let wires_6 = circuit.extend(Fq2::sub(wires_3.clone(), wires_4.clone()));
    //     let wires_7 = circuit.extend(Fq2::mul(wires_1.clone(), wires_2.clone()));
    //     let wires_8 = circuit.extend(Fq2::sub(wires_7.clone(), wires_5.clone()));
    //     circuit.add_wires(wires_6);
    //     circuit.add_wires(wires_8);
    //     circuit
    // }
}


#[cfg(test)]
mod tests {
    use crate::circuits::bn254::utils::{fq6_from_wires, random_fq6, wires_set_from_fq6};
    use super::*;

    #[test]
    fn test_fq6_add() {
        let a = random_fq6();
        let b = random_fq6();
        let circuit = Fq6::add(wires_set_from_fq6(a.clone()), wires_set_from_fq6(b.clone()));
        println!("gate count: {:?}", circuit.1.len());
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq6_from_wires(circuit.0);
        assert_eq!(c, a + b);
    }

    #[test]
    fn test_fq6_neg() {
        let a = random_fq6();
        let circuit = Fq6::neg(wires_set_from_fq6(a.clone()));
        println!("gate count: {:?}", circuit.1.len());
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq6_from_wires(circuit.0);
        assert_eq!(c, -a);
    }

    #[test]
    fn test_fq6_sub() {
        let a = random_fq6();
        let b = random_fq6();
        let circuit = Fq6::sub(wires_set_from_fq6(a.clone()), wires_set_from_fq6(b.clone()));
        println!("gate count: {:?}", circuit.1.len());
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq6_from_wires(circuit.0);
        assert_eq!(c, a - b);
    }

    #[test]
    fn test_fq6_double() {
        let a = random_fq6();
        let circuit = Fq6::double(wires_set_from_fq6(a.clone()));
        println!("gate count: {:?}", circuit.1.len());
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq6_from_wires(circuit.0);
        assert_eq!(c, a + a);
    }

    // #[test]
    // fn test_fq2_mul() {
    //     let a = random_fq2();
    //     let b = random_fq2();
    //     let circuit = Fq2::mul(wires_set_from_fq2(a.clone()), wires_set_from_fq2(b.clone()));
    //     println!("gate count: {:?}", circuit.1.len());
    //     for mut gate in circuit.1 {
    //         gate.evaluate();
    //     }
    //     let c = fq2_from_wires(circuit.0);
    //     assert_eq!(c, a * b);
    // }

    // #[test]
    // fn test_fq2_mul_by_constant() {
    //     let a = random_fq2();
    //     let b = random_fq2();
    //     let circuit = Fq2::mul_by_constant(wires_set_from_fq2(a.clone()), b.clone());
    //     println!("gate count: {:?}", circuit.1.len());
    //     for mut gate in circuit.1 {
    //         gate.evaluate();
    //     }
    //     let c = fq2_from_wires(circuit.0);
    //     assert_eq!(c, a * b);
    // }

    // #[test]
    // fn test_fq2_square() {
    //     let a = random_fq2();
    //     let circuit = Fq2::square(wires_set_from_fq2(a.clone()));
    //     println!("gate count: {:?}", circuit.1.len());
    //     for mut gate in circuit.1 {
    //         gate.evaluate();
    //     }
    //     let c = fq2_from_wires(circuit.0);
    //     assert_eq!(c, a * a);
    // }
}


