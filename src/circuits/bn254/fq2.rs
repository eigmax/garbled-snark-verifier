use crate::{bag::*, circuits::bn254::fq::Fq};

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
}

#[cfg(test)]
mod tests {
    use crate::circuits::bn254::utils::{fq2_from_wires, random_fq2, wires_set_from_fq2};
    use super::*;

    #[test]
    fn test_fq2_add() {
        let a = random_fq2();
        let b = random_fq2();
        let circuit = Fq2::add(wires_set_from_fq2(a.clone()), wires_set_from_fq2(b.clone()));
        println!("gate count: {:?}", circuit.1.len());
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
        println!("gate count: {:?}", circuit.1.len());
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
        println!("gate count: {:?}", circuit.1.len());
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
        println!("gate count: {:?}", circuit.1.len());
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq2_from_wires(circuit.0);
        assert_eq!(c, a + a);
    }

    #[test]
    fn test_fq2_mul() {
        let a = random_fq2();
        let b = random_fq2();
        let circuit = Fq2::mul(wires_set_from_fq2(a.clone()), wires_set_from_fq2(b.clone()));
        println!("gate count: {:?}", circuit.1.len());
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
        println!("gate count: {:?}", circuit.1.len());
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq2_from_wires(circuit.0);
        assert_eq!(c, a * b);
    }

    #[test]
    fn test_fq2_square() {
        let a = random_fq2();
        let circuit = Fq2::square(wires_set_from_fq2(a.clone()));
        println!("gate count: {:?}", circuit.1.len());
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq2_from_wires(circuit.0);
        assert_eq!(c, a * a);
    }
}
