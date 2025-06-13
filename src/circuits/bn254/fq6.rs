use crate::{bag::*, circuits::bn254::fq2::Fq2};
use ark_ff::{Fp6Config, fields::AdditiveGroup};

pub struct Fq6;

impl Fq6 {
    pub const N_BITS: usize = 3 * Fq2::N_BITS;

    pub fn as_montgomery(a: ark_bn254::Fq6) -> ark_bn254::Fq6 {
        ark_bn254::Fq6::new(
            Fq2::as_montgomery(a.c0),
            Fq2::as_montgomery(a.c1),
            Fq2::as_montgomery(a.c2),
        )
    }

    pub fn add(a: Wires, b: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        assert_eq!(b.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq2::N_BITS].to_vec();
        let a_c1 = a[Fq2::N_BITS..2 * Fq2::N_BITS].to_vec();
        let a_c2 = a[2 * Fq2::N_BITS..3 * Fq2::N_BITS].to_vec();
        let b_c0 = b[0..Fq2::N_BITS].to_vec();
        let b_c1 = b[Fq2::N_BITS..2 * Fq2::N_BITS].to_vec();
        let b_c2 = b[2 * Fq2::N_BITS..3 * Fq2::N_BITS].to_vec();
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
        let a_c1 = a[Fq2::N_BITS..2 * Fq2::N_BITS].to_vec();
        let a_c2 = a[2 * Fq2::N_BITS..3 * Fq2::N_BITS].to_vec();

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
        let a_c1 = a[Fq2::N_BITS..2 * Fq2::N_BITS].to_vec();
        let a_c2 = a[2 * Fq2::N_BITS..3 * Fq2::N_BITS].to_vec();
        let b_c0 = b[0..Fq2::N_BITS].to_vec();
        let b_c1 = b[Fq2::N_BITS..2 * Fq2::N_BITS].to_vec();
        let b_c2 = b[2 * Fq2::N_BITS..3 * Fq2::N_BITS].to_vec();
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
        let a_c1 = a[Fq2::N_BITS..2 * Fq2::N_BITS].to_vec();
        let a_c2 = a[2 * Fq2::N_BITS..3 * Fq2::N_BITS].to_vec();

        let wires_1 = circuit.extend(Fq2::double(a_c0));
        let wires_2 = circuit.extend(Fq2::double(a_c1));
        let wires_3 = circuit.extend(Fq2::double(a_c2));
        circuit.add_wires(wires_1);
        circuit.add_wires(wires_2);
        circuit.add_wires(wires_3);
        circuit
    }

    pub fn div6(a: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq2::N_BITS].to_vec();
        let a_c1 = a[Fq2::N_BITS..2 * Fq2::N_BITS].to_vec();
        let a_c2 = a[2 * Fq2::N_BITS..3 * Fq2::N_BITS].to_vec();

        let wires_1 = circuit.extend(Fq2::div6(a_c0.clone()));
        let wires_2 = circuit.extend(Fq2::div6(a_c1.clone()));
        let wires_3 = circuit.extend(Fq2::div6(a_c2.clone()));

        circuit.add_wires(wires_1);
        circuit.add_wires(wires_2);
        circuit.add_wires(wires_3);

        circuit
    }

    pub fn mul(a: Wires, b: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        assert_eq!(b.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq2::N_BITS].to_vec();
        let a_c1 = a[Fq2::N_BITS..2 * Fq2::N_BITS].to_vec();
        let a_c2 = a[2 * Fq2::N_BITS..3 * Fq2::N_BITS].to_vec();
        let b_c0 = b[0..Fq2::N_BITS].to_vec();
        let b_c1 = b[Fq2::N_BITS..2 * Fq2::N_BITS].to_vec();
        let b_c2 = b[2 * Fq2::N_BITS..3 * Fq2::N_BITS].to_vec();

        let v0 = circuit.extend(Fq2::mul(a_c0.clone(), b_c0.clone()));

        let wires_2: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::add(a_c0.clone(), a_c2.clone()));
        let wires_3: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::add(wires_2.clone(), a_c1.clone()));
        let wires_4: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::sub(wires_2.clone(), a_c1.clone()));
        let wires_5: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::double(a_c1.clone()));
        let wires_6: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::double(a_c2.clone()));
        let wires_7: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::double(wires_6.clone()));
        let wires_8: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::add(a_c0.clone(), wires_5.clone()));
        let wires_9: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::add(wires_8.clone(), wires_7.clone()));

        let wires_10: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::add(b_c0.clone(), b_c2.clone()));
        let wires_11: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::add(wires_10.clone(), b_c1.clone()));
        let wires_12: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::sub(wires_10.clone(), b_c1.clone()));
        let wires_13: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::double(b_c1.clone()));
        let wires_14: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::double(b_c2.clone()));
        let wires_15: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::double(wires_14.clone()));
        let wires_16: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::add(b_c0.clone(), wires_13.clone()));
        let wires_17: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::add(wires_16.clone(), wires_15.clone()));

        let v1 = circuit.extend(Fq2::mul(wires_3.clone(), wires_11.clone()));
        let v2 = circuit.extend(Fq2::mul(wires_4.clone(), wires_12.clone()));
        let v3 = circuit.extend(Fq2::mul(wires_9.clone(), wires_17.clone()));
        let v4 = circuit.extend(Fq2::mul(a_c2.clone(), b_c2.clone()));

        let v2_2 = circuit.extend(Fq2::double(v2.clone()));

        let v0_3 = circuit.extend(Fq2::triple(v0.clone()));
        let v1_3 = circuit.extend(Fq2::triple(v1.clone()));
        let v2_3 = circuit.extend(Fq2::triple(v2.clone()));
        let v4_3 = circuit.extend(Fq2::triple(v4.clone()));

        let v0_6 = circuit.extend(Fq2::double(v0_3.clone()));
        let v1_6 = circuit.extend(Fq2::double(v1_3.clone()));
        let v4_6 = circuit.extend(Fq2::double(v4_3.clone()));

        let v4_12 = circuit.extend(Fq2::double(v4_6.clone()));

        let wires_18: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::sub(v0_3.clone(), v1_3.clone()));
        let wires_19: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::sub(wires_18.clone(), v2.clone()));
        let wires_20: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::add(wires_19.clone(), v3.clone()));
        let wires_21: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::sub(wires_20.clone(), v4_12.clone()));
        let wires_22: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::mul_by_nonresidue(wires_21.clone()));
        let mut c0 = circuit.extend(Fq2::add(wires_22.clone(), v0_6.clone()));

        let wires_23: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::sub(v1_6.clone(), v0_3.clone()));
        let wires_24: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::sub(wires_23.clone(), v2_2.clone()));
        let wires_25: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::sub(wires_24.clone(), v3.clone()));
        let wires_26: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::add(wires_25.clone(), v4_12.clone()));
        let wires_27: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::mul_by_nonresidue(v4_6.clone()));
        let c1: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::add(wires_26, wires_27));

        let wires_28: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::sub(v1_3.clone(), v0_6.clone()));
        let wires_29: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::add(wires_28.clone(), v2_3.clone()));
        let c2: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::sub(wires_29.clone(), v4_6.clone()));

        c0.extend(c1);
        c0.extend(c2);
        let result = circuit.extend(Fq6::div6(c0));

        circuit.add_wires(result);
        circuit
    }

    pub fn mul_montgomery(a: Wires, b: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        assert_eq!(b.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq2::N_BITS].to_vec();
        let a_c1 = a[Fq2::N_BITS..2 * Fq2::N_BITS].to_vec();
        let a_c2 = a[2 * Fq2::N_BITS..3 * Fq2::N_BITS].to_vec();
        let b_c0 = b[0..Fq2::N_BITS].to_vec();
        let b_c1 = b[Fq2::N_BITS..2 * Fq2::N_BITS].to_vec();
        let b_c2 = b[2 * Fq2::N_BITS..3 * Fq2::N_BITS].to_vec();

        let v0 = circuit.extend(Fq2::mul_montgomery(a_c0.clone(), b_c0.clone()));

        let wires_2: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::add(a_c0.clone(), a_c2.clone()));
        let wires_3: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::add(wires_2.clone(), a_c1.clone()));
        let wires_4: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::sub(wires_2.clone(), a_c1.clone()));
        let wires_5: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::double(a_c1.clone()));
        let wires_6: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::double(a_c2.clone()));
        let wires_7: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::double(wires_6.clone()));
        let wires_8: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::add(a_c0.clone(), wires_5.clone()));
        let wires_9: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::add(wires_8.clone(), wires_7.clone()));

        let wires_10: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::add(b_c0.clone(), b_c2.clone()));
        let wires_11: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::add(wires_10.clone(), b_c1.clone()));
        let wires_12: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::sub(wires_10.clone(), b_c1.clone()));
        let wires_13: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::double(b_c1.clone()));
        let wires_14: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::double(b_c2.clone()));
        let wires_15: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::double(wires_14.clone()));
        let wires_16: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::add(b_c0.clone(), wires_13.clone()));
        let wires_17: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::add(wires_16.clone(), wires_15.clone()));

        let v1 = circuit.extend(Fq2::mul_montgomery(wires_3.clone(), wires_11.clone()));
        let v2 = circuit.extend(Fq2::mul_montgomery(wires_4.clone(), wires_12.clone()));
        let v3 = circuit.extend(Fq2::mul_montgomery(wires_9.clone(), wires_17.clone()));
        let v4 = circuit.extend(Fq2::mul_montgomery(a_c2.clone(), b_c2.clone()));

        let v2_2 = circuit.extend(Fq2::double(v2.clone()));

        let v0_3 = circuit.extend(Fq2::triple(v0.clone()));
        let v1_3 = circuit.extend(Fq2::triple(v1.clone()));
        let v2_3 = circuit.extend(Fq2::triple(v2.clone()));
        let v4_3 = circuit.extend(Fq2::triple(v4.clone()));

        let v0_6 = circuit.extend(Fq2::double(v0_3.clone()));
        let v1_6 = circuit.extend(Fq2::double(v1_3.clone()));
        let v4_6 = circuit.extend(Fq2::double(v4_3.clone()));

        let v4_12 = circuit.extend(Fq2::double(v4_6.clone()));

        let wires_18: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::sub(v0_3.clone(), v1_3.clone()));
        let wires_19: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::sub(wires_18.clone(), v2.clone()));
        let wires_20: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::add(wires_19.clone(), v3.clone()));
        let wires_21: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::sub(wires_20.clone(), v4_12.clone()));
        let wires_22: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::mul_by_nonresidue(wires_21.clone()));
        let mut c0 = circuit.extend(Fq2::add(wires_22.clone(), v0_6.clone()));

        let wires_23: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::sub(v1_6.clone(), v0_3.clone()));
        let wires_24: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::sub(wires_23.clone(), v2_2.clone()));
        let wires_25: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::sub(wires_24.clone(), v3.clone()));
        let wires_26: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::add(wires_25.clone(), v4_12.clone()));
        let wires_27: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::mul_by_nonresidue(v4_6.clone()));
        let c1: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::add(wires_26, wires_27));

        let wires_28: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::sub(v1_3.clone(), v0_6.clone()));
        let wires_29: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::add(wires_28.clone(), v2_3.clone()));
        let c2: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::sub(wires_29.clone(), v4_6.clone()));

        c0.extend(c1);
        c0.extend(c2);
        let result = circuit.extend(Fq6::div6(c0));

        circuit.add_wires(result);
        circuit
    }

    pub fn mul_by_constant(a: Wires, b: ark_bn254::Fq6) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq2::N_BITS].to_vec();
        let a_c1 = a[Fq2::N_BITS..2 * Fq2::N_BITS].to_vec();
        let a_c2 = a[2 * Fq2::N_BITS..3 * Fq2::N_BITS].to_vec();

        let v0 = circuit.extend(Fq2::mul_by_constant(a_c0.clone(), b.c0.clone()));

        let wires_2: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::add(a_c0.clone(), a_c2.clone()));
        let wires_3: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::add(wires_2.clone(), a_c1.clone()));
        let wires_4: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::sub(wires_2.clone(), a_c1.clone()));
        let wires_5: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::double(a_c1.clone()));
        let wires_6: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::double(a_c2.clone()));
        let wires_7: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::double(wires_6.clone()));
        let wires_8: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::add(a_c0.clone(), wires_5.clone()));
        let wires_9: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::add(wires_8.clone(), wires_7.clone()));

        let v1 = circuit.extend(Fq2::mul_by_constant(
            wires_3.clone(),
            b.c0.clone() + b.c1.clone() + b.c2.clone(),
        ));
        let v2 = circuit.extend(Fq2::mul_by_constant(
            wires_4.clone(),
            b.c0.clone() - b.c1.clone() + b.c2.clone(),
        ));
        let v3 = circuit.extend(Fq2::mul_by_constant(
            wires_9.clone(),
            b.c0.clone() + b.c1.double().clone() + b.c2.double().double().clone(),
        ));
        let v4 = circuit.extend(Fq2::mul_by_constant(a_c2.clone(), b.c2.clone()));

        let v2_2 = circuit.extend(Fq2::double(v2.clone()));

        let v0_3 = circuit.extend(Fq2::triple(v0.clone()));
        let v1_3 = circuit.extend(Fq2::triple(v1.clone()));
        let v2_3 = circuit.extend(Fq2::triple(v2.clone()));
        let v4_3 = circuit.extend(Fq2::triple(v4.clone()));

        let v0_6 = circuit.extend(Fq2::double(v0_3.clone()));
        let v1_6 = circuit.extend(Fq2::double(v1_3.clone()));
        let v4_6 = circuit.extend(Fq2::double(v4_3.clone()));

        let v4_12 = circuit.extend(Fq2::double(v4_6.clone()));

        let wires_18: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::sub(v0_3.clone(), v1_3.clone()));
        let wires_19: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::sub(wires_18.clone(), v2.clone()));
        let wires_20: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::add(wires_19.clone(), v3.clone()));
        let wires_21: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::sub(wires_20.clone(), v4_12.clone()));
        let wires_22: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::mul_by_nonresidue(wires_21.clone()));
        let mut c0 = circuit.extend(Fq2::add(wires_22.clone(), v0_6.clone()));

        let wires_23: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::sub(v1_6.clone(), v0_3.clone()));
        let wires_24: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::sub(wires_23.clone(), v2_2.clone()));
        let wires_25: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::sub(wires_24.clone(), v3.clone()));
        let wires_26: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::add(wires_25.clone(), v4_12.clone()));
        let wires_27: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::mul_by_nonresidue(v4_6.clone()));
        let c1: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::add(wires_26, wires_27));

        let wires_28: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::sub(v1_3.clone(), v0_6.clone()));
        let wires_29: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::add(wires_28.clone(), v2_3.clone()));
        let c2: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::sub(wires_29.clone(), v4_6.clone()));

        c0.extend(c1);
        c0.extend(c2);
        let result = circuit.extend(Fq6::div6(c0));

        circuit.add_wires(result);
        circuit
    }

    pub fn mul_by_fq2(a: Wires, b: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        assert_eq!(b.len(), Fq2::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq2::N_BITS].to_vec();
        let a_c1 = a[Fq2::N_BITS..2 * Fq2::N_BITS].to_vec();
        let a_c2 = a[2 * Fq2::N_BITS..3 * Fq2::N_BITS].to_vec();

        let c0 = circuit.extend(Fq2::mul(a_c0, b.clone()));
        let c1 = circuit.extend(Fq2::mul(a_c1, b.clone()));
        let c2 = circuit.extend(Fq2::mul(a_c2, b.clone()));
        circuit.add_wires(c0);
        circuit.add_wires(c1);
        circuit.add_wires(c2);
        circuit
    }

    pub fn mul_by_constant_fq2(a: Wires, b: ark_bn254::Fq2) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq2::N_BITS].to_vec();
        let a_c1 = a[Fq2::N_BITS..2 * Fq2::N_BITS].to_vec();
        let a_c2 = a[2 * Fq2::N_BITS..3 * Fq2::N_BITS].to_vec();

        let c0 = circuit.extend(Fq2::mul_by_constant(a_c0, b));
        let c1 = circuit.extend(Fq2::mul_by_constant(a_c1, b));
        let c2 = circuit.extend(Fq2::mul_by_constant(a_c2, b));
        circuit.add_wires(c0);
        circuit.add_wires(c1);
        circuit.add_wires(c2);
        circuit
    }

    pub fn mul_by_nonresidue(a: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq2::N_BITS].to_vec();
        let a_c1 = a[Fq2::N_BITS..2 * Fq2::N_BITS].to_vec();
        let a_c2 = a[2 * Fq2::N_BITS..3 * Fq2::N_BITS].to_vec();
        let u = circuit.extend(Fq2::mul_by_nonresidue(a_c2));

        circuit.add_wires(u);
        circuit.add_wires(a_c0);
        circuit.add_wires(a_c1);
        circuit
    }

    pub fn mul_by_01(a: Wires, c0: Wires, c1: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        assert_eq!(c0.len(), Fq2::N_BITS);
        assert_eq!(c1.len(), Fq2::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq2::N_BITS].to_vec();
        let a_c1 = a[Fq2::N_BITS..2 * Fq2::N_BITS].to_vec();
        let a_c2 = a[2 * Fq2::N_BITS..3 * Fq2::N_BITS].to_vec();

        let wires_1 = circuit.extend(Fq2::mul(a_c0.clone(), c0.clone()));
        let wires_2 = circuit.extend(Fq2::mul(a_c1.clone(), c1.clone()));
        let wires_3 = circuit.extend(Fq2::add(a_c1.clone(), a_c2.clone()));
        let wires_4 = circuit.extend(Fq2::mul(wires_3.clone(), c1.clone()));
        let wires_5 = circuit.extend(Fq2::sub(wires_4.clone(), wires_2.clone()));
        let wires_6 = circuit.extend(Fq2::mul_by_nonresidue(wires_5.clone()));
        let wires_7 = circuit.extend(Fq2::add(wires_6.clone(), wires_1.clone()));
        let wires_8 = circuit.extend(Fq2::add(a_c0.clone(), a_c1.clone()));
        let wires_9 = circuit.extend(Fq2::add(c0.clone(), c1.clone()));
        let wires_10 = circuit.extend(Fq2::mul(wires_8.clone(), wires_9.clone()));
        let wires_11 = circuit.extend(Fq2::sub(wires_10.clone(), wires_1.clone()));
        let wires_12 = circuit.extend(Fq2::sub(wires_11.clone(), wires_2.clone()));
        let wires_13 = circuit.extend(Fq2::add(a_c0.clone(), a_c2.clone()));
        let wires_14 = circuit.extend(Fq2::mul(wires_13.clone(), c0.clone()));
        let wires_15 = circuit.extend(Fq2::sub(wires_14.clone(), wires_1.clone()));
        let wires_16 = circuit.extend(Fq2::add(wires_15.clone(), wires_2.clone()));
        circuit.add_wires(wires_7);
        circuit.add_wires(wires_12);
        circuit.add_wires(wires_16);
        circuit
    }

    pub fn mul_by_01_constant1(a: Wires, c0: Wires, c1: ark_bn254::Fq2) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        assert_eq!(c0.len(), Fq2::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq2::N_BITS].to_vec();
        let a_c1 = a[Fq2::N_BITS..2 * Fq2::N_BITS].to_vec();
        let a_c2 = a[2 * Fq2::N_BITS..3 * Fq2::N_BITS].to_vec();

        let wires_1 = circuit.extend(Fq2::mul(a_c0.clone(), c0.clone()));
        let wires_2 = circuit.extend(Fq2::mul_by_constant(a_c1.clone(), c1.clone()));
        let wires_3 = circuit.extend(Fq2::add(a_c1.clone(), a_c2.clone()));
        let wires_4 = circuit.extend(Fq2::mul_by_constant(wires_3.clone(), c1.clone()));
        let wires_5 = circuit.extend(Fq2::sub(wires_4.clone(), wires_2.clone()));
        let wires_6 = circuit.extend(Fq2::mul_by_nonresidue(wires_5.clone()));
        let wires_7 = circuit.extend(Fq2::add(wires_6.clone(), wires_1.clone()));
        let wires_8 = circuit.extend(Fq2::add(a_c0.clone(), a_c1.clone()));
        let wires_9 = circuit.extend(Fq2::add_constant(c0.clone(), c1.clone()));
        let wires_10 = circuit.extend(Fq2::mul(wires_8.clone(), wires_9.clone()));
        let wires_11 = circuit.extend(Fq2::sub(wires_10.clone(), wires_1.clone()));
        let wires_12 = circuit.extend(Fq2::sub(wires_11.clone(), wires_2.clone()));
        let wires_13 = circuit.extend(Fq2::add(a_c0.clone(), a_c2.clone()));
        let wires_14 = circuit.extend(Fq2::mul(wires_13.clone(), c0.clone()));
        let wires_15 = circuit.extend(Fq2::sub(wires_14.clone(), wires_1.clone()));
        let wires_16 = circuit.extend(Fq2::add(wires_15.clone(), wires_2.clone()));
        circuit.add_wires(wires_7);
        circuit.add_wires(wires_12);
        circuit.add_wires(wires_16);
        circuit
    }

    pub fn square(a: Wires) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq2::N_BITS].to_vec();
        let a_c1 = a[Fq2::N_BITS..2 * Fq2::N_BITS].to_vec();
        let a_c2 = a[2 * Fq2::N_BITS..3 * Fq2::N_BITS].to_vec();

        let v0 = circuit.extend(Fq2::square(a_c0.clone()));
        let wires_1: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::mul(a_c0.clone(), a_c1.clone()));
        let v1: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::double(wires_1));
        let wires_2: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::add(a_c0.clone(), a_c2.clone()));
        let wires_3: Vec<Rc<RefCell<Wire>>> =
            circuit.extend(Fq2::sub(wires_2.clone(), a_c1.clone()));
        let v2 = circuit.extend(Fq2::square(wires_3));
        let wires_4: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::mul(a_c2.clone(), a_c1.clone()));
        let v3: Vec<Rc<RefCell<Wire>>> = circuit.extend(Fq2::double(wires_4));
        let v4 = circuit.extend(Fq2::square(a_c2.clone()));

        let v3_b = circuit.extend(Fq2::mul_by_nonresidue(v3.clone()));
        let v4_b = circuit.extend(Fq2::mul_by_nonresidue(v4.clone()));

        let c0 = circuit.extend(Fq2::add(v0.clone(), v3_b.clone()));
        let c1 = circuit.extend(Fq2::add(v1.clone(), v4_b.clone()));
        let wires_5 = circuit.extend(Fq2::add(v1.clone(), v2));
        let wires_6 = circuit.extend(Fq2::add(wires_5, v3));
        let wires_7 = circuit.extend(Fq2::add(v4, v0.clone()));
        let c2 = circuit.extend(Fq2::sub(wires_6, wires_7));

        circuit.add_wires(c0);
        circuit.add_wires(c1);
        circuit.add_wires(c2);
        circuit
    }

    pub fn inverse(r: Wires) -> Circuit {
        assert_eq!(r.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a = r[0..Fq2::N_BITS].to_vec();
        let b = r[Fq2::N_BITS..2 * Fq2::N_BITS].to_vec();
        let c = r[2 * Fq2::N_BITS..3 * Fq2::N_BITS].to_vec();

        let a_square = circuit.extend(Fq2::square(a.clone()));
        let b_square = circuit.extend(Fq2::square(b.clone()));
        let c_square = circuit.extend(Fq2::square(c.clone()));

        let ab = circuit.extend(Fq2::mul(a.clone(), b.clone()));
        let ac = circuit.extend(Fq2::mul(a.clone(), c.clone()));
        let bc = circuit.extend(Fq2::mul(b.clone(), c.clone()));

        let bc_beta = circuit.extend(Fq2::mul_by_nonresidue(bc));

        let a_square_minus_bc_beta = circuit.extend(Fq2::sub(a_square, bc_beta));

        let c_square_beta = circuit.extend(Fq2::mul_by_nonresidue(c_square));
        let c_square_beta_minus_ab = circuit.extend(Fq2::sub(c_square_beta, ab));
        let b_square_minus_ac = circuit.extend(Fq2::sub(b_square, ac));

        let wires_1 = circuit.extend(Fq2::mul(c_square_beta_minus_ab.clone(), c.clone()));

        let wires_2 = circuit.extend(Fq2::mul(b_square_minus_ac.clone(), b));

        let wires_1_plus_wires_2 = circuit.extend(Fq2::add(wires_1.clone(), wires_2.clone()));
        let wires_3 = circuit.extend(Fq2::mul_by_nonresidue(wires_1_plus_wires_2));

        let wires_4 = circuit.extend(Fq2::mul(a, a_square_minus_bc_beta.clone()));
        let norm = circuit.extend(Fq2::add(wires_4, wires_3));

        let inverse_norm = circuit.extend(Fq2::inverse(norm));
        let res_c0 = circuit.extend(Fq2::mul(a_square_minus_bc_beta, inverse_norm.clone()));
        let res_c1 = circuit.extend(Fq2::mul(c_square_beta_minus_ab, inverse_norm.clone()));
        let res_c2 = circuit.extend(Fq2::mul(b_square_minus_ac, inverse_norm.clone()));

        circuit.add_wires(res_c0);
        circuit.add_wires(res_c1);
        circuit.add_wires(res_c2);
        circuit
    }

    pub fn frobenius(a: Wires, i: usize) -> Circuit {
        assert_eq!(a.len(), Self::N_BITS);
        let mut circuit = Circuit::empty();

        let a_c0 = a[0..Fq2::N_BITS].to_vec();
        let a_c1 = a[Fq2::N_BITS..2 * Fq2::N_BITS].to_vec();
        let a_c2 = a[2 * Fq2::N_BITS..3 * Fq2::N_BITS].to_vec();

        let frobenius_a_c0 = circuit.extend(Fq2::frobenius(a_c0, i));
        let frobenius_a_c1 = circuit.extend(Fq2::frobenius(a_c1, i));
        let frobenius_a_c2 = circuit.extend(Fq2::frobenius(a_c2, i));
        let frobenius_a_c1_updated = circuit.extend(Fq2::mul_by_constant(
            frobenius_a_c1,
            ark_bn254::Fq6Config::FROBENIUS_COEFF_FP6_C1
                [i % ark_bn254::Fq6Config::FROBENIUS_COEFF_FP6_C1.len()],
        ));
        let frobenius_a_c2_updated = circuit.extend(Fq2::mul_by_constant(
            frobenius_a_c2,
            ark_bn254::Fq6Config::FROBENIUS_COEFF_FP6_C2
                [i % ark_bn254::Fq6Config::FROBENIUS_COEFF_FP6_C2.len()],
        ));
        circuit.0.extend(frobenius_a_c0);
        circuit.0.extend(frobenius_a_c1_updated);
        circuit.0.extend(frobenius_a_c2_updated);
        circuit
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuits::bn254::utils::{
        fq6_from_wires, random_fq2, random_fq6, wires_set_from_fq2, wires_set_from_fq6,
    };
    use ark_ff::{Field, Fp12Config};
    use serial_test::serial;

    #[test]
    fn test_fq6_add() {
        let a = random_fq6();
        let b = random_fq6();
        let circuit = Fq6::add(wires_set_from_fq6(a.clone()), wires_set_from_fq6(b.clone()));
        circuit.gate_counts().print();
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
        circuit.gate_counts().print();
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
        circuit.gate_counts().print();
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
        circuit.gate_counts().print();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq6_from_wires(circuit.0);
        assert_eq!(c, a + a);
    }

    #[test]
    fn test_fq6_div6() {
        let a = random_fq6();
        let circuit = Fq6::div6(wires_set_from_fq6(a.clone()));
        circuit.gate_counts().print();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq6_from_wires(circuit.0);
        assert_eq!(c + c + c + c + c + c, a);
    }

    #[test]
    #[serial]
    fn test_fq6_mul() {
        let a = random_fq6();
        let b = random_fq6();
        let circuit = Fq6::mul(wires_set_from_fq6(a.clone()), wires_set_from_fq6(b.clone()));
        circuit.gate_counts().print();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq6_from_wires(circuit.0);
        assert_eq!(c, a * b);
    }

    #[test]
    #[serial]
    fn test_fq6_mul_montgomery() {
        let a = random_fq6();
        let b = random_fq6();
        let circuit = Fq6::mul_montgomery(
            wires_set_from_fq6(Fq6::as_montgomery(a.clone())),
            wires_set_from_fq6(Fq6::as_montgomery(b.clone())),
        );
        circuit.gate_counts().print();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq6_from_wires(circuit.0);
        assert_eq!(c, Fq6::as_montgomery(a * b));
    }

    #[test]
    fn test_fq6_mul_by_constant() {
        let a = random_fq6();
        let b = random_fq6();
        let circuit = Fq6::mul_by_constant(wires_set_from_fq6(a.clone()), b);
        circuit.gate_counts().print();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq6_from_wires(circuit.0);
        assert_eq!(c, a * b);
    }

    #[test]
    fn test_fq6_mul_by_fq2() {
        let a = random_fq6();
        let b = random_fq2();
        let circuit = Fq6::mul_by_fq2(wires_set_from_fq6(a.clone()), wires_set_from_fq2(b.clone()));
        circuit.gate_counts().print();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq6_from_wires(circuit.0);
        assert_eq!(
            c,
            a * ark_bn254::Fq6::new(b, ark_bn254::Fq2::ZERO, ark_bn254::Fq2::ZERO)
        );
    }

    #[test]
    fn test_fq6_mul_by_constant_fq2() {
        let a = random_fq6();
        let b = random_fq2();
        let circuit = Fq6::mul_by_constant_fq2(wires_set_from_fq6(a.clone()), b);
        circuit.gate_counts().print();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq6_from_wires(circuit.0);
        assert_eq!(
            c,
            a * ark_bn254::Fq6::new(b, ark_bn254::Fq2::ZERO, ark_bn254::Fq2::ZERO)
        );
    }

    #[test]
    fn test_fq6_mul_by_nonresidue() {
        let a = random_fq6();
        let circuit = Fq6::mul_by_nonresidue(wires_set_from_fq6(a.clone()));
        circuit.gate_counts().print();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq6_from_wires(circuit.0);
        let mut a_nonresiude = a.clone();
        ark_bn254::Fq12Config::mul_fp6_by_nonresidue_in_place(&mut a_nonresiude);
        assert_eq!(c, a_nonresiude);
    }

    #[test]
    fn test_fq6_mul_by_01() {
        let a = random_fq6();
        let c0 = random_fq2();
        let c1 = random_fq2();
        let circuit = Fq6::mul_by_01(
            wires_set_from_fq6(a.clone()),
            wires_set_from_fq2(c0.clone()),
            wires_set_from_fq2(c1.clone()),
        );
        circuit.gate_counts().print();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq6_from_wires(circuit.0);
        let mut b = a;
        b.mul_by_01(&c0, &c1);
        assert_eq!(c, b);
    }

    #[test]
    #[serial]
    fn test_fq6_square() {
        let a = random_fq6();
        let circuit = Fq6::square(wires_set_from_fq6(a.clone()));
        circuit.gate_counts().print();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq6_from_wires(circuit.0);
        assert_eq!(c, a * a);
    }

    #[test]
    #[serial]
    fn test_fq6_inverse() {
        let a = random_fq6();
        let circuit = Fq6::inverse(wires_set_from_fq6(a.clone()));
        circuit.gate_counts().print();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq6_from_wires(circuit.0);
        assert_eq!(c.inverse().unwrap(), a);
    }

    #[test]
    fn test_fq6_frobenius() {
        let a = random_fq6();

        let circuit = Fq6::frobenius(wires_set_from_fq6(a.clone()), 0);
        circuit.gate_counts().print();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq6_from_wires(circuit.0);
        assert_eq!(c, a.frobenius_map(0));

        let circuit = Fq6::frobenius(wires_set_from_fq6(a.clone()), 1);
        circuit.gate_counts().print();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = fq6_from_wires(circuit.0);
        assert_eq!(c, a.frobenius_map(1));
    }
}
