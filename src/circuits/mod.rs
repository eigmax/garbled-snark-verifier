use std::{cell::RefCell, rc::Rc};
use crate::{gate::Gate, wire::Wire};

pub fn half_adder(input_wires: Vec<Rc<RefCell<Wire>>>) -> (Vec<Rc<RefCell<Wire>>>, Vec<Gate>) {
    assert_eq!(input_wires.len(), 2);
    let wire_a = input_wires[0].clone();
    let wire_b = input_wires[1].clone();
    let wire_result = Rc::new(RefCell::new(Wire::new()));
    let wire_carry = Rc::new(RefCell::new(Wire::new()));
    let gate_result = Gate::new(wire_a.clone(), wire_b.clone(), wire_result.clone(), "xor".to_string());
    let gate_carry = Gate::new(wire_a.clone(), wire_b.clone(), wire_carry.clone(), "and".to_string());
    (vec![wire_result, wire_carry], vec![gate_result, gate_carry])
}

pub fn full_adder(input_wires: Vec<Rc<RefCell<Wire>>>) -> (Vec<Rc<RefCell<Wire>>>, Vec<Gate>) {
    assert_eq!(input_wires.len(), 3);
    let wire_a = input_wires[0].clone();
    let wire_b = input_wires[1].clone();
    let wire_c = input_wires[2].clone();
    let wire_d = Rc::new(RefCell::new(Wire::new()));
    let wire_e = Rc::new(RefCell::new(Wire::new()));
    let gate_1 = Gate::new(wire_a.clone(), wire_b.clone(), wire_d.clone(), "xor".to_string());
    let gate_2 = Gate::new(wire_a.clone(), wire_b.clone(), wire_e.clone(), "and".to_string());
    let wire_result = Rc::new(RefCell::new(Wire::new()));
    let wire_carry = Rc::new(RefCell::new(Wire::new()));
    let gate_3 = Gate::new(wire_d.clone(), wire_c.clone(), wire_result.clone(), "xor".to_string());
    let wire_f = Rc::new(RefCell::new(Wire::new()));
    let gate_4 = Gate::new(wire_d.clone(), wire_c.clone(), wire_f.clone(), "and".to_string());
    let gate_5 = Gate::new(wire_e.clone(), wire_f.clone(), wire_carry.clone(), "or".to_string());
    (vec![wire_result, wire_carry], vec![gate_1, gate_2, gate_3, gate_4, gate_5])
}

pub fn adder_2bit(input_wires: Vec<Rc<RefCell<Wire>>>) -> (Vec<Rc<RefCell<Wire>>>, Vec<Gate>) {
    assert_eq!(input_wires.len(), 4);
    let mut gates = Vec::new();
    let wire_a = input_wires[0].clone();
    let wire_b = input_wires[1].clone();
    let wire_c = input_wires[2].clone();
    let wire_d = input_wires[3].clone();
    let (wires_1, gates_1) = half_adder(vec![wire_a.clone(), wire_c.clone()]);
    let wire_e = wires_1[0].clone();
    let wire_f = wires_1[1].clone();
    gates.extend(gates_1);
    let (wires_2, gates_2) = full_adder(vec![wire_b.clone(), wire_d.clone(), wire_f]);
    let wire_g = wires_2[0].clone();
    let wire_h = wires_2[1].clone();
    gates.extend(gates_2);
    (vec![wire_e, wire_g, wire_h], gates)
}

pub fn adder_254bit(input_wires: Vec<Rc<RefCell<Wire>>>) -> (Vec<Rc<RefCell<Wire>>>, Vec<Gate>) {
    assert_eq!(input_wires.len(), 2*254);
    let mut output_gates = Vec::new();
    let mut output_wires=Vec::new();

    let (wires, gates) = half_adder(vec![input_wires[0].clone(), input_wires[254].clone()]);
    output_wires.push(wires[0].clone());
    output_gates.extend(gates);
    let mut carry_wire = wires[1].clone();
    for i in 1..254{
        let (wires, gates) = full_adder(vec![input_wires[i].clone(), input_wires[i+254].clone(),carry_wire]);
        output_wires.push(wires[0].clone());
        output_gates.extend(gates);
        carry_wire = wires[1].clone();
    }
    (output_wires, output_gates)
}

#[cfg(test)]
mod tests {
    use num_bigint::BigUint;
    use rand::{rng, Rng};
    use crate::bit_to_u8;

    use super::*;

    fn random_biguint() -> BigUint {
        BigUint::from_bytes_le(&rand::rng().random::<[u8; 32]>())
    }

    fn bits_from_biguint(u: BigUint) -> Vec<bool> {
        let bytes = u.to_bytes_le();
        let mut bits = Vec::new();
        for byte in bytes {
            for i in 0..8 {
                bits.push(((byte >> i) & 1) == 1)
            }
        }
        bits
    }

    fn biguint_from_bits(bits: Vec<bool>) -> BigUint {
        let zero = BigUint::ZERO;
        let one = BigUint::from(1_u8);
        let mut u = zero.clone();
        for bit in bits.iter().rev() {
            u = u.clone() + u.clone() + if *bit {one.clone()} else {zero.clone()};
        }
        u
    }

    #[test]
    fn test_random_biguint() {
        let u = random_biguint();
        println!("u: {:?}", u);
        let b = bits_from_biguint(u.clone());
        let v = biguint_from_bits(b);
        println!("v: {:?}", v);
        assert_eq!(u, v);
    }

    #[test]
    fn test_adder_2bit() {
        let wire_a = Rc::new(RefCell::new(Wire::new()));
        let wire_b = Rc::new(RefCell::new(Wire::new()));
        let wire_c = Rc::new(RefCell::new(Wire::new()));
        let wire_d = Rc::new(RefCell::new(Wire::new()));
        let (wires, gates) = adder_2bit(vec![wire_a.clone(), wire_b.clone(), wire_c.clone(), wire_d.clone()]);

        let wire_e = wires[0].clone();
        let wire_f = wires[1].clone();
        let wire_g = wires[2].clone();

        let a = rng().random::<u8>() % 4;
        let b = rng().random::<u8>() % 4;
        let c = a + b;

        wire_a.borrow_mut().set((a & 1) == 1);
        wire_b.borrow_mut().set((a & 2) == 1);
        wire_c.borrow_mut().set((b & 1) == 1);
        wire_d.borrow_mut().set((b & 2) == 1);

        for mut gate in gates {
            gate.evaluate();
        }

        let d = bit_to_u8(wire_e.borrow().get_value()) + 2 * bit_to_u8(wire_f.borrow().get_value()) + 4 * bit_to_u8(wire_g.borrow().get_value());
        assert_eq!(c, d);
    }
}

