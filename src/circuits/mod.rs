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
    use super::*;

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

        wire_a.borrow_mut().set(false);
        wire_b.borrow_mut().set(true);
        wire_c.borrow_mut().set(true);
        wire_d.borrow_mut().set(true);

        for mut gate in gates {
            gate.evaluate();
        }

        println!("bit0: {:?}", wire_e.borrow().get_value());
        println!("bit1: {:?}", wire_f.borrow().get_value());
        println!("bit2: {:?}", wire_g.borrow().get_value());
    }
}

