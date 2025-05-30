use crate::bag::*;

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

pub fn selector(input_wires: Vec<Rc<RefCell<Wire>>>) -> (Vec<Rc<RefCell<Wire>>>, Vec<Gate>) {
    assert_eq!(input_wires.len(),3);
    let wire_a = input_wires[0].clone();
    let wire_b = input_wires[1].clone();
    let wire_c = input_wires[2].clone();
    let wire_d = Rc::new(RefCell::new(Wire::new()));
    let wire_e = Rc::new(RefCell::new(Wire::new()));
    let wire_f = Rc::new(RefCell::new(Wire::new()));
    let wire_g = Rc::new(RefCell::new(Wire::new()));
    let gate_1 = Gate::new(wire_c.clone(), wire_c.clone(), wire_e.clone(), "inv".to_string());
    let gate_2 = Gate::new(wire_a.clone(), wire_c.clone(), wire_d.clone(), "nand".to_string());
    let gate_3 = Gate::new(wire_e.clone(), wire_b.clone(), wire_f.clone(), "nand".to_string());
    let gate_4 = Gate::new(wire_d.clone(), wire_f.clone(), wire_g.clone(), "nand".to_string());
    (vec![wire_g], vec![gate_1, gate_2, gate_3, gate_4])
}
