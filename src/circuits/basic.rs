use crate::bag::*;

pub fn half_adder(a: Wirex, b: Wirex) -> Circuit {
    let result = Rc::new(RefCell::new(Wire::new()));
    let carry = Rc::new(RefCell::new(Wire::new()));
    let gate_result = Gate::new(a.clone(), b.clone(), result.clone(), "xor".to_string());
    let gate_carry = Gate::new(a.clone(), b.clone(), carry.clone(), "and".to_string());
    Circuit::new(vec![result, carry], vec![gate_result, gate_carry])
}

pub fn full_adder(a: Wirex, b: Wirex, c: Wirex) -> Circuit {
    let d = Rc::new(RefCell::new(Wire::new()));
    let e = Rc::new(RefCell::new(Wire::new()));
    let f = Rc::new(RefCell::new(Wire::new()));
    let result = Rc::new(RefCell::new(Wire::new()));
    let carry = Rc::new(RefCell::new(Wire::new()));
    let gate_1 = Gate::new(a.clone(), b.clone(), d.clone(), "xor".to_string());
    let gate_2 = Gate::new(a.clone(), b.clone(), e.clone(), "and".to_string());
    let gate_3 = Gate::new(d.clone(), c.clone(), result.clone(), "xor".to_string());
    let gate_4 = Gate::new(d.clone(), c.clone(), f.clone(), "and".to_string());
    let gate_5 = Gate::new(e.clone(), f.clone(), carry.clone(), "or".to_string());
    Circuit::new(vec![result, carry], vec![gate_1, gate_2, gate_3, gate_4, gate_5])
}

pub fn selector(a: Wirex, b: Wirex, c: Wirex) -> Circuit {
    let d = Rc::new(RefCell::new(Wire::new()));
    let e = Rc::new(RefCell::new(Wire::new()));
    let f = Rc::new(RefCell::new(Wire::new()));
    let g = Rc::new(RefCell::new(Wire::new()));
    let gate_1 = Gate::new(c.clone(), c.clone(), e.clone(), "not".to_string());
    let gate_2 = Gate::new(a.clone(), c.clone(), d.clone(), "nand".to_string());
    let gate_3 = Gate::new(e.clone(), b.clone(), f.clone(), "nand".to_string());
    let gate_4 = Gate::new(d.clone(), f.clone(), g.clone(), "nand".to_string());
    Circuit::new(vec![g], vec![gate_1, gate_2, gate_3, gate_4])
}
