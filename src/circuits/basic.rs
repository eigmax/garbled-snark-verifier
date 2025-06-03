use crate::bag::*;

pub fn half_adder(a: Wirex, b: Wirex) -> Circuit {
    let result = Rc::new(RefCell::new(Wire::new()));
    let carry = Rc::new(RefCell::new(Wire::new()));
    let gate_result = Gate::xor(a.clone(), b.clone(), result.clone());
    let gate_carry = Gate::and(a.clone(), b.clone(), carry.clone());
    Circuit::new(vec![result, carry], vec![gate_result, gate_carry])
}

pub fn full_adder(a: Wirex, b: Wirex, c: Wirex) -> Circuit {
    let d = Rc::new(RefCell::new(Wire::new()));
    let e = Rc::new(RefCell::new(Wire::new()));
    let f = Rc::new(RefCell::new(Wire::new()));
    let result = Rc::new(RefCell::new(Wire::new()));
    let carry = Rc::new(RefCell::new(Wire::new()));
    let gate_1 = Gate::xor(a.clone(), b.clone(), d.clone());
    let gate_2 = Gate::and(a.clone(), b.clone(), e.clone());
    let gate_3 = Gate::xor(d.clone(), c.clone(), result.clone());
    let gate_4 = Gate::and(d.clone(), c.clone(), f.clone());
    let gate_5 = Gate::or(e.clone(), f.clone(), carry.clone());
    Circuit::new(vec![result, carry], vec![gate_1, gate_2, gate_3, gate_4, gate_5])
}

pub fn selector(a: Wirex, b: Wirex, c: Wirex) -> Circuit {
    let d = Rc::new(RefCell::new(Wire::new()));
    let e = Rc::new(RefCell::new(Wire::new()));
    let f = Rc::new(RefCell::new(Wire::new()));
    let g = Rc::new(RefCell::new(Wire::new()));
    let gate_1 = Gate::not(c.clone(), e.clone());
    let gate_2 = Gate::nand(a.clone(), c.clone(), d.clone());
    let gate_3 = Gate::nand(e.clone(), b.clone(), f.clone());
    let gate_4 = Gate::nand(d.clone(), f.clone(), g.clone());
    Circuit::new(vec![g], vec![gate_1, gate_2, gate_3, gate_4])
}
