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

pub fn half_subtracter(a: Wirex, b: Wirex) -> Circuit {
    let result = Rc::new(RefCell::new(Wire::new()));
    let borrow = Rc::new(RefCell::new(Wire::new()));
    let not_a = Rc::new(RefCell::new(Wire::new()));
    let gate_not_a = Gate::not(a.clone(), not_a.clone());
    let gate_result = Gate::xor(a.clone(), b.clone(), result.clone());
    let gate_borrow = Gate::and(not_a.clone(), b.clone(), borrow.clone());
    Circuit::new(vec![result, borrow], vec![gate_not_a, gate_result, gate_borrow])
}

pub fn full_subtracter(a: Wirex, b: Wirex, c: Wirex) -> Circuit {
    let d = Rc::new(RefCell::new(Wire::new()));
    let e = Rc::new(RefCell::new(Wire::new()));
    let f = Rc::new(RefCell::new(Wire::new()));
    let g = Rc::new(RefCell::new(Wire::new()));
    let h = Rc::new(RefCell::new(Wire::new()));
    let result = Rc::new(RefCell::new(Wire::new()));
    let borrow = Rc::new(RefCell::new(Wire::new()));

    let gate_1 = Gate::xor(a.clone(), b.clone(), d.clone());
    let gate_2 = Gate::xor(c.clone(), d.clone(), result.clone());
    let gate_3 = Gate::not(d.clone(), e.clone());
    let gate_4 = Gate::and(c.clone(), e.clone(), f.clone());
    let gate_5 = Gate::not(a.clone(), g.clone());
    let gate_6 = Gate::and(b.clone(), g.clone(), h.clone());
    let gate_7 = Gate::or(f.clone(), h.clone(), borrow.clone());

    Circuit::new(vec![result, borrow], vec![gate_1, gate_2, gate_3, gate_4, gate_5, gate_6, gate_7])
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

#[cfg(test)]
mod tests {
    use crate::{bag::*, circuits::basic::{full_adder, full_subtracter, half_adder, half_subtracter, selector}};

    #[test]
    fn test_half_adder() {
        let result = [
            ((false, false), (false, false)),
            ((false, true), (true, false)),
            ((true, false), (true, false)),
            ((true, true), (false, true)),
        ];

        for ((a, b), (c, d)) in result {
            let a_wire = Rc::new(RefCell::new(Wire::new()));
            a_wire.borrow_mut().set(a);

            let b_wire = Rc::new(RefCell::new(Wire::new()));
            b_wire.borrow_mut().set(b);

            let circuit = half_adder(a_wire, b_wire);

            for mut gate in circuit.1 {
                gate.evaluate();
            }

            let (c_wire, d_wire) = (circuit.0[0].clone(), circuit.0[1].clone());

            assert_eq!(c_wire.borrow().get_value(), c);
            assert_eq!(d_wire.borrow().get_value(), d);
        }
    }

    #[test]
    fn test_full_adder() {
        let result = [
            ((false, false, false), (false, false)),
            ((false, false, true), (true, false)),
            ((false, true, false), (true, false)),
            ((false, true, true), (false, true)),
            ((true, false, false), (true, false)),
            ((true, false, true), (false, true)),
            ((true, true, false), (false, true)),
            ((true, true, true), (true, true)),
        ];

        for ((a, b, c), (d, e)) in result {
            let a_wire = Rc::new(RefCell::new(Wire::new()));
            a_wire.borrow_mut().set(a);

            let b_wire = Rc::new(RefCell::new(Wire::new()));
            b_wire.borrow_mut().set(b);

            let c_wire = Rc::new(RefCell::new(Wire::new()));
            c_wire.borrow_mut().set(c);

            let circuit = full_adder(a_wire, b_wire, c_wire);

            for mut gate in circuit.1 {
                gate.evaluate();
            }

            let (d_wire, e_wire) = (circuit.0[0].clone(), circuit.0[1].clone());

            assert_eq!(d_wire.borrow().get_value(), d);
            assert_eq!(e_wire.borrow().get_value(), e);
        }
    }

    #[test]
    fn test_half_subtracter() {
        let result = [
            ((false, false), (false, false)),
            ((false, true), (true, true)),
            ((true, false), (true, false)),
            ((true, true), (false, false)),
        ];

        for ((a, b), (c, d)) in result {
            let a_wire = Rc::new(RefCell::new(Wire::new()));
            a_wire.borrow_mut().set(a);

            let b_wire = Rc::new(RefCell::new(Wire::new()));
            b_wire.borrow_mut().set(b);

            let circuit = half_subtracter(a_wire, b_wire);

            for mut gate in circuit.1 {
                gate.evaluate();
            }

            let (c_wire, d_wire) = (circuit.0[0].clone(), circuit.0[1].clone());

            assert_eq!(c_wire.borrow().get_value(), c);
            assert_eq!(d_wire.borrow().get_value(), d);
        }
    }

    #[test]
    fn test_full_subtracter() {
        let result = [
            ((false, false, false), (false, false)),
            ((false, false, true), (true, true)),
            ((false, true, false), (true, true)),
            ((false, true, true), (false, true)),
            ((true, false, false), (true, false)),
            ((true, false, true), (false, false)),
            ((true, true, false), (false, false)),
            ((true, true, true), (true, true)),
        ];

        for ((a, b, c), (d, e)) in result {
            let a_wire = Rc::new(RefCell::new(Wire::new()));
            a_wire.borrow_mut().set(a);

            let b_wire = Rc::new(RefCell::new(Wire::new()));
            b_wire.borrow_mut().set(b);

            let c_wire = Rc::new(RefCell::new(Wire::new()));
            c_wire.borrow_mut().set(c);

            let circuit = full_subtracter(a_wire, b_wire, c_wire);

            for mut gate in circuit.1 {
                gate.evaluate();
            }

            let (d_wire, e_wire) = (circuit.0[0].clone(), circuit.0[1].clone());

            assert_eq!(d_wire.borrow().get_value(), d);
            assert_eq!(e_wire.borrow().get_value(), e);
        }
    }

    #[test]
    fn test_selector() {
        let result = [
            ((false, false, false), false),
            ((false, false, true), false),
            ((false, true, false), true),
            ((false, true, true), false),
            ((true, false, false), false),
            ((true, false, true), true),
            ((true, true, false), true),
            ((true, true, true), true),
        ];

        for ((a, b, c), d) in result {
            let a_wire = Rc::new(RefCell::new(Wire::new()));
            a_wire.borrow_mut().set(a);

            let b_wire = Rc::new(RefCell::new(Wire::new()));
            b_wire.borrow_mut().set(b);

            let c_wire = Rc::new(RefCell::new(Wire::new()));
            c_wire.borrow_mut().set(c);

            let circuit = selector(a_wire, b_wire, c_wire);

            for mut gate in circuit.1 {
                gate.evaluate();
            }

            let d_wire = circuit.0[0].clone();

            assert_eq!(d_wire.borrow().get_value(), d);
        }
    }
}

