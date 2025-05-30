use crate::circuits::bigint::U254;
use crate::{bag::*, circuits::basic::selector};
use super::BigIntImpl;

impl<const N_BITS: usize> BigIntImpl<N_BITS> {
    pub fn greater_than(input_wires: Vec<Rc<RefCell<Wire>>>) -> (Vec<Rc<RefCell<Wire>>>, Vec<Gate>) {
        assert_eq!(input_wires.len(), 2*N_BITS);
        let mut circuit_gates = Vec::new();
        let mut not_wires=Vec::new();
        let mut add_wires=Vec::new();

        for _ in 0..U254::N_BITS{
            let new_wire = Rc::new(RefCell::new(Wire::new()));
            not_wires.push(new_wire);
        }

        for i in 0 ..U254::N_BITS{
            let gate =Gate::new(input_wires[i+U254::N_BITS].clone(),input_wires[i+U254::N_BITS].clone(),not_wires[i].clone(),"inv".to_string()); 
            circuit_gates.push(gate);
        }

        for i in 0 ..U254::N_BITS{
            add_wires.push(input_wires[i].clone())
        }
        add_wires.extend(not_wires);

        let (wires, gates) = U254::add(add_wires);
        circuit_gates.extend(gates);
        (vec![wires[U254::N_BITS].clone()], circuit_gates)
    
    }

    pub fn select(input_wires: Vec<Rc<RefCell<Wire>>>) -> (Vec<Rc<RefCell<Wire>>>, Vec<Gate>) {
        assert_eq!(input_wires.len(),2*U254::N_BITS+1);
        let mut circuit_gates = Vec::new();
        let mut output_wires= Vec::new();
        let selector_wire = input_wires[U254::N_BITS*2].clone();
        for i in 0..U254::N_BITS {
            let (wires, gates) = selector(vec![input_wires[i].clone(), input_wires[i+U254::N_BITS].clone(), selector_wire.clone()]);
            output_wires.extend(wires);
            circuit_gates.extend(gates);
        }
        (output_wires, circuit_gates)
    }
}

#[cfg(test)]
mod tests {
    use rand::{rng, Rng};
    use crate::circuits::bigint::{utils::biguint_from_bits, U254};
    use super::*;

    #[test]
    fn test_greater_than() {
        let mut input_wires = Vec::new();
        let mut bits1= Vec::new();
        let mut bits2= Vec::new();
        for _ in 0..U254::N_BITS {
            let bit = rng().random::<bool>();
            let new_wire = Rc::new(RefCell::new(Wire::new()));
            new_wire.borrow_mut().set(bit);
            input_wires.push(new_wire);
            bits1.push(bit);
        }
        for _ in 0..U254::N_BITS {
            let bit = rng().random::<bool>();
            let new_wire = Rc::new(RefCell::new(Wire::new()));
            new_wire.borrow_mut().set(bit);
            input_wires.push(new_wire);
            bits2.push(bit);
        }

        let a = biguint_from_bits(bits1);
        let b = biguint_from_bits(bits2);

        let (output_wires, gates) = U254::greater_than(input_wires);

        for mut gate in gates {
            gate.evaluate();
        }

        assert_eq!(a>b, output_wires[0].borrow().get_value());
    }

    #[test]
    fn test_select() {
        let mut input_wires = Vec::new();
        let mut bits1= Vec::new();
        let mut bits2= Vec::new();
        for _ in 0..U254::N_BITS {
            let bit = rng().random::<bool>();
            let new_wire = Rc::new(RefCell::new(Wire::new()));
            new_wire.borrow_mut().set(bit);
            input_wires.push(new_wire);
            bits1.push(bit);
        }
        for _ in 0..U254::N_BITS {
            let bit = rng().random::<bool>();
            let new_wire = Rc::new(RefCell::new(Wire::new()));
            new_wire.borrow_mut().set(bit);
            input_wires.push(new_wire);
            bits2.push(bit);
        }

        let select = Rc::new(RefCell::new(Wire::new()));
        input_wires.push(select.clone());
        select.borrow_mut().set(true);

        let (output_wires, gates) = U254::select(input_wires);

        for mut gate in gates {
            gate.evaluate();
        }

        for i in 0..U254::N_BITS {
            assert_eq!(bits1[i], output_wires[i].borrow().get_value());
        }
    }
}
