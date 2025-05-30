use crate::{bag::*, circuits::basic::{full_adder, half_adder}};
use super::BigIntImpl;

impl<const N_BITS: usize> BigIntImpl<N_BITS> {
    pub fn add(input_wires: Vec<Rc<RefCell<Wire>>>) -> (Vec<Rc<RefCell<Wire>>>, Vec<Gate>) {
        assert_eq!(input_wires.len(), 2*N_BITS);
        let mut output_gates = Vec::new();
        let mut output_wires=Vec::new();

        let (wires, gates) = half_adder(vec![input_wires[0].clone(), input_wires[254].clone()]);
        output_wires.push(wires[0].clone());
        output_gates.extend(gates);
        let mut carry_wire = wires[1].clone();
        for i in 1..N_BITS {
            let (wires, gates) = full_adder(vec![input_wires[i].clone(), input_wires[i+254].clone(),carry_wire]);
            output_wires.push(wires[0].clone());
            output_gates.extend(gates);
            carry_wire = wires[1].clone();
        }
        output_wires.push(carry_wire);
        (output_wires, output_gates)
    }
}

#[cfg(test)]
mod tests {
    use rand::{rng, Rng};
    use crate::circuits::bigint::{U254, utils::tests::{biguint_from_bits, bits_from_biguint}};
    use super::*;

    #[test]
    fn test_add() {
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
        let result = a+b;
        let mut output_bits= bits_from_biguint(result);
        output_bits.pop();

        let (output_wires, gates) = U254::add(input_wires);

        for mut gate in gates {
            gate.evaluate();
        }
        for i in 0..U254::N_BITS+1 {
            assert_eq!(output_bits[i], output_wires[i].borrow().get_value());
        }
    }
}

