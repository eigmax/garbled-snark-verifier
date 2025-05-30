use num_bigint::BigUint;
use crate::{bag::*, circuits::{basic::{full_adder, half_adder}, bigint::utils::bits_from_biguint}};
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

    pub fn add_constant(input_wires: Vec<Rc<RefCell<Wire>>>, c: BigUint) -> (Vec<Rc<RefCell<Wire>>>, Vec<Gate>) {
        assert_eq!(input_wires.len(), N_BITS);
        assert_ne!(c, BigUint::ZERO);
        let mut circuit_gates = Vec::new();
        let c_bits = bits_from_biguint(c);
        let mut output_wires=Vec::new();

        let mut carry_wire = Rc::new(RefCell::new(Wire::new()));
        let mut first_one = 0;
        while !c_bits[first_one]  {
            first_one += 1;
        }

        for i in 0..N_BITS {
            if i < first_one {
                output_wires.push(input_wires[i].clone());
            }
            else if i == first_one {
                let wire = Rc::new(RefCell::new(Wire::new()));
                let gate = Gate::new(input_wires[i].clone(), input_wires[i].clone(), wire.clone(), "inv".to_string());
                output_wires.push(wire);
                circuit_gates.push(gate);
                carry_wire = input_wires[i].clone(); 
            }
            else {
                if c_bits[i] {
                    let wire_1 = Rc::new(RefCell::new(Wire::new()));
                    let wire_2 = Rc::new(RefCell::new(Wire::new()));
                    let gate_1 = Gate::new(input_wires[i].clone(), carry_wire.clone(), wire_1.clone(), "xnor".to_string());
                    let gate_2 = Gate::new(input_wires[i].clone(), carry_wire.clone(), wire_2.clone(), "or".to_string());
                    output_wires.push(wire_1);
                    carry_wire = wire_2;
                    circuit_gates.push(gate_1);
                    circuit_gates.push(gate_2);
                }
                else {
                    let wire_1 = Rc::new(RefCell::new(Wire::new()));
                    let wire_2 = Rc::new(RefCell::new(Wire::new()));
                    let gate_1 = Gate::new(input_wires[i].clone(), carry_wire.clone(), wire_1.clone(), "xor".to_string());
                    let gate_2 = Gate::new(input_wires[i].clone(), carry_wire.clone(), wire_2.clone(), "and".to_string());
                    output_wires.push(wire_1);
                    carry_wire = wire_2;
                    circuit_gates.push(gate_1);
                    circuit_gates.push(gate_2);
                }
            }
        }
        output_wires.push(carry_wire);
        (output_wires, circuit_gates)
    }
}

#[cfg(test)]
mod tests {
    use rand::{rng, Rng};
    use crate::circuits::bigint::{utils::{biguint_from_bits, bits_from_biguint, random_u254}, U254};
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

    #[test]
    fn test_add_constant() {
        let mut input_wires = Vec::new();
        let mut bits1= Vec::new();
        for _ in 0..U254::N_BITS {
            let bit = rng().random::<bool>();
            let new_wire = Rc::new(RefCell::new(Wire::new()));
            new_wire.borrow_mut().set(bit);
            input_wires.push(new_wire);
            bits1.push(bit);
        }

        let a = biguint_from_bits(bits1.clone());
        let b = random_u254();
        let result = a.clone()+b.clone();
        let mut output_bits = bits_from_biguint(result.clone());
        output_bits.pop();

        let (output_wires, gates) = U254::add_constant(input_wires, b.clone());

        for mut gate in gates {
            gate.evaluate();
        }

        for i in 0..U254::N_BITS+1 {
            assert_eq!( output_bits[i], output_wires[i].borrow().get_value());
        }
    }
}

