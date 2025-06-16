use num_bigint::BigUint;

use super::BigIntImpl;
use crate::{bag::*, circuits::bigint::utils::bits_from_biguint};

impl<const N_BITS: usize> BigIntImpl<N_BITS> {
    pub fn mul(a_wires: Vec<Rc<RefCell<Wire>>>, b_wires: Vec<Rc<RefCell<Wire>>>) -> Circuit {
        assert_eq!(a_wires.len(), N_BITS);
        assert_eq!(b_wires.len(), N_BITS);

        let mut circuit = Circuit::empty();
        for _ in 0..(N_BITS * 2) {
            let wire = Rc::new(RefCell::new(Wire::new()));
            wire.borrow_mut().set(false);
            circuit.add_wire(wire)
        } //this part can be optimized later 

        for i in 0..N_BITS {
            let mut addition_wires_0 = vec![];
            for j in i..(i + N_BITS) {
                addition_wires_0.push(circuit.0[j].clone());
            }
            let addition_wires_1 =
                circuit.extend(Self::self_or_zero(a_wires.clone(), b_wires[i].clone()));
            let new_bits = circuit.extend(Self::add(addition_wires_0, addition_wires_1));
            circuit.0[i..(i + N_BITS + 1)].clone_from_slice(&new_bits[..((i + N_BITS - i) + 1)]);
        }
        circuit
    }

    ///Assuming constant is smaller than 2^N_BITS, and returns 2 * N_BITS result for now (can be optimized)
    pub fn mul_by_constant(a_wires: Vec<Rc<RefCell<Wire>>>, c: BigUint) -> Circuit {
        assert_eq!(a_wires.len(), N_BITS);
        let mut c_bits = bits_from_biguint(c);
        c_bits.truncate(N_BITS);
        //assert!(c_bits.len() < N_BITS, "{} is too long", c_bits.len());
        //this check doesn't work for now

        let mut circuit = Circuit::empty();

        for _ in 0..(N_BITS * 2) {
            let wire = Rc::new(RefCell::new(Wire::new()));
            wire.borrow_mut().set(false);
            circuit.add_wire(wire)
        } //this part can be optimized later 

        for (i, bit) in c_bits.iter().enumerate() {
            if *bit {
                let mut addition_wires = vec![];
                for j in i..(i + N_BITS) {
                    addition_wires.push(circuit.0[j].clone());
                }
                let new_bits = circuit.extend(Self::add(a_wires.clone(), addition_wires));
                circuit.0[i..(i + N_BITS + 1)]
                    .clone_from_slice(&new_bits[..((i + N_BITS - i) + 1)]);
            }
        }

        //this is buggy at the moment because of borrowing, an optimization for later maybe?
        /*
        let d = change_to_neg_pos_decomposition(c_bits);
        for (i, coeff) in d.iter().enumerate().rev() {
            if *coeff == 0 {
                continue;
            }
             let mut operation_wires = vec![];
            for j in i..(i + N_BITS) {
                operation_wires.push(circuit.0[j].clone());
            }
            let new_bits;
            if *coeff == 1 {
                new_bits = circuit.extend(Self::add(a_wires.clone(), operation_wires));
            } else {
                new_bits = circuit.extend(Self::optimized_sub(a_wires.clone(), operation_wires, false));
            }
            for j in i..=(i + N_BITS - (*coeff == -1) as usize) {
                circuit.0[j] = new_bits[j - i].clone();
            }
        }
        */
        circuit
    }
}

#[cfg(test)]
mod tests {
    use crate::circuits::bigint::{
        U254,
        utils::{biguint_from_bits, random_u254, wires_set_from_u254},
    };

    //tests are currently only for 254 bits

    #[test]
    fn test_mul() {
        for _ in 0..10 {
            let a = random_u254();
            let b = random_u254();
            let circuit = U254::mul(
                wires_set_from_u254(a.clone()),
                wires_set_from_u254(b.clone()),
            );
            let c = a * b;
            circuit.gate_counts().print();

            for mut gate in circuit.1 {
                gate.evaluate();
            }

            let result = biguint_from_bits(
                circuit
                    .0
                    .iter()
                    .map(|output_wire| output_wire.borrow().get_value())
                    .collect(),
            );
            assert_eq!(result, c);
        }
    }

    #[test]
    fn test_mul_by_constant() {
        for _ in 0..10 {
            let a = random_u254();
            let b = random_u254();
            let circuit = U254::mul_by_constant(wires_set_from_u254(a.clone()), b.clone());
            let c = a * b;
            circuit.gate_counts().print();

            for mut gate in circuit.1 {
                gate.evaluate();
            }

            let result = biguint_from_bits(
                circuit
                    .0
                    .iter()
                    .map(|output_wire| output_wire.borrow().get_value())
                    .collect(),
            );
            assert_eq!(result, c);
        }
    }
}
