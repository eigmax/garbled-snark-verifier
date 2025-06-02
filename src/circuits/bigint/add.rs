use num_bigint::BigUint;
use crate::{bag::*, circuits::{basic::{full_adder, half_adder}, bigint::utils::bits_from_biguint}};
use super::BigIntImpl;

impl<const N_BITS: usize> BigIntImpl<N_BITS> {
    pub fn add(a: Wires, b: Wires) -> Circuit {
        assert_eq!(a.len(), N_BITS);
        assert_eq!(b.len(), N_BITS);
        let mut circuit = Circuit::empty();
        let wires = circuit.extend(half_adder(a[0].clone(), b[0].clone()));
        circuit.add_wire(wires[0].clone());
        let mut carry = wires[1].clone();
        for i in 1..N_BITS {
            let wires = circuit.extend(full_adder(a[i].clone(), b[i].clone(),carry));
            circuit.add_wire(wires[0].clone());
            carry = wires[1].clone();
        }
        circuit.add_wire(carry);
        circuit
    }

    pub fn add_constant(a: Wires, b: BigUint) -> Circuit {
        assert_eq!(a.len(), N_BITS);
        assert_ne!(b, BigUint::ZERO);
        let mut circuit = Circuit::empty();

        let b_bits = bits_from_biguint(b);

        let mut carry = Rc::new(RefCell::new(Wire::new()));
        let mut first_one = 0;
        while !b_bits[first_one]  {
            first_one += 1;
        }

        for i in 0..N_BITS {
            if i < first_one {
                circuit.add_wire(a[i].clone());
            }
            else if i == first_one {
                let wire = Rc::new(RefCell::new(Wire::new()));
                circuit.add(Gate::new(a[i].clone(), a[i].clone(), wire.clone(), "inv".to_string()));
                circuit.add_wire(wire);
                carry = a[i].clone(); 
            }
            else {
                if b_bits[i] {
                    let wire_1 = Rc::new(RefCell::new(Wire::new()));
                    let wire_2 = Rc::new(RefCell::new(Wire::new()));
                    circuit.add(Gate::new(a[i].clone(), carry.clone(), wire_1.clone(), "xnor".to_string()));
                    circuit.add(Gate::new(a[i].clone(), carry.clone(), wire_2.clone(), "or".to_string()));
                    circuit.add_wire(wire_1);
                    carry = wire_2;
                }
                else {
                    let wire_1 = Rc::new(RefCell::new(Wire::new()));
                    let wire_2 = Rc::new(RefCell::new(Wire::new()));
                    circuit.add(Gate::new(a[i].clone(), carry.clone(), wire_1.clone(), "xor".to_string()));
                    circuit.add(Gate::new(a[i].clone(), carry.clone(), wire_2.clone(), "and".to_string()));
                    circuit.add_wire(wire_1);
                    carry = wire_2;
                }
            }
        }
        circuit.add_wire(carry);
        circuit
    }
}

#[cfg(test)]
mod tests {
    use crate::circuits::bigint::{utils::{biguint_from_wires, random_u254, wires_set_from_u254}, U254};

    #[test]
    fn test_add() {
        let a = random_u254();
        let b = random_u254();
        let circuit = U254::add(wires_set_from_u254(a.clone()), wires_set_from_u254(b.clone()));
        println!("gate count: {:?}", circuit.1.len());
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = biguint_from_wires(circuit.0);
        assert_eq!(c, a + b);
    }

    #[test]
    fn test_add_constant() {
        let a = random_u254();
        let b = random_u254();
        let circuit = U254::add_constant(wires_set_from_u254(a.clone()), b.clone());
        println!("gate count: {:?}", circuit.1.len());
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = biguint_from_wires(circuit.0);
        assert_eq!(c, a + b);
    }
}
