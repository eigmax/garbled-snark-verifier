use std::str::FromStr;
use num_bigint::BigUint;
use crate::{bag::*, circuits::{basic::{full_adder, full_subtracter, half_adder, half_subtracter}, bigint::utils::{bits_from_biguint, wires_for_u254, wires_set_from_u254}}};
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
                circuit.add(Gate::not(a[i].clone(), wire.clone()));
                circuit.add_wire(wire);
                carry = a[i].clone(); 
            }
            else {
                if b_bits[i] {
                    let wire_1 = Rc::new(RefCell::new(Wire::new()));
                    let wire_2 = Rc::new(RefCell::new(Wire::new()));
                    circuit.add(Gate::xnor(a[i].clone(), carry.clone(), wire_1.clone()));
                    circuit.add(Gate::or(a[i].clone(), carry.clone(), wire_2.clone()));
                    circuit.add_wire(wire_1);
                    carry = wire_2;
                }
                else {
                    let wire_1 = Rc::new(RefCell::new(Wire::new()));
                    let wire_2 = Rc::new(RefCell::new(Wire::new()));
                    circuit.add(Gate::xor(a[i].clone(), carry.clone(), wire_1.clone()));
                    circuit.add(Gate::and(a[i].clone(), carry.clone(), wire_2.clone()));
                    circuit.add_wire(wire_1);
                    carry = wire_2;
                }
            }
        }
        circuit.add_wire(carry);
        circuit
    }

    pub fn sub(a: Wires, b: Wires) -> Circuit {
        assert_eq!(a.len(), N_BITS);
        assert_eq!(b.len(), N_BITS);
        let mut circuit = Circuit::empty();
        let wires = circuit.extend(half_subtracter(a[0].clone(), b[0].clone()));
        circuit.add_wire(wires[0].clone());
        let mut borrow = wires[1].clone();
        for i in 1..N_BITS {
            let wires = circuit.extend(full_subtracter(a[i].clone(), b[i].clone(), borrow));
            circuit.add_wire(wires[0].clone());
            borrow = wires[1].clone();
        }
        circuit.add_wire(borrow);
        circuit
    }

    pub fn half(a: Wires) -> Circuit {
        assert_eq!(a.len(), N_BITS);
        let mut circuit = Circuit::empty();
        let not_a = Rc::new(RefCell::new(Wire::new()));
        let zero_wire = Rc::new(RefCell::new(Wire::new()));
        circuit.add(Gate::not(a[0].clone(), not_a.clone())); 
        circuit.add(Gate::and(a[0].clone(), not_a.clone(), zero_wire.clone())); 
        circuit.add_wires(a[1..N_BITS].to_vec());
        circuit.add_wire(zero_wire);
        circuit
    }

    pub fn odd_part(a: Wires) -> Circuit {
        assert_eq!(a.len(), N_BITS);
        let mut circuit = Circuit::empty();
        let mut select = wires_for_u254();
        let not_select = wires_for_u254();
        select[0] = a[0].clone();
        for i in 1..N_BITS {
            circuit.add(Gate::or(select[i-1].clone(), a[i].clone(), select[i].clone()));
        }

        for i in 0..N_BITS {
            circuit.add(Gate::not(select[i].clone(), not_select[i].clone()));
        }

        let k = wires_for_u254();
        for i in 0..N_BITS-1 {
            circuit.add(Gate::and(not_select[i].clone(), a[i+1].clone(), k[i].clone()));
        }

        let mut result = wires_for_u254();
        for i in 0..N_BITS {
            let half_result = circuit.extend(Self::half(result.clone()));
            result = circuit.extend( Self::select( result.clone(), half_result, select[i].clone()));
        }
        circuit.add_wires(result.clone());
        circuit.add_wires(k.clone());
        circuit
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use num_bigint::BigUint;

    use crate::circuits::bigint::{utils::{biguint_from_wires, random_u254, wires_set_from_u254}, U254};

    #[test]
    fn test_add() {
        let a = random_u254();
        let b = random_u254();
        let circuit = U254::add(wires_set_from_u254(a.clone()), wires_set_from_u254(b.clone()));
        circuit.print_gate_type_counts();
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
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = biguint_from_wires(circuit.0);
        assert_eq!(c, a + b);
    }

    #[test]
    fn test_sub() {
        let mut a = random_u254();
        let mut b = random_u254();
        if a < b {
            (a, b) = (b, a);
        }
        let circuit = U254::sub(wires_set_from_u254(a.clone()), wires_set_from_u254(b.clone()));
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = biguint_from_wires(circuit.0);
        assert_eq!(c, a - b);
    }

    #[test]
    fn test_half() {
        let a = random_u254();
        let circuit = U254::half(wires_set_from_u254(a.clone()));
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = biguint_from_wires(circuit.0);
        let x = (a.clone() - (c.clone() + c.clone() )) == BigUint::from_str("1").unwrap();
        let y = (a - (c.clone() + c )) == BigUint::from_str("0").unwrap();
        assert!(x | y)
    }

    #[test]
    fn test_odd_part() {
        let a = random_u254();
        let circuit = U254::odd_part(wires_set_from_u254(a.clone()));
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = biguint_from_wires(circuit.0[0..U254::N_BITS].to_vec());
        let d = biguint_from_wires(circuit.0[U254::N_BITS..2*U254::N_BITS].to_vec());
        println!("a= {:?}" , a);
        println!("c= {:?}" , c);
        println!("d= {:?}" , d);
        println!("cd= {:?}" ,c.clone()* d.clone());
        assert_eq!(a , c.clone() *d.clone() + c*d.clone());
    }
}
