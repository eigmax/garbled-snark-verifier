use num_bigint::BigUint;
use crate::circuits::bigint::utils::wires_for_u254;
use crate::circuits::bigint::U254;
use crate::{bag::*, circuits::basic::selector};
use super::BigIntImpl;

impl<const N_BITS: usize> BigIntImpl<N_BITS> {
    pub fn greater_than(a: Wires, b: Wires) -> Circuit {
        assert_eq!(a.len(), N_BITS);
        assert_eq!(b.len(), N_BITS);
        let mut circuit = Circuit::empty();

        let not_b = wires_for_u254();

        for i in 0..U254::N_BITS{
            circuit.add(Gate::not(b[i].clone(), not_b[i].clone()));
        }

        let wires = circuit.extend(U254::add(a, not_b));
        circuit.add_wire(wires[N_BITS].clone());
        circuit
    }

    pub fn less_than_constant(a: Wires, b: BigUint) -> Circuit {
        assert_eq!(a.len(), N_BITS);
        let mut circuit = Circuit::empty();

        let not_a = wires_for_u254();

        for i in 0..U254::N_BITS {
            circuit.add(Gate::not(a[i].clone(), not_a[i].clone()));
        }

        let wires = circuit.extend(U254::add_constant(not_a, b));
        circuit.add_wire(wires[N_BITS].clone());
        circuit
    }

    pub fn select(a: Wires, b: Wires, s: Wirex) -> Circuit {
        assert_eq!(a.len(), N_BITS);
        assert_eq!(b.len(), N_BITS);
        let mut circuit = Circuit::empty();
        
        for i in 0..U254::N_BITS {
            let wires = circuit.extend(selector(a[i].clone(), b[i].clone(), s.clone()));
            circuit.add_wire(wires[0].clone());
        }
        circuit
    }
}

#[cfg(test)]
mod tests {
    use crate::circuits::bigint::{utils::{biguint_from_wires, random_u254, wires_set_from_u254}, U254};
    use super::*;

    #[test]
    fn test_greater_than() {
        let a = random_u254();
        let b = random_u254();
        let circuit = U254::greater_than(wires_set_from_u254(a.clone()), wires_set_from_u254(b.clone()));
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        assert_eq!(a > b, circuit.0[0].borrow().get_value());
    }

    #[test]
    fn test_less_than_constant() {
        let a = random_u254();
        let b = random_u254();
        let circuit = U254::less_than_constant(wires_set_from_u254(a.clone()), b.clone());
        circuit.print_gate_type_counts();
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        assert_eq!(a < b, circuit.0[0].borrow().get_value());
    }

    #[test]
    fn test_select() {
        let a = random_u254();
        let b = random_u254();
        let s = Rc::new(RefCell::new(Wire::new()));
        s.borrow_mut().set(true);
        let circuit = U254::select(wires_set_from_u254(a.clone()), wires_set_from_u254(b.clone()), s);
        for mut gate in circuit.1 {
            gate.evaluate();
        }
        let c = biguint_from_wires(circuit.0);
        assert_eq!(a, c);
    }
}
