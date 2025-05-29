use crate::{bag::*, circuits::utils::{full_adder, half_adder}};
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

pub fn adder_2bit(input_wires: Vec<Rc<RefCell<Wire>>>) -> (Vec<Rc<RefCell<Wire>>>, Vec<Gate>) {
    assert_eq!(input_wires.len(), 4);
    let mut gates = Vec::new();
    let wire_a = input_wires[0].clone();
    let wire_b = input_wires[1].clone();
    let wire_c = input_wires[2].clone();
    let wire_d = input_wires[3].clone();
    let (wires_1, gates_1) = half_adder(vec![wire_a.clone(), wire_c.clone()]);
    let wire_e = wires_1[0].clone();
    let wire_f = wires_1[1].clone();
    gates.extend(gates_1);
    let (wires_2, gates_2) = full_adder(vec![wire_b.clone(), wire_d.clone(), wire_f]);
    let wire_g = wires_2[0].clone();
    let wire_h = wires_2[1].clone();
    gates.extend(gates_2);
    (vec![wire_e, wire_g, wire_h], gates)
}

#[cfg(test)]
mod tests {
    use num_bigint::BigUint;
    use rand::{rng, Rng};
    use crate::{bit_to_u8, circuits::bigint::U254};
    use super::*;

    fn random_biguint() -> BigUint {
        BigUint::from_bytes_le(&rand::rng().random::<[u8; 32]>())
    }

    fn bits_from_biguint(u: BigUint) -> Vec<bool> {
        let bytes = u.to_bytes_le();
        let mut bits = Vec::new();
        for byte in bytes {
            for i in 0..8 {
                bits.push(((byte >> i) & 1) == 1)
            }
        }
        bits
    }

    fn biguint_from_bits(bits: Vec<bool>) -> BigUint {
        let zero = BigUint::ZERO;
        let one = BigUint::from(1_u8);
        let mut u = zero.clone();
        for bit in bits.iter().rev() {
            u = u.clone() + u.clone() + if *bit {one.clone()} else {zero.clone()};
        }
        u
    }

    #[test]
    fn test_random_biguint() {
        let u = random_biguint();
        println!("u: {:?}", u);
        let b = bits_from_biguint(u.clone());
        let v = biguint_from_bits(b);
        println!("v: {:?}", v);
        assert_eq!(u, v);
    }

    #[test]
    fn test_adder_2bit() {
        let wire_a = Rc::new(RefCell::new(Wire::new()));
        let wire_b = Rc::new(RefCell::new(Wire::new()));
        let wire_c = Rc::new(RefCell::new(Wire::new()));
        let wire_d = Rc::new(RefCell::new(Wire::new()));
        let (wires, gates) = adder_2bit(vec![wire_a.clone(), wire_b.clone(), wire_c.clone(), wire_d.clone()]);

        let wire_e = wires[0].clone();
        let wire_f = wires[1].clone();
        let wire_g = wires[2].clone();

        let a = rng().random::<u8>() % 4;
        let b = rng().random::<u8>() % 4;
        let c = a + b;

        wire_a.borrow_mut().set((a & 1) == 1);
        wire_b.borrow_mut().set((a & 2) == 1);
        wire_c.borrow_mut().set((b & 1) == 1);
        wire_d.borrow_mut().set((b & 2) == 1);

        for mut gate in gates {
            gate.evaluate();
        }

        let d = bit_to_u8(wire_e.borrow().get_value()) + 2 * bit_to_u8(wire_f.borrow().get_value()) + 4 * bit_to_u8(wire_g.borrow().get_value());
        assert_eq!(c, d);
    }


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

        let a= biguint_from_bits(bits1);
        let b= biguint_from_bits(bits2);
        let result=a+b;
        let mut output_bits= bits_from_biguint(result);
        output_bits.pop();

        let (output_wires, gates) = U254::add(input_wires);

        for mut gate in gates {
            gate.evaluate();
        }
        for i in 0..U254::N_BITS+1 {
            assert_eq!( output_bits[i], output_wires[i].borrow().get_value());
        }
    }
}

