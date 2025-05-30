use crate::{bag::*, circuits::{bigint::U254, bn254::fq::Fq}};

pub struct Fq2;

impl Fq2 {
    pub fn add(input_wires: Vec<Rc<RefCell<Wire>>>) -> (Vec<Rc<RefCell<Wire>>>, Vec<Gate>) {
        assert_eq!( input_wires.len(), U254::N_BITS*4);
        let mut circuit_gates = Vec::new();
        let mut output_wires = Vec::new();
        let mut a = input_wires[0..U254::N_BITS].to_vec();
        let mut b = input_wires[U254::N_BITS..U254::N_BITS*2].to_vec();
        let c = input_wires[U254::N_BITS*2..U254::N_BITS*3].to_vec();
        let d = input_wires[U254::N_BITS*3..U254::N_BITS*4].to_vec();
        a.extend(c);
        b.extend(d);
        
        let (wires_1, gates_1) = Fq::add(a);
        circuit_gates.extend(gates_1);
        output_wires.extend(wires_1);
        let (wires_2 , gates_2) = Fq::add(b);
        circuit_gates.extend(gates_2);
        output_wires.extend(wires_2);
        (output_wires, circuit_gates)
    }

    pub fn mul(input_wires: Vec<Rc<RefCell<Wire>>>) -> (Vec<Rc<RefCell<Wire>>>, Vec<Gate>) {
        todo!();
    }
}


#[cfg(test)]
mod tests {
    use crate::circuits::bn254::utils::{bits_from_fq2, fq2_from_bits, random_fq2};
    use super::*;

    #[test]
    fn test_fq2_add() {
        let a = random_fq2();
        let b = random_fq2();
        let c = a + b;
        let mut input_wires = Vec::new();
        for bit in bits_from_fq2(a) {
            let wire = Rc::new(RefCell::new(Wire::new()));
            wire.borrow_mut().set(bit);
            input_wires.push(wire)
        }
        for bit in bits_from_fq2(b) {
            let wire = Rc::new(RefCell::new(Wire::new()));
            wire.borrow_mut().set(bit);
            input_wires.push(wire)
        }
        let (output_wires, gates) = Fq2::add(input_wires);
        println!("gate count: {:?}", gates.len());
        for mut gate in gates {
            gate.evaluate();
        }
        let d = fq2_from_bits(output_wires.iter().map(|output_wire| { output_wire.borrow().get_value() }).collect());
        println!("{:?} , {:?}" , c , d);
        assert_eq!(c, d);
    }    
}

