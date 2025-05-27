use std::{cell::RefCell, rc::Rc};
use rand::{rng, Rng};
use crate::{bristol::parser, gate::Gate, wire::Wire, s::S};

pub struct Circuit {
    pub nog: usize,
    pub now: usize,
    pub input_sizes: Vec<usize>,
    pub output_sizes: Vec<usize>,
    pub wires: Vec<Rc<RefCell<Wire>>>,
    pub gates: Vec<Gate>
}

impl Circuit {
    pub fn from_bristol(filename: &str) -> Self {
        parser(filename)
    }

    pub fn public_data(&self) -> (Vec<Vec<S>>, Vec<Vec<S>>) {
        let wire_public = self.wires.iter().map(|wire| wire.borrow().public_data()).collect();
        let gate_public= self.gates.iter().map(|gate| gate.garbled()).collect();
        (wire_public, gate_public)
    }

    pub fn set_input_wires(&self) {
        for i in 0..self.input_sizes.iter().sum() {
            self.wires[i].borrow_mut().set(rng().random());
        }
    }
}

#[cfg(test)]
mod tests {
    use std::iter::zip;
    use bitvm::bigint::U256;
    use bitvm::treepp::*;
    use super::*;

    fn test_circuit(circuit_filename: &str) {
        // println!("testing {:?}", circuit_filename);
        // let circuit = Circuit::from_bristol(circuit_filename);

        // let public_data = circuit.public_data();

        // let mut incorrect_public_data = public_data.clone();
        // let u: u32 = rng().random();
        // incorrect_public_data[(u as usize) % public_data.len()].0 = vec![S::random(), S::random(), S::random(), S::random()];

        // circuit.set_input_wires();

        // let gate_constant_script = Gate::constant_script();

        // for (correct, pd) in [(true, public_data), (false, incorrect_public_data)] {
        //     println!("testing {:?} garble", if correct {"correct"} else {"incorrect"});
        //     for (i, (gate, gpd)) in zip(circuit.gates.clone(), pd).enumerate() {
        //         let (garble, _, _, wire_c_public) = gpd.clone();
        //         let (garble_check, c) = gate.check_garble(garble, wire_c_public);
        //         let gate_script = Gate::script(gpd, garble_check, gate_constant_script.clone());
        //         let script = script! {
        //             { U256::push_hex(&hex::encode(&gate.wire_b.borrow().get_label().s)) }
        //             { U256::push_hex(&hex::encode(&gate.wire_a.borrow().get_label().s)) }
        //         }.push_script(gate_script);
        //         let result = execute_script(script);
        //         assert!(result.success);
        //         println!("testing gate[{:?}], garble is {:?}", i, if garble_check {"correct"} else {"incorrect"});
        //         if garble_check {
        //             gate.wire_c.borrow_mut().set_label(c);
        //         }
        //         else {
        //             assert!(!correct);
        //             break;
        //         }
        //     }
        // }
    }

    #[test]
    fn test_circuit_adder() {
        test_circuit("adder64.txt");
    }

    #[test]
    fn test_circuit_subtracter() {
        test_circuit("subtracter64.txt");
    }

    #[test]
    fn test_circuit_multiplier() {
        test_circuit("multiplier64.txt");
    }
}
