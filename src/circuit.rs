use std::{cell::RefCell, rc::Rc};
use bitvm::treepp::*;
use rand::{rng, Rng};
use crate::{bristol::parser, gate::{Gate, Wire, S}};

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

    pub fn public_data(&self) -> Vec<(Vec<S>, Vec<S>, Vec<S>, Vec<S>)> {
        self.gates.iter().map(|gate| gate.public_data()).collect()
    }

    pub fn scripts(&self, public_data: Vec<(Vec<S>, Vec<S>, Vec<S>, Vec<S>)>) -> Vec<Script> {
        public_data.iter().map(|pd| Gate::script(pd.clone())).collect()
    }

    pub fn set_input_wires(&self) {
        for i in 0..self.input_sizes.iter().sum() {
            self.wires[i].borrow_mut().set_value(rng().random());
        }
    }
}

#[cfg(test)]
mod tests {
    use std::iter::zip;
    use bitvm::bigint::U256;
    use super::*;

    #[test]
    fn test_circuit() {
        let circuit = Circuit::from_bristol("adder64.txt");

        let public_data = circuit.public_data();

        let mut incorrect_public_data = public_data.clone();
        let u: u32 = rng().random();
        incorrect_public_data[(u as usize) % public_data.len()].0 = vec![S::random(), S::random(), S::random(), S::random()];

        circuit.set_input_wires();

        // let scripts = circuit.scripts(public_data.clone());
            
        // for (script, (gate, (garble, _, _, wire_c_public))) in zip(scripts, zip(circuit.gates.clone(), public_data)) {
        //     let (garble_check, c) = gate.check_garble(garble, wire_c_public);
        //     let s = script! {
        //         { U256::push_hex(&hex::encode(&gate.wire_b.borrow().get_label().s)) }
        //         { U256::push_hex(&hex::encode(&gate.wire_a.borrow().get_label().s)) }
        //         { script }
        //     };
        //     let result = execute_script(s);
        //     if garble_check {
        //         gate.wire_c.borrow_mut().set_label(c);
        //         assert!(!result.success);
        //     }
        //     else {
        //         assert!(result.success);
        //         break;
        //     }
        // }

        for pd in [public_data, incorrect_public_data] {
            let scripts = circuit.scripts(pd.clone());
            
            for (script, (gate, (garble, _, _, wire_c_public))) in zip(scripts, zip(circuit.gates.clone(), pd)) {
                let (garble_check, c) = gate.check_garble(garble, wire_c_public);
                let s = script! {
                    { U256::push_hex(&hex::encode(&gate.wire_b.borrow().get_label().s)) }
                    { U256::push_hex(&hex::encode(&gate.wire_a.borrow().get_label().s)) }
                    { script }
                };
                let result = execute_script(s);
                if garble_check {
                    gate.wire_c.borrow_mut().set_label(c);
                    assert!(!result.success);
                }
                else {
                    assert!(result.success);
                    break;
                }
            }
        }
    }
}
