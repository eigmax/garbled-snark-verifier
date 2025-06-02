pub mod basic;
pub mod bigint;
pub mod bn254;

use crate::bag::{Gate, Wires, Wirex};

pub struct Circuit(Wires, Vec<Gate>);

impl Circuit {
    pub fn empty() -> Self {
        Self(Vec::new(), Vec::new())
    }

    pub fn new(wires: Wires, gates: Vec<Gate>) -> Self {
        Self(wires, gates)
    }

    pub fn extend(&mut self, circuit: Self) -> Wires {
        self.1.extend(circuit.1);
        circuit.0
    }

    pub fn add(&mut self, gate: Gate) {
        self.1.push(gate);
    }

    pub fn add_wire(&mut self, wire: Wirex) {
        self.0.push(wire);
    }

    pub fn add_wires(&mut self, wires: Wires) {
        self.0.extend(wires);
    }

    pub fn gate_count(&self) -> usize {
        self.1.len()
    }

    // this makes test run longer, comment out if you want to use it
    pub fn print_gate_type_counts(&self) {
        // for gate_type in ["and", "nand", "or", "xor", "xnor", "not"] {
        //     println!("{:?}\t: {:?}", gate_type, self.1.iter().filter(|gate| gate.name == gate_type).count());
        // }
        // println!("total gate count: {:?}", self.gate_count());
    }
}

