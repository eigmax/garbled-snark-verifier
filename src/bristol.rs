use std::{cell::RefCell, fs, rc::Rc};
use crate::{circuit::Circuit, gate::Gate, wire::Wire};

pub fn parser(filename: &str) -> Circuit {
    let data = fs::read_to_string(filename).expect("error");
    let mut lines = data.lines();

    let mut words = lines.next().unwrap().split_whitespace();
    let nog: usize = words.next().unwrap().parse().unwrap();
    let now: usize = words.next().unwrap().parse().unwrap();
    let mut wires = Vec::new();
    for _ in 0..now {
        wires.push(Rc::new(RefCell::new(Wire::new())));
    }

    let mut input_sizes = Vec::<usize>::new();
    let mut words = lines.next().unwrap().split_whitespace();
    for _ in 0..words.next().unwrap().parse().unwrap() {
        let x: usize = words.next().unwrap().parse().unwrap();
        input_sizes.push(x);
    }

    let mut output_sizes = Vec::<usize>::new();
    let mut words = lines.next().unwrap().split_whitespace();
    for _ in 0..words.next().unwrap().parse().unwrap() {
        let x: usize = words.next().unwrap().parse().unwrap();
        output_sizes.push(x);
    }

    let mut i = 0;
    let mut gates = Vec::new();
    while i < nog {
        let line = lines.next().unwrap();
        if line.is_empty() {
            continue;
        }
        let mut words = line.split_whitespace();
        let noi: usize = words.next().unwrap().parse().unwrap();
        let noo: usize = words.next().unwrap().parse().unwrap();
        let mut input_wires: Vec<usize> = Vec::new();
        for _ in 0..noi {
            input_wires.push(words.next().unwrap().parse().unwrap());
        }
        let mut output_wires: Vec<usize> = Vec::new();
        for _ in 0..noo {
            output_wires.push(words.next().unwrap().parse().unwrap());
        }
        let gate_type = words.next().unwrap().to_lowercase();
        if gate_type == "and" {
            let gate = Gate::and(wires[input_wires[0]].clone(), wires[input_wires[1]].clone(), wires[output_wires[0]].clone());
            gates.push(gate);
        }
        else if gate_type == "xor" {
            let gate = Gate::xor(wires[input_wires[0]].clone(), wires[input_wires[1]].clone(), wires[output_wires[0]].clone());
            gates.push(gate);
        }
        else if gate_type == "inv" {
            let gate = Gate::not(wires[input_wires[0]].clone(), wires[output_wires[0]].clone());
            gates.push(gate);
        }
        i += 1;
    }
    Circuit {
        nog,
        now,
        input_sizes,
        output_sizes,
        wires,
        gates,
    }
}

#[cfg(test)]
mod tests {
    use rand::{rng, Rng};
    use super::*;

    #[test]
    fn test_bristol_adder() {
        let adder_circuit = parser("adder64.txt");
        let a: u64 = rng().random();
        let b: u64 = rng().random();
        for i in 0..adder_circuit.input_sizes[0] {
            adder_circuit.wires[i].borrow_mut().set_value((a >> i) & 1 == 1);
        }
        for (i, j) in (adder_circuit.input_sizes[0]..(adder_circuit.input_sizes[0]+adder_circuit.input_sizes[1])).enumerate() {
            adder_circuit.wires[j].borrow_mut().set_value((b >> i) & 1 == 1);
        }
        for mut gate in adder_circuit.gates {
            gate.evaluate();
        }
        let mut result_bits = Vec::new();
        for i in (adder_circuit.now-adder_circuit.output_sizes[0])..adder_circuit.now {
            result_bits.push(adder_circuit.wires[i].borrow().get_value());
        }
        let mut c: u64 = 0;
        for bit in result_bits.iter().rev() {
            c = 2 * c + if *bit {1} else {0};
        }
        assert_eq!(c, a.wrapping_add(b));
    }

    #[test]
    fn test_bristol_multiplier() {
        let adder_circuit = parser("multiplier64.txt");
        let a: u64 = rng().random();
        let b: u64 = rng().random();
        for i in 0..adder_circuit.input_sizes[0] {
            adder_circuit.wires[i].borrow_mut().set_value((a >> i) & 1 == 1);
        }
        for (i, j) in (adder_circuit.input_sizes[0]..(adder_circuit.input_sizes[0]+adder_circuit.input_sizes[1])).enumerate() {
            adder_circuit.wires[j].borrow_mut().set_value((b >> i) & 1 == 1);
        }
        for mut gate in adder_circuit.gates {
            gate.evaluate();
        }
        let mut result_bits = Vec::new();
        for i in (adder_circuit.now-adder_circuit.output_sizes[0])..adder_circuit.now {
            result_bits.push(adder_circuit.wires[i].borrow().get_value());
        }
        let mut c: u64 = 0;
        for bit in result_bits.iter().rev() {
            c = 2 * c + if *bit {1} else {0};
        }
        assert_eq!(c, a.wrapping_mul(b));
    }

    #[test]
    fn test_bristol_subtracter() {
        let adder_circuit = parser("subtracter64.txt");
        let a: u64 = rng().random();
        let b: u64 = rng().random();
        for i in 0..adder_circuit.input_sizes[0] {
            adder_circuit.wires[i].borrow_mut().set_value((a >> i) & 1 == 1);
        }
        for (i, j) in (adder_circuit.input_sizes[0]..(adder_circuit.input_sizes[0]+adder_circuit.input_sizes[1])).enumerate() {
            adder_circuit.wires[j].borrow_mut().set_value((b >> i) & 1 == 1);
        }
        for mut gate in adder_circuit.gates {
            gate.evaluate();
        }
        let mut result_bits = Vec::new();
        for i in (adder_circuit.now-adder_circuit.output_sizes[0])..adder_circuit.now {
            result_bits.push(adder_circuit.wires[i].borrow().get_value());
        }
        let mut c: u64 = 0;
        for bit in result_bits.iter().rev() {
            c = 2 * c + if *bit {1} else {0};
        }
        assert_eq!(c, a.wrapping_sub(b));
    }
}

