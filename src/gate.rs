use std::{cell::RefCell, rc::Rc};
use bitcoin::ScriptBuf;
use bitvm::{bigint::U256, hash::blake3::blake3_compute_script_with_limb, treepp::*};
use crate::{s::S, wire::Wire};

pub fn convert_between_blake3_and_normal_form() -> Script {
    script! {
        { U256::transform_limbsize(29, 8) }
        for _ in 0..8 {
            28 OP_ROLL
            29 OP_ROLL
            30 OP_ROLL
            31 OP_ROLL
        }
        { U256::transform_limbsize(8, 29) }
    }
}

const LIMB_LEN: u8 = 29;
const N_LIMBS: u8 = 9;

#[derive(Clone)]
pub struct Gate {
    pub wire_a: Rc<RefCell<Wire>>,
    pub wire_b: Rc<RefCell<Wire>>,
    pub wire_c: Rc<RefCell<Wire>>,
    pub name: String,
}

impl Gate {
    pub fn new(wire_a: Rc<RefCell<Wire>>, wire_b: Rc<RefCell<Wire>>, wire_c: Rc<RefCell<Wire>>, name: String) -> Self {
        Self {
            wire_a,
            wire_b,
            wire_c,
            name,
        }
    }

    pub fn f(&self) -> fn(bool, bool) -> bool {
        if self.name=="and" {
            fn and(a: bool, b: bool) -> bool {a & b};
            return and;
        }
        else if self.name=="or" {
            fn or(a: bool, b: bool) -> bool {a | b};
            return or;
        }
        else {
            fn empty(_a: bool, _b: bool) -> bool {false};
            return empty;
        }
    }

    pub fn evaluation_script(&self) -> Script {
        if self.name=="and" {
            script! { OP_BOOLAND }
        }
        else if self.name=="or" {
            script! { OP_BOOLOR }
        }
        else if self.name=="xor" {
            script! { OP_NUMNOTEQUAL }
        }
        else if self.name=="nand" {
            script! { OP_BOOLAND OP_NOT }
        }
        else {
            script! {}
        }
    }
    
    pub fn evaluate(&mut self) {
        self.wire_c.borrow_mut().set((self.f())(self.wire_a.borrow().get_value(), self.wire_b.borrow().get_value()));
    }

    pub fn garbled(&self) -> Vec<S> {
        let mut result = Vec::new();
        let lsb_a = self.wire_a.borrow().l0.lsb();
        let lsb_b = self.wire_b.borrow().l0.lsb();
        for (mi, mj) in [(false, false), (true, false), (false, true), (true, true)] {
            let i = lsb_a ^ mi;
            let j = lsb_b ^ mj;
            let k = (self.f())(i, j);
            let a = self.wire_a.borrow().select(i);
            let b = self.wire_b.borrow().select(j);
            let c = self.wire_c.borrow().select(k);
            let garbled_row = S::hash_together(a, b) + c.neg();
            result.push(garbled_row);
        }
        result
    }

    pub fn check_garble(&self, garble: Vec<S>, hash_c: Vec<S>) -> (bool, S) {
        let a = self.wire_a.borrow().get_label();
        let b = self.wire_b.borrow().get_label();
        let row = garble[(if a.lsb() {1} else {0})+2*(if b.lsb() {1} else {0})].clone();
        let c = S::hash_together(a, b) + row.neg();
        let hc = c.hash();
        (hc == hash_c[0] || hc == hash_c[1], c)
    }

    pub fn script(public_data: (Vec<S>, Vec<S>, Vec<S>, Vec<S>), correct: bool) -> Script {
        let (garbled, hash_a, hash_b, hash_c) = public_data;
        script! {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_gate() {
        let wire_1 = Rc::new(RefCell::new(Wire::new()));
        let wire_2 = Rc::new(RefCell::new(Wire::new()));
        let wire_3 = Rc::new(RefCell::new(Wire::new()));
        let gate = Gate::new(wire_1, wire_2, wire_3, "and".to_string());

        let public_data = gate.garbled();
        let mut incorrect_public_data = public_data.clone();
        incorrect_public_data  = vec![S::random(), S::random(), S::random(), S::random()];

        for (correct, public_data) in [(true, public_data), (false, incorrect_public_data)] {
            println!("testing {:?} garble", if correct {"correct"} else {"incorrect"});
            for a in [gate.wire_a.borrow().l0.clone(), gate.wire_a.borrow().l1.clone()] {
                for b in [gate.wire_b.borrow().l0.clone(), gate.wire_b.borrow().l1.clone()] {
                    // let gate_script = Gate::script(public_data.clone(), correct, gate_constant_script.clone());
                    // let script = script! {
                    //     { U256::push_hex(&hex::encode(&b.s)) }
                    //     { U256::push_hex(&hex::encode(&a.s)) }
                    // }.push_script(gate_script.clone());
                    // println!("script len: {:?}", script.len());
                    // let result = execute_script(script);
                    // assert!(result.success);
                }
            }
        }
    }
}
