use rand::Rng;
use blake3::hash;
use bitvm::treepp::*;

use crate::utils::xor;

pub struct Wire {
    pub label0: Vec<u8>,
    pub label1: Vec<u8>,
}

impl Wire {
    pub fn new() -> Self {
        let label0 = rand::rng().random::<[u8; 32]>().to_vec();
        let label1 = rand::rng().random::<[u8; 32]>().to_vec();
        Self {
            label0,
            label1,
        }
    }

    pub fn labels(&self) -> (Vec<u8>, Vec<u8>) {
        (self.label0.clone(), self.label1.clone())
    }

    pub fn label_hashes(&self) -> (Vec<u8>, Vec<u8>) {
        let h0 = hash(&self.label0);
        let hash0 = h0.as_bytes();
        let h1 = hash(&self.label1);
        let hash1 = h1.as_bytes();
        (hash0.to_vec(), hash1.to_vec())
    }
}

pub struct Gate {
    pub wire_a: Wire,
    pub wire_b: Wire,
    pub wire_c: Wire,
    pub f: fn(bool, bool) -> bool,
}

impl Gate {
    pub fn new(wire_a: Wire, wire_b: Wire, wire_c: Wire, f: fn(bool, bool) -> bool) -> Self {
        Self {
            wire_a,
            wire_b,
            wire_c,
            f,
        }
    }

    pub fn garbled(&self) -> Vec<Vec<u8>> {
        let (wire_a_label0, wire_a_label1) = self.wire_a.labels();
        let (wire_b_label0, wire_b_label1) = self.wire_b.labels();
        let (wire_c_label0, wire_c_label1) = self.wire_c.labels();
        let mut result = Vec::new();
        for a in [false, true] {
            for b in [false, true] {
                let mut h = if a {wire_a_label1.clone()} else {wire_a_label0.clone()};
                h.extend(if b {wire_b_label1.clone()} else {wire_b_label0.clone()});
                let hash_h = hash(&h);
                let hash_ab = hash_h.as_bytes();
                let c = (self.f)(a, b);
                result.push(xor(if c {wire_c_label1.clone()} else {wire_c_label0.clone()}, hash_ab.to_vec()));
            }
        }
        result
    }

    pub fn script(&self, garbled: Vec<Vec<u8>>) -> Script {
        // expects label_a and label_b (it may expect them in a different form then bytes, i will decide that), can be executed if none of the rows in the garbled gate passes, operator has to ensure it is a valid garble
        script! {
            // .
        }
    }
}

#[cfg(test)]
mod tests {
    use bitvm::hash::blake3::{blake3_compute_script_with_limb, blake3_push_message_script_with_limb, blake3_verify_output_script};

    use super::*;
    use rand::{seq::SliceRandom, rng};

    #[test]
    fn test_gate() {
        fn and(a: bool, b: bool) -> bool {
            return a & b;
        }
        let wire_1 = Wire::new();
        let wire_2 = Wire::new();
        let wire_3 = Wire::new();
        let gate = Gate::new(wire_1, wire_2, wire_3, and);
        let mut garbled = gate.garbled();
        garbled.shuffle(&mut rng());
        for u in garbled.clone() {
            println!("u: {:?}", u);
        }
        let limb_len = 8;
        let gate_script = gate.script(garbled);
        let blake3_256_script = blake3_compute_script_with_limb(32, limb_len);
        let script = script! {
            { blake3_push_message_script_with_limb(&gate.wire_c.label0, limb_len) }
            { blake3_push_message_script_with_limb(&gate.wire_b.label1, limb_len) }
            { blake3_push_message_script_with_limb(&gate.wire_a.label0, limb_len) }
            // put a to altstack
            for _ in 0..32 {
                OP_TOALTSTACK
            }
            // put b to altstack
            for _ in 0..32 {
                OP_TOALTSTACK
            }
            // copy c
            for _ in 0..32 {
                31 OP_PICK
            }
            // hash c
            { blake3_256_script }
            // check hash
            // { blake3_verify_output_script(expected_hash) }
        };
    }
}
