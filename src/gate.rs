use rand::Rng;
use blake3::hash;
use bitvm::{bigint::U256, hash::blake3::blake3_compute_script_with_limb, treepp::*, u4::u4_logic::{u4_drop_full_logic_table, u4_drop_full_lookup, u4_full_table_operation, u4_push_full_lookup, u4_push_full_xor_table}};

use crate::utils::xor;

pub struct Wire {
    pub label0: Vec<u8>,
    pub label1: Vec<u8>,
    pub hash0: Vec<u8>,
    pub hash1: Vec<u8>,
}

impl Wire {
    pub fn new() -> Self {
        let label0 = rand::rng().random::<[u8; 32]>().to_vec();
        let label1 = rand::rng().random::<[u8; 32]>().to_vec();
        let h0 = hash(&label0);
        let hash0 = h0.as_bytes().to_vec();
        let h1 = hash(&label1);
        let hash1 = h1.as_bytes().to_vec();
        Self {
            label0,
            label1,
            hash0,
            hash1
        }
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
        let mut result = Vec::new();
        for a in [false, true] {
            for b in [false, true] {
                let mut h = if a {self.wire_a.label1.clone()} else {self.wire_a.label0.clone()};
                h.extend(if b {self.wire_b.label1.clone()} else {self.wire_b.label0.clone()});
                let hash_h = hash(&h);
                let hash_ab = hash_h.as_bytes();
                let c = (self.f)(a, b);
                result.push(xor(if c {self.wire_c.label1.clone()} else {self.wire_c.label0.clone()}, hash_ab.to_vec()));
            }
        }
        result
    }

    pub fn script(&self, _garbled: Vec<Vec<u8>>, correct: Vec<u8>, limb_len: u8) -> Script {
        let input_len = 255 / limb_len + 1;
        // expects label_a and label_b as input, can be executed if none of the rows in the garbled gate passes, operator has to ensure it is a valid garble
        script! {
            // put a to altstack
            for _ in 0..2*input_len {
                OP_TOALTSTACK
            }
            // copy b
            for _ in 0..2*input_len {
                { 2*input_len-1 } OP_PICK
            }
            // put b to altstack
            for _ in 0..2*input_len {
                OP_TOALTSTACK
            }
            // hash b
            { blake3_compute_script_with_limb(32, limb_len) }
            // transform to 9-limb form
            { U256::transform_limbsize(4, 29) }
            // push possible hash values (may need to randomize the order)
            { U256::push_hex(&hex::encode(self.wire_b.hash0.clone())) }
            { U256::push_hex(&hex::encode(self.wire_b.hash1.clone())) }
            // check hash is one of these
            { U256::copy(2) }
            { U256::equal(0, 1) }
            OP_TOALTSTACK
            { U256::equal(0, 1) }
            OP_FROMALTSTACK
            OP_BOOLOR
            OP_VERIFY
            // pop b and a from altstack
            for _ in 0..2*input_len {
                OP_FROMALTSTACK
            }
            for _ in 0..2*input_len {
                OP_FROMALTSTACK
            }
            // switch the order
            for _ in 0..2*input_len {
                { 4*input_len-1 } OP_ROLL
            }
            // put b to altstack
            for _ in 0..2*input_len {
                OP_TOALTSTACK
            }
            // copy a
            for _ in 0..2*input_len {
                { 2*input_len-1 } OP_PICK
            }
            // put a to altstack
            for _ in 0..2*input_len {
                OP_TOALTSTACK
            }
            // hash a
            { blake3_compute_script_with_limb(32, limb_len) }
            // transform to 9-limb form
            { U256::transform_limbsize(4, 29) }
            // push possible hash values (may need to randomize the order)
            { U256::push_hex(&hex::encode(self.wire_a.hash0.clone())) }
            { U256::push_hex(&hex::encode(self.wire_a.hash1.clone())) }
            // check hash is one of these
            { U256::copy(2) }
            { U256::equal(0, 1) }
            OP_TOALTSTACK
            { U256::equal(0, 1) }
            OP_FROMALTSTACK
            OP_BOOLOR
            OP_VERIFY
            // pop a and b from altstack and drop appended zeroes
            for _ in 0..2*input_len {
                OP_FROMALTSTACK
            }
            for _ in 0..input_len {
                OP_DROP
            }
            for _ in 0..2*input_len {
                OP_FROMALTSTACK
            }
            for _ in 0..input_len {
                OP_DROP
            }
            // hash a|b
            { blake3_compute_script_with_limb(64, limb_len) }
            // push garbled row (pushing the correct one for now)
            for byte in correct {
                { byte / 16 }
                { byte % 16 }
            }
            // put hash and garbled row to altstack
            for _ in 0..64 {
                OP_TOALTSTACK
            }
            for _ in 0..64 {
                OP_TOALTSTACK
            }
            // push xor table and lookup
            { u4_push_full_xor_table() }
            { u4_push_full_lookup()}
            // pop hash and garbled row from altstack
            for _ in 0..64 {
                OP_FROMALTSTACK
            }
            for _ in 0..64 {
                OP_FROMALTSTACK
            }
            // zip them
            for i in 0..64 {
                127 OP_ROLL
                { 64+i } OP_ROLL
            }
            // xor
            for i in 0..64 {
                { u4_full_table_operation(127-2*i, 127-2*i+16) }
                OP_TOALTSTACK
            }
            // drop xor table and lookup
            { u4_drop_full_lookup() }
            { u4_drop_full_logic_table() }
            // get result from altstack
            for _ in 0..64 {
                OP_FROMALTSTACK
            }
            // prepare it for hashing, pad zeroes and hash it
            for _ in 0..8 {
                57 OP_ROLL
                57 OP_ROLL
                59 OP_ROLL
                59 OP_ROLL
                61 OP_ROLL
                61 OP_ROLL
                63 OP_ROLL
                63 OP_ROLL
            }
            for _ in 0..64 {
                0
            }
            { blake3_compute_script_with_limb(32, 4) }
            // transform to 9-limb form
            { U256::transform_limbsize(4, 29) }
            // push possible hash values (may need to randomize the order)
            { U256::push_hex(&hex::encode(self.wire_c.hash0.clone())) }
            { U256::push_hex(&hex::encode(self.wire_c.hash1.clone())) }
            // check hash is one of these
            { U256::copy(2) }
            { U256::equal(0, 1) }
            OP_TOALTSTACK
            { U256::equal(0, 1) }
            OP_FROMALTSTACK
            OP_BOOLOR
            OP_NOT // (this time check it is neither of them)
            // OP_VERIFY
        }
    }
}

#[cfg(test)]
mod tests {
    use bitvm::hash::blake3::blake3_push_message_script_with_limb;

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
        let correct = garbled[1].clone();
        garbled.shuffle(&mut rng());

        let limb_len = 29;
        let gate_script = gate.script(garbled, correct, limb_len);

        let script = script! {
            { blake3_push_message_script_with_limb(&gate.wire_b.label1, limb_len) }
            { blake3_push_message_script_with_limb(&gate.wire_a.label0, limb_len) }
            { gate_script }
            OP_NOT
        };

        println!("script len: {:?}", script.len());
        let result = execute_script(script);
        // for (i, a) in result.final_stack.0.iter_str().enumerate() {
        //     if i % 32 == 31 {
        //         println!(", {:?}", a);
        //     }
        //     else if i % 32 == 0 {
        //         print!("stack[{}]: {:?}", i / 32, a);
        //     }
        //     else {
        //         print!(", {:?}", a);
        //     }
        // }
        // println!("");
        assert!(result.success);
    }
}
