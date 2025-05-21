use std::{iter::zip, ops::Add};
use rand::{seq::SliceRandom, Rng};
use blake3::hash;
use bitvm::{bigint::U256, hash::blake3::blake3_compute_script_with_limb, treepp::*};

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

#[derive(Clone)]
pub struct S {
    pub s: [u8; 32],
}

impl S {
    pub fn new(s: [u8; 32]) -> Self {
        Self {
            s
        }
    }

    pub const fn zero() -> Self {
        Self {
            s: [0_u8; 32]
        }
    }

    pub const fn one() -> Self {
        let mut s = [0_u8; 32];
        s[31] = 1;
        Self {
            s
        }
    }

    pub const fn delta() -> Self {
        Self {
            s: [7_u8; 32]
        }
    }

    pub fn random() -> Self {
        Self {
            s: rand::rng().random::<[u8; 32]>()
        }
    }

    pub fn lsb(&self) -> bool {
        self.s[31] % 2 == 1
    }

    pub fn neg(&self) -> Self {
        let mut s = self.s.clone();
        for i in 0..32 {
            s[i] = 255 - self.s[i];
        }
        let x = Self {
            s
        };
        x + Self::one()
    }

    pub fn sign_change(&self, selector: bool) -> Self {
        if selector {
            self.neg()
        }
        else {
            self.clone()
        }
    }

    pub fn hash(&self) -> Self {
        let h = hash(&self.s);
        Self {
            s: *h.as_bytes()
        }
    }

    pub fn hash_together(a: Self, b: Self) -> Self {
        let mut h = a.s.to_vec();
        h.extend(b.s.to_vec());
        let hash_h = hash(&h);
        Self {
            s: *hash_h.as_bytes()
        }
    }
}

impl Add for S {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let mut s = [0_u8; 32];
        let mut carry = 0;
        for (i, (u, v)) in zip(self.s, rhs.s).enumerate().rev() {
            let x = (u as u32) + (v as u32) + carry;
            s[i] = (x % 256) as u8;
            carry = x / 256;
        }
        Self {
            s
        }
    }
}

// global offset, DELTA.lsb()=1;
static DELTA: S = S::delta();
const LIMB_LEN: u8 = 29;
const N_LIMBS: u8 = 9;

pub struct Wire {
    pub l0: S,
    pub l1: S,
    pub hash0: S,
    pub hash1: S,
}

impl Wire {
    pub fn new() -> Self {
        let l0 = S::random();
        let l1 = l0.clone() + DELTA.sign_change(l0.lsb());
        let hash0 = l0.hash();
        let hash1 = l1.hash();
        Self {
            l0,
            l1,
            hash0,
            hash1
        }
    }
}

impl Wire {
    pub fn select(&self, selector: bool) -> S {
        if selector {
            self.l1.clone()
        }
        else {
            self.l0.clone()
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

    pub fn garbled(&self) -> Vec<S> {
        let mut result = Vec::new();
        let lsb_a = self.wire_a.l0.lsb();
        let lsb_b = self.wire_b.l0.lsb();
        for (mi, mj) in [(false, false), (true, false), (false, true), (true, true)] {
            let i = lsb_a ^ mi;
            let j = lsb_b ^ mj;
            let k = (self.f)(i, j);
            let a = self.wire_a.select(i);
            let b = self.wire_b.select(j);
            let c = self.wire_c.select(k);
            let garbled_row = S::hash_together(a, b) + c.neg();
            result.push(garbled_row);
        }
        result
    }

    pub fn script(&self, garbled: Vec<S>) -> Script {
        let mut hash_a = vec![self.wire_a.hash0.s.clone(), self.wire_a.hash1.s.clone()];
        hash_a.shuffle(&mut rand::rng());
        let mut hash_b = vec![self.wire_b.hash0.s.clone(), self.wire_b.hash1.s.clone()];
        hash_b.shuffle(&mut rand::rng());
        let mut hash_c = vec![self.wire_c.hash0.s.clone(), self.wire_c.hash1.s.clone()];
        hash_c.shuffle(&mut rand::rng());

        // inputs: B, A
        // if Hash(Hash(A||B)-tau_{a+2b}) is not equal to wire_c.hash0 or wire_c.hash1 (a=lsb(A) and b=lsb(B)), this script is executable
        script! {
            // B A
            for _ in 0..2*N_LIMBS {
                OP_TOALTSTACK
            }
            // B | A
            for _ in 0..2*N_LIMBS {
                { 2*N_LIMBS-1 } OP_PICK
            }
            // B B | A
            for _ in 0..2*N_LIMBS {
                OP_TOALTSTACK
            }
            // B | B A
            { blake3_compute_script_with_limb(32, LIMB_LEN) }
            { U256::transform_limbsize(4, 29) } // transform to 9-limb form
            // hB | B A
            { U256::push_hex(&hex::encode(hash_b[0])) }
            { U256::push_hex(&hex::encode(hash_b[1])) }
            // hB hB? hB? | B A
            { U256::copy(2) }
            { U256::equal(0, 1) }
            OP_TOALTSTACK
            { U256::equal(0, 1) }
            OP_FROMALTSTACK
            OP_BOOLOR
            OP_VERIFY
            // | B A
            for _ in 0..2*N_LIMBS {
                OP_FROMALTSTACK
            }
            for _ in 0..2*N_LIMBS {
                OP_FROMALTSTACK
            }
            // B A
            for _ in 0..2*N_LIMBS {
                { 4*N_LIMBS-1 } OP_ROLL
            }
            // A B
            for _ in 0..2*N_LIMBS {
                OP_TOALTSTACK
            }
            // A | B
            for _ in 0..2*N_LIMBS {
                { 2*N_LIMBS-1 } OP_PICK
            }
            // A A | B
            for _ in 0..2*N_LIMBS {
                OP_TOALTSTACK
            }
            // A | A B
            { blake3_compute_script_with_limb(32, LIMB_LEN) }
            { U256::transform_limbsize(4, 29) } // transform to 9-limb form
            // hA | A B
            { U256::push_hex(&hex::encode(hash_a[0])) }
            { U256::push_hex(&hex::encode(hash_a[1])) }
            // hA hA? hA? | A B
            { U256::copy(2) }
            { U256::equal(0, 1) }
            OP_TOALTSTACK
            { U256::equal(0, 1) }
            OP_FROMALTSTACK
            OP_BOOLOR
            OP_VERIFY
            // | A B
            for _ in 0..2*N_LIMBS {
                OP_FROMALTSTACK
            }
            for _ in 0..N_LIMBS {
                OP_DROP
            }
            // A | B
            for _ in 0..2*N_LIMBS {
                OP_FROMALTSTACK
            }
            for _ in 0..N_LIMBS {
                OP_DROP
            }
            // A B
            { U256::copy(0) }
            { convert_between_blake3_and_normal_form() } 
            { U256::div2rem() }
            OP_TOALTSTACK
            { U256::drop() }
            { U256::copy(1) }
            { convert_between_blake3_and_normal_form() } 
            { U256::div2rem() }
            OP_TOALTSTACK
            { U256::drop() }
            // A B | a b
            { blake3_compute_script_with_limb(64, LIMB_LEN) }
            { U256::transform_limbsize(4, 29) }
            // hAB | a b
            { U256::push_hex(&hex::encode(garbled[0].s)) }
            { U256::push_hex(&hex::encode(garbled[1].s)) }
            { U256::push_hex(&hex::encode(garbled[2].s)) }
            { U256::push_hex(&hex::encode(garbled[3].s)) }
            // hAB tau0 tau1 tau2 tau3
            OP_FROMALTSTACK OP_FROMALTSTACK
            OP_IF
                OP_IF
                // tau3
                { U256::toaltstack() }
                { U256::drop() }
                { U256::drop() }
                { U256::drop() }
                { U256::fromaltstack() }
                OP_ELSE
                // tau2
                { U256::drop() }
                { U256::toaltstack() }
                { U256::drop() }
                { U256::drop() }
                { U256::fromaltstack() }
                OP_ENDIF
            OP_ELSE
                OP_IF
                // tau1
                { U256::drop() }
                { U256::drop() }
                { U256::toaltstack() }
                { U256::drop() }
                { U256::fromaltstack() }
                OP_ELSE
                // tau0
                { U256::drop() }
                { U256::drop() }
                { U256::drop() }
                OP_ENDIF
            OP_ENDIF
            // hAB tau_{a+2b}
            { U256::sub(1, 0) }
            // C=hAB-tau_{a+2b}
            { convert_between_blake3_and_normal_form() }
            for _ in 0..N_LIMBS { 0 }
            { blake3_compute_script_with_limb(32, LIMB_LEN) }
            { U256::transform_limbsize(4, 29) } // transform to 9-limb form
            // hC
            { U256::copy(0) }
            // hC hC
            { U256::push_hex(&hex::encode(hash_c[0])) }
            // hC hC hC?
            { U256::notequal(0, 1) } OP_VERIFY
            // hC
            { U256::push_hex(&hex::encode(hash_c[1])) }
            // hC hC?
            { U256::notequal(0, 1) } OP_VERIFY
            OP_TRUE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bitvm::hash::blake3::blake3_push_message_script_with_limb;

    #[test]
    fn test_gate() {
        fn and(a: bool, b: bool) -> bool {
            return a & b;
        }
        let wire_1 = Wire::new();
        let wire_2 = Wire::new();
        let wire_3 = Wire::new();
        let gate = Gate::new(wire_1, wire_2, wire_3, and);

        let correct_garbled = gate.garbled();
        let incorrect_garbled = vec![S::random(), S::random(), S::random(), S::random()];

        for (expected_result, garbled) in [(false, correct_garbled), (true, incorrect_garbled)] {
            let gate_script = gate.script(garbled);

            for a in [gate.wire_a.l0.clone(), gate.wire_a.l1.clone()] {
                for b in [gate.wire_b.l0.clone(), gate.wire_b.l1.clone()] {
                    let script = script! {
                        { blake3_push_message_script_with_limb(&b.s, LIMB_LEN) }
                        { blake3_push_message_script_with_limb(&a.s, LIMB_LEN) }
                        { gate_script.clone() }
                    };

                    println!("script len: {:?}", script.len());
                    let result = execute_script(script);
                    assert_eq!(expected_result, result.success);
                }
            }
        }
    }
}
