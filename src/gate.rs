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
    pub f: fn(bool, bool) -> bool,
}

impl Gate {
    pub fn new(wire_a: Rc<RefCell<Wire>>, wire_b: Rc<RefCell<Wire>>, wire_c: Rc<RefCell<Wire>>, f: fn(bool, bool) -> bool) -> Self {
        Self {
            wire_a,
            wire_b,
            wire_c,
            f,
        }
    }

    pub fn and(wire_a: Rc<RefCell<Wire>>, wire_b: Rc<RefCell<Wire>>, wire_c: Rc<RefCell<Wire>>) -> Self {
        fn f(a: bool, b: bool) -> bool {a & b}
        Self::new(wire_a, wire_b, wire_c, f)
    }

    pub fn xor(wire_a: Rc<RefCell<Wire>>, wire_b: Rc<RefCell<Wire>>, wire_c: Rc<RefCell<Wire>>) -> Self {
        fn f(a: bool, b: bool) -> bool {a ^ b}
        Self::new(wire_a, wire_b, wire_c, f)
    }

    pub fn not(wire_a: Rc<RefCell<Wire>>, wire_c: Rc<RefCell<Wire>>) -> Self {
        fn f(a: bool, b: bool) -> bool {!(a & b)}
        Self::new(wire_a.clone(), wire_a.clone(), wire_c, f)
    }

    pub fn public_data(&self) -> (Vec<S>, Vec<S>, Vec<S>, Vec<S>) {
        (self.garbled(), self.wire_a.borrow().public_data(), self.wire_b.borrow().public_data(), self.wire_c.borrow().public_data())
    }
    
    pub fn evaluate(&mut self) {
        self.wire_c.borrow_mut().set_value((self.f)(self.wire_a.borrow().get_value(), self.wire_b.borrow().get_value()));
    }

    pub fn garbled(&self) -> Vec<S> {
        let mut result = Vec::new();
        let lsb_a = self.wire_a.borrow().l0.lsb();
        let lsb_b = self.wire_b.borrow().l0.lsb();
        for (mi, mj) in [(false, false), (true, false), (false, true), (true, true)] {
            let i = lsb_a ^ mi;
            let j = lsb_b ^ mj;
            let k = (self.f)(i, j);
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

    pub fn constant_script() -> (ScriptBuf, ScriptBuf, ScriptBuf, ScriptBuf) {
        let s0 = script! {
            { U256::copy(0) }                                      // B A A
            { U256::div2rem() }                                    // B A halfA a
            OP_TOALTSTACK { U256::drop() }                         // B A | a
            { U256::copy(1) }                                      // B A B | a
            { U256::div2rem() }                                    // B A halfB b | a
            OP_TOALTSTACK { U256::drop() }                         // B A | b a
            { convert_between_blake3_and_normal_form() }           // B A' | b a
            { U256::toaltstack() }                                 // B | A' b a
            { convert_between_blake3_and_normal_form() }           // B' | A' b a
            { U256::copy(0) } { U256::toaltstack() }               // B' | B' A' b a
            for _ in 0..N_LIMBS {0}                                // B'0 | B' A' b a
            { blake3_compute_script_with_limb(32, LIMB_LEN) }
            { U256::transform_limbsize(4, LIMB_LEN.into()) }       // hB | B' A' b a
        }.compile();
        let s1 = script! {
            { U256::copy(2) }
            { U256::equal(0, 1) }
            OP_TOALTSTACK
            { U256::equal(0, 1) }
            OP_FROMALTSTACK
            OP_BOOLOR
            OP_VERIFY                                              // | B' A' b a
            { U256::fromaltstack() } { U256::fromaltstack() }      // B' A' | b a
            { U256::roll(1) }                                      // A' B' | b a
            { U256::toaltstack() }                                 // A' | B' b a
            { U256::copy(0) } { U256::toaltstack() }               // A' | A' B' b a
            for _ in 0..N_LIMBS {0}                                // A'0 | A' B' b a
            { blake3_compute_script_with_limb(32, LIMB_LEN) }
            { U256::transform_limbsize(4, LIMB_LEN.into()) }       // hA | A' B' b a
        }.compile();
        let s2 = script! {
            { U256::copy(2) }
            { U256::equal(0, 1) }
            OP_TOALTSTACK
            { U256::equal(0, 1) }
            OP_FROMALTSTACK
            OP_BOOLOR
            OP_VERIFY                                              // | A' B' b a
            { U256::fromaltstack() } { U256::fromaltstack() }      // A' B' | b a
            { blake3_compute_script_with_limb(64, LIMB_LEN) }
            { U256::transform_limbsize(4, LIMB_LEN.into()) }       // hAB | b a
        }.compile();
        let s3 = script! {
            OP_FROMALTSTACK OP_FROMALTSTACK OP_SWAP                // hAB tau0 tau1 tau2 tau3 a b
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
            OP_ENDIF                                               // hAB tau
            { U256::sub(1, 0) }                                    // C=hAB-tau
            { convert_between_blake3_and_normal_form() }           // C'
            for _ in 0..N_LIMBS {0}                                // C'0
            { blake3_compute_script_with_limb(32, LIMB_LEN) }
            { U256::transform_limbsize(4, 29) }                    // hC
        }.compile();
        (s0, s1, s2, s3)
    }

    pub fn script(public_data: (Vec<S>, Vec<S>, Vec<S>, Vec<S>), correct: bool, s: (ScriptBuf, ScriptBuf, ScriptBuf, ScriptBuf)) -> ScriptBuf {
        let (garbled, hash_a, hash_b, hash_c) = public_data;

        script! {}.push_script(s.0).push_script(
            script! {
                { U256::push_hex(&hex::encode(hash_b[0].s)) }
                { U256::push_hex(&hex::encode(hash_b[1].s)) }          // hB hB? hB? | B' A' b a
            }.compile()
        ).push_script(s.1).push_script(
            script! {
                { U256::push_hex(&hex::encode(hash_a[0].s)) }
                { U256::push_hex(&hex::encode(hash_a[1].s)) }          // hA hA? hA? | A' B' b a
            }.compile()
        ).push_script(s.2).push_script(
            script! {
                { U256::push_hex(&hex::encode(garbled[0].s)) }
                { U256::push_hex(&hex::encode(garbled[1].s)) }
                { U256::push_hex(&hex::encode(garbled[2].s)) }
                { U256::push_hex(&hex::encode(garbled[3].s)) }         // hAB tau0 tau1 tau2 tau3 | b a
            }.compile()
        ).push_script(s.3).push_script(
            script! {
                if correct {
                    { U256::copy(0) }                                  // hC hC
                    { U256::push_hex(&hex::encode(hash_c[0].s)) }
                    { U256::equal(0, 1) } OP_TOALTSTACK
                    { U256::push_hex(&hex::encode(hash_c[1].s)) }
                    { U256::equal(0, 1) } OP_FROMALTSTACK
                    OP_BOOLOR OP_VERIFY
                }
                else {
                    { U256::copy(0) }                                  // hC hC
                    { U256::push_hex(&hex::encode(hash_c[0].s)) }      // hC hC hC?
                    { U256::notequal(0, 1) } OP_VERIFY                 // hC
                    { U256::push_hex(&hex::encode(hash_c[1].s)) }      // hC hC?
                    { U256::notequal(0, 1) } OP_VERIFY                 // 
                }
                OP_TRUE
            }.compile()
        ).compile()
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
        let gate = Gate::and(wire_1, wire_2, wire_3);

        let public_data = gate.public_data();
        let mut incorrect_public_data = public_data.clone();
        incorrect_public_data.0 = vec![S::random(), S::random(), S::random(), S::random()];

        let gate_constant_script = Gate::constant_script();

        for (correct, public_data) in [(true, public_data), (false, incorrect_public_data)] {
            println!("testing {:?} garble", if correct {"correct"} else {"incorrect"});
            for a in [gate.wire_a.borrow().l0.clone(), gate.wire_a.borrow().l1.clone()] {
                for b in [gate.wire_b.borrow().l0.clone(), gate.wire_b.borrow().l1.clone()] {
                    let gate_script = Gate::script(public_data.clone(), correct, gate_constant_script.clone());
                    let script = script! {
                        { U256::push_hex(&hex::encode(&b.s)) }
                        { U256::push_hex(&hex::encode(&a.s)) }
                    }.push_script(gate_script.clone());
                    println!("script len: {:?}", script.len());
                    let result = execute_script(script);
                    assert!(result.success);
                }
            }
        }
    }
}
