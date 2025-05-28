use crate::{convert_between_blake3_and_normal_form, s::S, LIMB_LEN, N_LIMBS};
use bitvm::{bigint::U256, hash::blake3::blake3_compute_script_with_limb, treepp::*};

#[derive(Clone, Debug)]
pub struct Wire {
    pub l0: S,
    pub l1: S,
    pub hash0: S,
    pub hash1: S,
    pub value: Option<bool>,
    pub label: Option<S>,
}

impl Wire {
    pub fn new() -> Self {
        let l0 = S::random();
        let l1 = S::random();
        let hash0 = l0.hash();
        let hash1 = l1.hash();
        Self {
            l0,
            l1,
            hash0,
            hash1,
            value: None,
            label: None,
        }
    }

    pub fn select(&self, selector: bool) -> S {
        if selector {
            self.l1.clone()
        }
        else {
            self.l0.clone()
        }
    }

    pub fn select_hash(&self, selector: bool) -> S {
        if selector {
            self.hash1.clone()
        }
        else {
            self.hash0.clone()
        }
    }

    pub fn get_value(&self) -> bool {
        assert!(self.value.is_some());
        self.value.unwrap()
    }

    pub fn get_label(&self) -> S {
        assert!(self.value.is_some());
        self.label.clone().unwrap()
    }

    pub fn set(&mut self, bit: bool) {
        assert!(self.value.is_none());
        self.value = Some(bit);
        self.label = Some(self.select(bit));
    }

    pub fn set2(&mut self, bit: bool, label: S) {
        assert!(self.value.is_none());
        self.value = Some(bit);
        self.label = Some(label);
    }

    pub fn commitment_script(&self) -> Script {
        script! {                                                  // x bit_x
            OP_TOALTSTACK                                          // x | bit_x
            { convert_between_blake3_and_normal_form() }
            for _ in 0..N_LIMBS {0}                                // x'0 | bit_x
            { blake3_compute_script_with_limb(32, LIMB_LEN) }
            { U256::transform_limbsize(4, LIMB_LEN.into()) }       // hx | bit_x
            OP_FROMALTSTACK                                        // hx bit_x
            OP_IF
                { U256::push_hex(&hex::encode(self.hash1.0)) }
            OP_ELSE
                { U256::push_hex(&hex::encode(self.hash0.0)) }
            OP_ENDIF                                               // hx hash
            { U256::equal(0, 1) }
        }
    }
}
