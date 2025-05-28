use bitvm::{bigint::U256, treepp::*};

pub mod s;
pub mod wire;
pub mod gate;
pub mod circuit;
pub mod bristol;
pub mod circuits;

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
