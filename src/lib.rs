use bitvm::{bigint::U256, treepp::*};

pub mod s;
pub mod wire;
pub mod gate;
pub mod circuit;
pub mod bristol;
pub mod circuits;

pub mod bag {
    pub use crate::s::S;
    pub use crate::wire::Wire;
    pub use crate::gate::Gate;
    pub use crate::circuit::Circuit;
    pub use std::{cell::RefCell, rc::Rc};
    pub type Wirex = Rc<RefCell<Wire>>;
    pub type Wires = Vec<Wirex>;
}

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

pub fn bit_to_usize(bit: bool) -> usize {
    if bit {1} else {0}
}

const LIMB_LEN: u8 = 29;
const N_LIMBS: u8 = 9;
