pub mod core;
pub mod circuits;

pub mod bag {
    pub use crate::core::s::S;
    pub use crate::core::wire::Wire;
    pub use crate::core::gate::Gate;
    pub use crate::core::circuit::Circuit;
    pub use std::{cell::RefCell, rc::Rc};
    pub type Wirex = Rc<RefCell<Wire>>;
    pub type Wires = Vec<Wirex>;
    pub use crate::core::gate::GateCount;
}
