use crate::bag::*;
use super::BigIntImpl;

impl<const N_BITS: usize> BigIntImpl<N_BITS> {
    pub fn mul(input_wires: Vec<Rc<RefCell<Wire>>>) -> (Vec<Rc<RefCell<Wire>>>, Vec<Gate>) {
        todo!()
    }
}
