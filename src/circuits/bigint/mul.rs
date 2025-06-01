use crate::bag::*;
use super::BigIntImpl;

impl<const N_BITS: usize> BigIntImpl<N_BITS> {
    pub fn mul(a: Wires, b: Wires) -> Circuit {
        assert_eq!(a.len(), N_BITS);
        assert_eq!(b.len(), N_BITS);
        let circuit = Circuit::empty();
        
        circuit
    }
}
