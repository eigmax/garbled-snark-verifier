pub mod add;
pub mod mul;

#[derive(Debug)]
pub struct BigIntImpl<const N_BITS: usize> {}

impl<const N_BITS: usize> BigIntImpl<N_BITS> {
    pub const N_BITS: usize = N_BITS;
}

pub type U254 = BigIntImpl<254>;
