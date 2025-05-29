pub mod add;
pub mod mul;

#[derive(Debug)]
pub struct BigIntImpl<const N_BITS: u32> {}

pub type U254 = BigIntImpl<254>;
