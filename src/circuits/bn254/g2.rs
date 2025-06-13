use crate::circuits::bn254::fq2::Fq2;

pub struct G2Projective;

impl G2Projective {
    pub const N_BITS: usize = 3 * Fq2::N_BITS;
}
