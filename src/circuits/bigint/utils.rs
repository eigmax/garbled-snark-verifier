#[cfg(test)]
pub mod tests {
    use num_bigint::BigUint;
    use rand::{rng, Rng};

    pub fn random_biguint() -> BigUint {
        BigUint::from_bytes_le(&rng().random::<[u8; 32]>())
    }

    pub fn bits_from_biguint(u: BigUint) -> Vec<bool> {
        let bytes = u.to_bytes_le();
        let mut bits = Vec::new();
        for byte in bytes {
            for i in 0..8 {
                bits.push(((byte >> i) & 1) == 1)
            }
        }
        bits
    }

    pub fn biguint_from_bits(bits: Vec<bool>) -> BigUint {
        let zero = BigUint::ZERO;
        let one = BigUint::from(1_u8);
        let mut u = zero.clone();
        for bit in bits.iter().rev() {
            u = u.clone() + u.clone() + if *bit {one.clone()} else {zero.clone()};
        }
        u
    }

    #[test]
    fn test_random_biguint() {
        let u = random_biguint();
        println!("u: {:?}", u);
        let b = bits_from_biguint(u.clone());
        let v = biguint_from_bits(b);
        println!("v: {:?}", v);
        assert_eq!(u, v);
    }
}
