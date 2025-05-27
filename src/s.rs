use std::{iter::zip, ops::Add};
use rand::Rng;
use blake3::hash;

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct S {
    pub s: [u8; 32],
}

impl S {
    pub fn new(s: [u8; 32]) -> Self {
        Self {
            s
        }
    }

    pub const fn zero() -> Self {
        Self {
            s: [0_u8; 32]
        }
    }

    pub const fn one() -> Self {
        let mut s = [0_u8; 32];
        s[31] = 1;
        Self {
            s
        }
    }

    pub const fn delta() -> Self {
        Self {
            s: [7_u8; 32]
        }
    }

    pub fn random() -> Self {
        Self::new(rand::rng().random::<[u8; 32]>())
    }

    pub fn neg(&self) -> Self {
        let mut s = self.s.clone();
        for i in 0..32 {
            s[i] = 255 - self.s[i];
        }
        Self::new(s) + Self::one()
    }

    pub fn hash(&self) -> Self {
        Self::new(*hash(&self.s).as_bytes())
    }

    pub fn hash_together(a: Self, b: Self) -> Self {
        let mut h = a.s.to_vec();
        h.extend(b.s.to_vec());
        Self::new(*hash(&h).as_bytes())
    }
}

impl Add for S {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let mut s = [0_u8; 32];
        let mut carry = 0;
        for (i, (u, v)) in zip(self.s, rhs.s).enumerate().rev() {
            let x = (u as u32) + (v as u32) + carry;
            s[i] = (x % 256) as u8;
            carry = x / 256;
        }
        Self {
            s
        }
    }
}

#[cfg(test)]
mod tests {
    use bitvm::{bigint::U256, treepp::*};
    use super::*;

    #[test]
    fn test_s() {
        let a = S::random();
        let b = S::random();
        let c = a.clone() + b.clone();
        let d = a.neg();

        let script = script! {
            { U256::push_hex(&hex::encode(&a.s)) }
            { U256::push_hex(&hex::encode(&b.s)) }
            { U256::add(0, 1) }
            { U256::push_hex(&hex::encode(&c.s)) }
            { U256::equalverify(0, 1) }
            { U256::push_hex(&hex::encode(&a.s)) }
            { U256::push_hex(&hex::encode(&d.s)) }
            { U256::add(0, 1) }
            { U256::push_hex(&hex::encode(&S::zero().s)) }
            { U256::equalverify(0, 1) }
            OP_TRUE
        };
        println!("script len: {:?}", script.len());
        let result = execute_script(script);
        assert!(result.success);
    }
}

