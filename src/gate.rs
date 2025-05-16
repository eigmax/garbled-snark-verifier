use rand::Rng;
use blake3::hash;

pub struct Wire {
    pub label0: Vec<u8>,
    pub label1: Vec<u8>,
}

impl Wire {
    pub fn new() -> Self {
        let label0 = rand::rng().random::<[u8; 32]>().to_vec();
        let label1 = rand::rng().random::<[u8; 32]>().to_vec();
        Self {
            label0,
            label1,
        }
    }

    pub fn label_hashes(&self) -> (Vec<u8>, Vec<u8>) {
        let h0 = hash(&self.label0);
        let hash0 = h0.as_bytes();
        let h1 = hash(&self.label1);
        let hash1 = h1.as_bytes();
        (hash0.to_vec(), hash1.to_vec())
    }
}

pub struct Gate {
    pub wire_a: Wire,
    pub wire_b: Wire,
    pub wire_c: Wire,
    pub f: fn(bool, bool) -> bool,
}

impl Gate {
    pub fn new(wire_a: Wire, wire_b: Wire, wire_c: Wire, f: fn(bool, bool) -> bool) -> Self {
        Self {
            wire_a,
            wire_b,
            wire_c,
            f,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_gate() {
        fn and(a: bool, b: bool) -> bool {
            return a & b;
        }
        let wire_1 = Wire::new();
        let wire_2 = Wire::new();
        let wire_3 = Wire::new();
        let gate = Gate::new(wire_1, wire_2, wire_3, and);
    }
}
