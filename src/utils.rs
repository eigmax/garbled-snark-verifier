use std::iter::zip;

pub fn xor(a: Vec<u8>, b: Vec<u8>) -> Vec<u8> {
    let mut c = Vec::new();

    for (u, v) in zip(a, b) {
        c.push(u ^ v);
    }
    c
}