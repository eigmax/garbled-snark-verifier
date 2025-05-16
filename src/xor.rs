use crate::treepp::*;

/// Zips the a-th and b-th u32 elements from the top and keep the one chosen (given as the first parameter) in the stack (without preserving order)
/// Assuming a is smaller than b and x_i denoting the i-th part of the x-th number:
/// Input:  ... (a u32 elements) a_0 a_1 a_2 a_3 ... (b - a - 1 u32 elements) b_0 b_1 b_2 b_3
/// Output: b_0 a_0 b_1 a_1 b_2 a_2 b_3 a_3 ... (b u32 elements including the element that is chosen to stay and rest of the stack)
pub fn u32_copy_zip(a: u32, b: u32) -> Script {
    if a < b {
        _u32_copy_zip(a, b)
    } else {
        _u32_zip_copy(b, a)
    }
}

/// Helper for u32_copy_zip
pub fn _u32_copy_zip(mut a: u32, mut b: u32) -> Script {
    assert!(a < b);
    a = (a + 1) * 4 - 1;
    b = (b + 1) * 4 - 1;

    script! {
        {a} OP_PICK {b+1} OP_ROLL
        {a+1} OP_PICK {b+2} OP_ROLL
        {a+2} OP_PICK {b+3} OP_ROLL
        {a+3} OP_PICK {b+4} OP_ROLL
    }
}

///Helper for u32_copy_zip
pub fn _u32_zip_copy(mut a: u32, mut b: u32) -> Script {
    assert!(a < b);

    a = (a + 1) * 4 - 1;
    b = (b + 1) * 4 - 1;
    script! {
        {a} OP_ROLL {b} OP_PICK
        {a+1} OP_ROLL {b} OP_PICK
        {a+2} OP_ROLL {b} OP_PICK
        {a+3} OP_ROLL {b} OP_PICK
    }
}

/// Bitwise XOR of two u8 elements, i denoting how many values are there in the stack after the table (including the input numbers A and B)
/// Expects the u8_xor_table on the stack and uses it to process even and odd bits separately
pub fn u8_xor(i: u32) -> Script {
    script! {
        // f_A = f(A)
        OP_DUP
        {i}
        OP_ADD
        OP_PICK

        // A_even = f_A << 1
        OP_DUP
        OP_DUP
        OP_ADD

        // A_odd = A - A_even
        OP_ROT
        OP_SWAP
        OP_SUB

        // f_B = f(B)
        OP_ROT
        OP_DUP
        {i + 1}
        OP_ADD
        OP_PICK

        // B_even = f_B << 1
        OP_DUP
        OP_DUP
        OP_ADD

        // B_odd = B - B_even
        OP_ROT
        OP_SWAP
        OP_SUB

        // A_andxor_B_even = f_A + f_B
        OP_SWAP
        3
        OP_ROLL
        OP_ADD

        // A_xor_B_even = A_andxor_B_even - (f(A_andxor_B_even) << 1)
        OP_DUP
        {i + 1}
        OP_ADD
        OP_PICK
        OP_DUP
        OP_ADD
        OP_SUB

        // A_andxor_B_odd = A_odd + B_odd
        OP_SWAP
        OP_ROT
        OP_ADD

        // A_xor_B_odd = A_andxor_B_odd - (f(A_andxor_B_odd) << 1)
        OP_DUP
        {i}
        OP_ADD
        OP_PICK
        OP_DUP
        OP_ADD
        OP_SUB

        // A_xor_B = A_xor_B_odd + (A_xor_B_even << 1)
        OP_OVER
        OP_ADD
        OP_ADD
    }
}

/// Bitwise XOR of a-th and b-th u32 elements from the top, keeps a-th element in the stack
/// Expects u8_xor_table on the stack to use u8_xor, and stack_size as a parameter to locate the table (which should be equal to 1 + number of the u32 elements in the stack after the table)
pub fn u32_xor(a: u32, b: u32, stack_size: u32) -> Script {
    assert_ne!(a, b);
    script! {
        {u32_copy_zip(a, b)}

        //
        // XOR
        //

        {u8_xor(8 + (stack_size - 2) * 4)}

        OP_TOALTSTACK

        {u8_xor(6 + (stack_size - 2) * 4)}

        OP_TOALTSTACK

        {u8_xor(4 + (stack_size - 2) * 4)}

        OP_TOALTSTACK

        {u8_xor(2 + (stack_size - 2) * 4)}


        OP_FROMALTSTACK
        OP_FROMALTSTACK
        OP_FROMALTSTACK
    }
}

/// Pushes the u8 XOR table, for the function f(x) = (x & 0b10101010) >> 1
pub fn u8_push_xor_table() -> Script {
    script! {
        85
        OP_DUP
        84
        OP_DUP
        OP_2OVER
        OP_2OVER
        81
        OP_DUP
        80
        OP_DUP
        OP_2OVER
        OP_2OVER

        85
        OP_DUP
        84
        OP_DUP
        OP_2OVER
        OP_2OVER
        81
        OP_DUP
        80
        OP_DUP
        OP_2OVER
        OP_2OVER

        69
        OP_DUP
        68
        OP_DUP
        OP_2OVER
        OP_2OVER
        65
        OP_DUP
        64
        OP_DUP
        OP_2OVER
        OP_2OVER

        69
        OP_DUP
        68
        OP_DUP
        OP_2OVER
        OP_2OVER
        65
        OP_DUP
        64
        OP_DUP
        OP_2OVER
        OP_2OVER

        85
        OP_DUP
        84
        OP_DUP
        OP_2OVER
        OP_2OVER
        81
        OP_DUP
        80
        OP_DUP
        OP_2OVER
        OP_2OVER

        85
        OP_DUP
        84
        OP_DUP
        OP_2OVER
        OP_2OVER
        81
        OP_DUP
        80
        OP_DUP
        OP_2OVER
        OP_2OVER

        69
        OP_DUP
        68
        OP_DUP
        OP_2OVER
        OP_2OVER
        65
        OP_DUP
        64
        OP_DUP
        OP_2OVER
        OP_2OVER

        69
        OP_DUP
        68
        OP_DUP
        OP_2OVER
        OP_2OVER
        65
        OP_DUP
        64
        OP_DUP
        OP_2OVER
        OP_2OVER

        21
        OP_DUP
        20
        OP_DUP
        OP_2OVER
        OP_2OVER
        17
        OP_DUP
        16
        OP_DUP
        OP_2OVER
        OP_2OVER

        21
        OP_DUP
        20
        OP_DUP
        OP_2OVER
        OP_2OVER
        17
        OP_DUP
        16
        OP_DUP
        OP_2OVER
        OP_2OVER

        5
        OP_DUP
        4
        OP_DUP
        OP_2OVER
        OP_2OVER
        1
        OP_DUP
        0
        OP_DUP
        OP_2OVER
        OP_2OVER

        5
        OP_DUP
        4
        OP_DUP
        OP_2OVER
        OP_2OVER
        1
        OP_DUP
        0
        OP_DUP
        OP_2OVER
        OP_2OVER

        21
        OP_DUP
        20
        OP_DUP
        OP_2OVER
        OP_2OVER
        17
        OP_DUP
        16
        OP_DUP
        OP_2OVER
        OP_2OVER

        21
        OP_DUP
        20
        OP_DUP
        OP_2OVER
        OP_2OVER
        17
        OP_DUP
        16
        OP_DUP
        OP_2OVER
        OP_2OVER

        5
        OP_DUP
        4
        OP_DUP
        OP_2OVER
        OP_2OVER
        1
        OP_DUP
        0
        OP_DUP
        OP_2OVER
        OP_2OVER

        5
        OP_DUP
        4
        OP_DUP
        OP_2OVER
        OP_2OVER
        1
        OP_DUP
        0
        OP_DUP
        OP_2OVER
        OP_2OVER
    }
}

/// Drops the u8 XOR table
pub fn u8_drop_xor_table() -> Script {
    script! {
        for _ in 0..128{
            OP_2DROP
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_u8_xor_exhaustive() {
        for a in 0..256 {
            for b in 0..256 {
                let script = script! {
                  { u8_push_xor_table() }
                  { a }
                  { b }
                  { u8_xor(2) }
                  { a ^ b }
                  OP_EQUAL
                  OP_TOALTSTACK
                  { u8_drop_xor_table() }
                  OP_FROMALTSTACK
                };
                run(script);
            }
        }
    }
}
