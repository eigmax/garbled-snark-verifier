use super::u4_std::u4_drop;
use crate::treepp::*;
use crate::u4::u4_add::u4_arrange_nibbles;

/*
    Full tables for bitwise operations consist of 16x16 elements, operates using OP_PICK on 16 * A + B (A and B being the input numbers)
    Half tables for bitwise operations consist of 16*17/2=136 elements to save space and to calculate, operates with a triangular shape and ordering the input values
*/

/// Pushes the bitwise XOR table
pub fn u4_push_full_xor_table() -> Script {
    script! {
        for i in (0..16).rev() {
            for j in (0..16).rev() {
                {i ^ j}
            }
        }
    }
}

/// Drops full logic table
pub fn u4_drop_full_logic_table() -> Script {
    u4_drop(16 * 16)
}

/// Pushes table for the value x * 16
pub fn u4_push_full_lookup() -> Script {
    script! {
        for i in (0..=256).rev().step_by(16) {
            { i }
        }
    }
}

/// Drops the table for x * 16
pub fn u4_drop_full_lookup() -> Script {
    u4_drop(17)
}

/// Pushes the half bitwise XOR table
pub fn u4_push_half_xor_table() -> Script {
    script! {
        for i in (0..16).rev() {
            for j in (i..16).rev() {
                {i ^ j}
            }
        }
    }
}

/// Pushes the half bitwise AND table
pub fn u4_push_half_and_table() -> Script {
    script! {
        OP_15
        OP_14
        OP_DUP
        OP_13
        OP_12
        OP_2DUP
        OP_DUP
        OP_2DUP
        OP_11
        OP_10
        OP_9
        OP_8
        OP_11
        OP_10
        OP_DUP
        OP_8
        OP_DUP
        OP_10
        OP_DUP
        OP_9
        OP_8
        OP_2DUP
        OP_2DUP
        OP_2DUP
        OP_DUP
        OP_2DUP
        OP_2DUP
        OP_2DUP
        OP_7
        OP_6
        OP_5
        OP_4
        OP_3
        OP_2
        OP_1
        OP_0
        OP_7
        OP_6
        OP_DUP
        OP_4
        OP_DUP
        OP_2
        OP_DUP
        OP_0
        OP_DUP
        OP_6
        OP_DUP
        OP_5
        OP_4
        OP_2DUP
        OP_1
        OP_0
        OP_2DUP
        OP_5
        OP_4
        OP_2DUP
        OP_DUP
        OP_2DUP
        OP_0
        OP_DUP
        OP_2DUP
        OP_4
        OP_DUP
        OP_2DUP
        OP_3
        OP_2
        OP_1
        OP_0
        OP_2OVER
        OP_2OVER
        OP_2OVER
        OP_2OVER
        OP_3
        OP_2
        OP_DUP
        OP_0
        OP_DUP
        OP_2
        OP_DUP
        OP_0
        OP_DUP
        OP_2
        OP_DUP
        OP_0
        OP_DUP
        OP_2
        OP_DUP
        OP_1
        OP_0
        OP_2DUP
        OP_2DUP
        OP_2DUP
        OP_2DUP
        OP_2DUP
        OP_2DUP
        OP_2DUP
        OP_DUP
        OP_2DUP
        OP_3DUP
        OP_3DUP
        OP_3DUP
        OP_3DUP
    }
}

/// Drops half logic table
pub fn u4_drop_half_table() -> Script {
    u4_drop(136)
}

/// Pushes the table to calculate the order of ordered pairs (a, b) satisfying the conditions a <= b and 0 <= a, b < 16
pub fn u4_push_half_lookup() -> Script {
    script! {
        136
        135
        133
        130
        126
        121
        115
        108
        100
        91
        81
        70
        58
        45
        31
        16
    }
}

/// Drops the table that calculates the order of ordered pairs (a, b) satisfying the condition a <= b
pub fn u4_drop_half_lookup() -> Script {
    u4_drop(16)
}

/// Sorts the top 2 stack values
pub fn u4_sort() -> Script {
    script! {
        OP_2DUP
        OP_MIN
        OP_TOALTSTACK
        OP_MAX
        OP_FROMALTSTACK
    }
}

/// Calculates the logic operation with the given half table, lookup parameter denoting how many elements are there after the table including the two u4 elements
pub fn u4_half_table_operation(lookup: u32) -> Script {
    script! {
        { u4_sort() }
        { lookup - 1 }
        OP_ADD
        OP_PICK
        { lookup - 2 }
        OP_ADD
        OP_ADD
        OP_PICK
    }
}

/// Calculates the logic operation with the given full table, lookup parameter denoting how many elements are there after the table including the two u4 elements
pub fn u4_full_table_operation(lookup: u32, table: u32) -> Script {
    script! {
        { lookup }
        OP_ADD
        OP_PICK
        { table }
        OP_ADD
        OP_ADD
        OP_PICK
    }
}

/// Calculates the bitwise XOR of top 2 u4 values using half AND table, lookup parameter denoting how many elements are there after the table including the two u4 elements
/// Uses the formula a XOR b = (a + b) - 2 * (a AND b)
pub fn u4_xor_with_half_and_table(lookup: u32) -> Script {
    script! {
        OP_2DUP
        { u4_half_table_operation(lookup + 2) }
        OP_DUP
        OP_ADD
        OP_SUB
        OP_ADD
    }
}

/// Does bitwise operation with bases.len() elements at the top of the stack, both consisting of nibble_count u4's and at the positions of the bases vector (note that existing operations are commutative)
/// Expects a half logic operation table and offset parameter to locate it, which should be equal to the number of elements after the table including the inputs
/// Keeps the result at the altstack
pub fn u4_logic_nibs(
    nibble_count: u32,
    mut bases: Vec<u32>,
    offset: u32,
    do_xor_with_half_and_table: bool,
) -> Script {
    let numbers = bases.len() as u32;
    bases.sort();
    script! {
        { u4_arrange_nibbles(nibble_count, bases) }
        for nib in 0..nibble_count {
            for i in 0..numbers-1 {
                if do_xor_with_half_and_table {
                    { u4_xor_with_half_and_table( offset - i - nib * numbers ) }
                } else {
                    { u4_half_table_operation( offset - i - nib * numbers ) }
                }
            }
            OP_TOALTSTACK
        }
    }
}

/// Calculates the u32 xor of two elements with half and table, given their positions with the bases parameter
pub fn u4_xor_u32(bases: Vec<u32>, offset: u32, do_xor_with_and: bool) -> Script {
    u4_logic_nibs(8, bases, offset, do_xor_with_and)
}

