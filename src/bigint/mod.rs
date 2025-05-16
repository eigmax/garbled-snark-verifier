use std::cmp::Ordering;
use crate::pseudo::NMUL;
use crate::treepp::*;

#[derive(Debug)]
pub struct BigIntImpl<const N_BITS: u32, const LIMB_SIZE: u32> {}

impl<const N_BITS: u32, const LIMB_SIZE: u32> BigIntImpl<N_BITS, LIMB_SIZE> {
    pub const N_BITS: u32 = N_BITS;
    pub const LIMB_SIZE: u32 = LIMB_SIZE;
    pub const N_LIMBS: u32 = N_BITS.div_ceil(LIMB_SIZE);
    pub const HEAD: u32 = N_BITS - (Self::N_LIMBS - 1) * LIMB_SIZE;
    pub const HEAD_OFFSET: u32 = 1u32 << Self::HEAD;
}

/// Struct to store the information of each step in `transform_limbsize` function.
/// ## Fields:
/// - current_limb_remaining_bits: the number of bits left in the current source limb that is being processed.
/// - extract_window: the number of bits to extract from the current limb.
/// - drop_currentlimb: signals to drop the current limb and bring another from altstack.
/// - initiate_targetlimb: signals to start a new target limb.
#[derive(Debug)]
struct TransformStep {
    current_limb_remaining_bits: u32,
    extract_window: u32,
    drop_currentlimb: bool,
    initiate_targetlimb: bool,
}

impl<const N_BITS: u32, const LIMB_SIZE: u32> BigIntImpl<N_BITS, LIMB_SIZE> {

    /// Generates a vector of TransformStep struct that encodes all the information needed to
    /// convert BigInt form one limbsize represention (source) to another (target).
    /// used as a helper function for `transform_limbsize`
    fn get_transform_steps(source_limb_size: u32, target_limb_size: u32) -> Vec<TransformStep> {
        //define an empty vector to store Transform steps
        let mut transform_steps: Vec<TransformStep> = Vec::new();

        // compute the number of limbs for target and source
        let target_n_limbs = N_BITS.div_ceil(target_limb_size);
        let mut target_limb_remaining_bits = Self::N_BITS - (target_n_limbs - 1) * target_limb_size;
        let source_n_limbs = N_BITS.div_ceil(source_limb_size);
        let source_head = Self::N_BITS - (source_n_limbs - 1) * source_limb_size;

        // define a vector of limbsizes of source
        let mut limb_sizes: Vec<u32> = Vec::with_capacity(source_n_limbs as usize);
        let mut first_iter_flag = true;
        for _ in 0..(source_n_limbs - 1) {
            limb_sizes.push(source_limb_size);
        }
        limb_sizes.push(source_head);

        //iterate until all limbs of source are processed
        while !limb_sizes.is_empty() {
            //iterate until the target limb is filled completely
            while target_limb_remaining_bits > 0 {
                let source_limb_last_idx = limb_sizes.len() - 1;
                let source_limb_remaining_bits = limb_sizes[source_limb_last_idx];

                match source_limb_remaining_bits.cmp(&target_limb_remaining_bits) {
                    Ordering::Less => {
                        transform_steps.push(TransformStep {
                            current_limb_remaining_bits: source_limb_remaining_bits,
                            extract_window: source_limb_remaining_bits,
                            drop_currentlimb: true,
                            initiate_targetlimb: first_iter_flag,
                        });
                        target_limb_remaining_bits -= source_limb_remaining_bits;
                        limb_sizes.pop();
                    }
                    Ordering::Equal => {
                        transform_steps.push(TransformStep {
                            current_limb_remaining_bits: source_limb_remaining_bits,
                            extract_window: target_limb_remaining_bits,
                            drop_currentlimb: true,
                            initiate_targetlimb: first_iter_flag,
                        });
                        target_limb_remaining_bits = 0;
                        limb_sizes.pop();
                    }
                    Ordering::Greater => {
                        transform_steps.push(TransformStep {
                            current_limb_remaining_bits: source_limb_remaining_bits,
                            extract_window: target_limb_remaining_bits,
                            drop_currentlimb: false,
                            initiate_targetlimb: first_iter_flag,
                        });
                        limb_sizes[source_limb_last_idx] =
                            source_limb_remaining_bits - target_limb_remaining_bits;
                        target_limb_remaining_bits = 0;
                    }
                }
                first_iter_flag = false;
            }
            target_limb_remaining_bits = target_limb_size;
            first_iter_flag = true;
        }
        transform_steps
    }

    /// Transform Limbsize for BigInt
    /// This function changes the representation of BigInt present on stack as multiple limbs of source limbsize to
    /// any another limbsize within 1 and 31 (inclusive).
    /// Specifically, This can be used to transform limbs into nibbles, limbs into bits ans vice-versa to aid optimizetions.
    ///
    /// ## Assumptions:
    /// - Does NOT do input validation.
    /// - The message is placed such that LSB is on top of stack. (MSB pushed first)
    ///
    /// ## Stack Effects:
    /// The original BigInt which that was in stack is dropped
    /// The same BigInt with target_limbsize is left on stack
    ///  
    /// ## Panics:
    /// - If the source or target limb size lies outside of 0 to 31 (inclusive), fails with assertion error.
    /// - If the source or target limb size is greater than number of bits, fails with assertion error.
    /// - If the elements do not fit on the stack. (few satck elements are also used for intermediate computation).
    /// - The number of bits in the BigInt must be 32 or larger.
    pub fn transform_limbsize(source_limb_size: u32, target_limb_size: u32) -> Script {
        // ensure that source and target limb sizes are between 0 and 31 inclusive
        assert!(
            source_limb_size < 32 && source_limb_size > 0,
            "source limb size must lie between 1 and 31 inclusive"
        );
        assert!(
            target_limb_size < 32 && target_limb_size > 0,
            "target limb size must lie between 1 and 31 inclusive"
        );

        //ensure that source and target limb size aren't greater than N_BITS
        assert!(
            source_limb_size <= Self::N_BITS,
            "source limb size mustn't be greater than number of bits in bigInt"
        );
        assert!(
            target_limb_size <= Self::N_BITS,
            "target limb size mustn't be greater than number of bits in bigInt"
        );

        //ensure that the N_BITS are larger than or equal to 32
        assert!(
            Self::N_BITS >= 32,
            "The number of bits in BigInt must be atleast 32"
        );

        // if both source and target limb size are same, do nothing
        if source_limb_size == target_limb_size {
            script!()
        } else {
            let steps = Self::get_transform_steps(source_limb_size, target_limb_size);

            let source_n_limbs = N_BITS.div_ceil(source_limb_size);
            script!(
            // send all limbs except the first to alt stack so that the MSB is handled first
            for _ in 0..(source_n_limbs - 1){OP_TOALTSTACK}

            for (index, step) in steps.iter().enumerate() {
                    {extract_digits(step.current_limb_remaining_bits, step.extract_window)}

                    if !step.initiate_targetlimb{
                        // add
                        OP_ROT
                        for _ in 0..step.extract_window {OP_DUP OP_ADD}
                        OP_ROT
                        OP_ADD
                        OP_SWAP
                    }

                    if step.drop_currentlimb{
                        OP_DROP
                        //except when its the last limb, we pull a new limb from altstack
                        if index != (steps.len() - 1){
                        OP_FROMALTSTACK
                        }
                    }
                }
            )
        }
    }
}

/// Extracts a window of bits from a u32 limb on top of stack
///
/// ## Assumptions;
/// Doesn't do input validation
/// All the bits before start_index must be 0 for the extract to work properly
///
/// ## Panics:
/// - If the start_index is not between the range 1 and 31 (inclusive), fails with assertion error
/// - If the window is larger than the start_index, fails with assertion error
///
/// ## Stack behaviour:
/// - extracts the desired window as a stack element
/// - leaves the original limb with extracted bits set to zero on top of stack
pub fn extract_digits(start_index: u32, window: u32) -> Script {
    // doesnot work if start_index is 32
    assert!(
        start_index < 32 && start_index > 0,
        "start_index must lie between 1 and 31 (inclusive)"
    );

    //panics if the window exceeds the number of bits on the left of start_index
    assert!(
        start_index >= window,
        "not enough bits left of start_index to fill the window!"
    );

    script! {
        0
        OP_SWAP
        for i in 0..window {
            OP_TUCK
            { 1 << (start_index - i - 1) }
            OP_GREATERTHANOREQUAL
            OP_TUCK
            OP_ADD
            if i < window - 1 { { NMUL(2) } }
            OP_ROT OP_ROT
            OP_IF
                { 1 << (start_index - i - 1) }
                OP_SUB
            OP_ENDIF
        }
    }
}

pub type U256 = BigIntImpl<256, 29>;
