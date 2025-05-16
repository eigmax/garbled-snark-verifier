#[allow(dead_code)]
// Re-export what is needed to write treepp scripts
pub mod treepp {
    pub use crate::execute_script;
    pub use crate::execute_script_without_stack_limit;
    pub use crate::run;
    pub use bitcoin_script::{script, Script};
}

use core::fmt;

use bitcoin::{
    hashes::Hash,
    hex::DisplayHex,
    Opcode, ScriptBuf, TapLeafHash, Transaction,
};
use bitcoin_scriptexec::{Exec, ExecCtx, ExecError, ExecStats, Options, Stack, TxTemplate};

pub mod bigint;
pub mod blake3;
pub mod u4;
pub mod gate;
pub mod pseudo;

/// A wrapper for the stack types to print them better.
pub struct FmtStack(pub Stack);
impl fmt::Display for FmtStack {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut iter = self.0.iter_str().enumerate().peekable();
        write!(f, "\n0:\t\t ")?;
        while let Some((index, mut item)) = iter.next() {
            if item.is_empty() {
                write!(f, "    []    ")?;
            } else {
                item.reverse();
                write!(f, "0x{:8}", item.as_hex())?;
            }
            if iter.peek().is_some() {
                if (index + 1) % f.width().unwrap_or(4) == 0 {
                    write!(f, "\n{}:\t\t", index + 1)?;
                }
                write!(f, " ")?;
            }
        }
        Ok(())
    }
}

impl FmtStack {
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn get(&self, index: usize) -> Vec<u8> {
        self.0.get(index)
    }
}

impl fmt::Debug for FmtStack {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)?;
        Ok(())
    }
}

#[derive(Debug)]
pub struct ExecuteInfo {
    pub success: bool,
    pub error: Option<ExecError>,
    pub final_stack: FmtStack,
    pub remaining_script: String,
    pub last_opcode: Option<Opcode>,
    pub stats: ExecStats,
}

impl fmt::Display for ExecuteInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.success {
            writeln!(f, "Script execution successful.")?;
        } else {
            writeln!(f, "Script execution failed!")?;
        }
        if let Some(ref error) = self.error {
            writeln!(f, "Error: {:?}", error)?;
        }
        if !self.remaining_script.is_empty() {
            if self.remaining_script.len() < 500 {
                writeln!(f, "Remaining Script: {}", self.remaining_script)?;
            } else {
                let mut string = self.remaining_script.clone();
                string.truncate(500);
                writeln!(f, "Remaining Script: {}...", string)?;
            }
        }
        if !self.final_stack.is_empty() {
            match f.width() {
                None => writeln!(f, "Final Stack: {:4}", self.final_stack)?,
                Some(width) => {
                    writeln!(f, "Final Stack: {:width$}", self.final_stack, width = width)?
                }
            }
        }
        if let Some(ref opcode) = self.last_opcode {
            writeln!(f, "Last Opcode: {:?}", opcode)?;
        }
        writeln!(f, "Stats: {:?}", self.stats)?;
        Ok(())
    }
}

pub fn execute_script(script: treepp::Script) -> ExecuteInfo {
    execute_script_buf_optional_stack_limit(script.compile(), true)
}

pub fn execute_script_buf(script: bitcoin::ScriptBuf) -> ExecuteInfo {
    execute_script_buf_optional_stack_limit(script, true)
}

pub fn execute_script_without_stack_limit(script: treepp::Script) -> ExecuteInfo {
    execute_script_buf_optional_stack_limit(script.compile(), false)
}

pub fn execute_script_buf_without_stack_limit(script: bitcoin::ScriptBuf) -> ExecuteInfo {
    execute_script_buf_optional_stack_limit(script, false)
}

/// Executing a script on stack without `MAX_STACK_SIZE` limit is only for testing purposes \
/// Don't use in production without the stack limit (i.e. `stack_limit` set to false)
fn execute_script_buf_optional_stack_limit(
    script: bitcoin::ScriptBuf,
    stack_limit: bool,
) -> ExecuteInfo {
    let opts = Options {
        enforce_stack_limit: stack_limit,
        ..Default::default()
    };
    let mut exec = Exec::new(
        ExecCtx::Tapscript,
        opts,
        TxTemplate {
            tx: Transaction {
                version: bitcoin::transaction::Version::TWO,
                lock_time: bitcoin::locktime::absolute::LockTime::ZERO,
                input: vec![],
                output: vec![],
            },
            prevouts: vec![],
            input_idx: 0,
            taproot_annex_scriptleaf: Some((TapLeafHash::all_zeros(), None)),
        },
        script,
        vec![],
    )
    .expect("error creating exec");

    loop {
        if exec.exec_next().is_err() {
            break;
        }
    }
    let res = exec.result().unwrap();
    ExecuteInfo {
        success: res.success,
        error: res.error.clone(),
        last_opcode: res.opcode,
        final_stack: FmtStack(exec.stack().clone()),
        remaining_script: exec.remaining_script().to_asm_string(),
        stats: exec.stats().clone(),
    }
}

pub fn run(script: treepp::Script) {
    // let stack = script.clone().analyze_stack();
    // if !stack.is_valid_final_state_without_inputs() {
    //     println!("Stack analysis does not end in valid state: {:?}", stack);
    //     assert!(false);
    // }
    let exec_result = execute_script(script);
    if !exec_result.success {
        println!(
            "ERROR: {:?} <--- \n STACK: {:4} ",
            exec_result.last_opcode, exec_result.final_stack
        );
    }
    //println!("Max_stack_items = {}", exec_result.stats.max_nb_stack_items);
    assert!(exec_result.success);
}

pub fn execute_raw_script_with_inputs(script: Vec<u8>, witness: Vec<Vec<u8>>) -> ExecuteInfo {
    // Get the default options for the script exec.
    // Do not enforce the stack limit.
    let opts = Options {
        enforce_stack_limit: false,
        ..Default::default()
    };

    let mut exec = Exec::new(
        ExecCtx::Tapscript,
        opts,
        TxTemplate {
            tx: Transaction {
                version: bitcoin::transaction::Version::TWO,
                lock_time: bitcoin::locktime::absolute::LockTime::ZERO,
                input: vec![],
                output: vec![],
            },
            prevouts: vec![],
            input_idx: 0,
            taproot_annex_scriptleaf: Some((TapLeafHash::all_zeros(), None)),
        },
        ScriptBuf::from_bytes(script),
        witness,
    )
    .expect("error creating exec");

    loop {
        let temp_res = exec.exec_next();
        match temp_res {
            Ok(()) => (),
            Err(err) => {
                if !err.success {
                    // println!("temp_res: {:?}", temp_res);
                }
                break;
            }
        }
    }

    let res = exec.result().unwrap();
    let execute_info = ExecuteInfo {
        success: res.success,
        error: res.error.clone(),
        last_opcode: res.opcode,
        final_stack: FmtStack(exec.stack().clone()),
        // alt_stack: FmtStack(exec.altstack().clone()),
        remaining_script: exec.remaining_script().to_owned().to_asm_string(),
        stats: exec.stats().clone(),
    };

    execute_info
}

pub fn execute_script_with_inputs(script: treepp::Script, witness: Vec<Vec<u8>>) -> ExecuteInfo {
    execute_raw_script_with_inputs(script.compile().to_bytes(), witness)
}

#[cfg(test)]
mod test {

    use super::execute_script_without_stack_limit;
    use super::treepp::*;

    #[test]
    fn test_script_debug() {
        let script = script! {
            OP_TRUE
            DEBUG
            OP_TRUE
            OP_VERIFY
        };
        let exec_result = execute_script(script);
        assert!(!exec_result.success);
    }

    #[test]
    fn test_execute_script_without_stack_limit() {
        let script = script! {
            for _ in 0..1001 {
                OP_1
            }
            for _ in 0..1001 {
                OP_DROP
            }
            OP_1
        };
        let exec_result = execute_script_without_stack_limit(script);
        assert!(exec_result.success);
    }
}
