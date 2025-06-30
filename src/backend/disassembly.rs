use std::fmt::Display;

use super::instructions::{Chunk, Constant, Instruction};

pub fn disassemble(name: &str, chunk: &Chunk, constants: &[Constant]) {
    println!("====== {} =====", name);
    for (ip, instruction) in chunk.code.iter().copied().enumerate() {
        disassemble_instruction(chunk, ip, instruction, constants);
    }
}
fn arg_instruction<T: Display>(name: &'static str, arg: T) {
    println!("{} {}", name, arg)
}
pub fn disassemble_instruction(
    chunk: &Chunk,
    ip: usize,
    instruction: Instruction,
    constants: &[Constant],
) {
    if ip > 0 && chunk.lines[ip] == chunk.lines[ip - 1] {
        print!("|  ")
    } else {
        print!("{} ", chunk.lines[ip])
    }
    print!("{:04} ", ip);
    match instruction {
        Instruction::LoadConstant(constant) => {
            println!(
                "LoadConstant {} ({})",
                constant, &constants[constant as usize]
            )
        }
        Instruction::LoadInt(int) => {
            arg_instruction("LoadInt", int);
        }
        Instruction::LoadGlobal(global) => {
            arg_instruction("LoadGlobal", global);
        }
        Instruction::LoadLocal(local) => {
            arg_instruction("LoadLocal", local);
        }
        Instruction::LoadClosure(closure_constant) => {
            println!(
                "LoadClosure {} ({})",
                closure_constant, &constants[closure_constant as usize]
            );
            let Constant::Function(function) = &constants[closure_constant as usize] else {
                unreachable!()
            };
            for &(index, is_local) in &function.upvalues {
                println!(
                    "|   {} {}",
                    if is_local { "local" } else { "upvalue" },
                    index
                );
            }
        }
        _ => {
            println!("{:?}", instruction)
        }
    }
}
