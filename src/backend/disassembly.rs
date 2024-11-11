use super::instructions::{Chunk, Constant, Instruction};

pub fn disassemble(name:&str,chunk:&Chunk,constants:&[Constant]){
    println!("====== {} =====",name);
    for (ip,instruction) in chunk.code.iter().copied().enumerate(){
        disassemble_instruction(chunk,ip,instruction,constants);
    }
}

pub fn disassemble_instruction(chunk:&Chunk,ip:usize,instruction:Instruction,constants:&[Constant]){
    if ip > 0 && chunk.lines[ip] == chunk.lines[ip-1]{
        print!("|  ")
    }
    else{
        print!("{} ",chunk.lines[ip])
    }
    print!("{:04} ",ip);
    match instruction{
        Instruction::LoadConstant(constant) => {
            println!("LoadConstant {} ({:?})",constant,&constants[constant as usize])
        },
        _ => {
            
            println!("{:?}",instruction)
        }
    }
}