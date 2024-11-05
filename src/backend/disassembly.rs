use super::instructions::{Chunk, Instruction};

pub fn disassemble(name:&str,chunk:&Chunk){
    println!("====== {} =====",name);
    for (ip,instruction) in chunk.code.iter().copied().enumerate(){
        disassemble_instruction(chunk,ip,instruction);
    }
}

pub fn disassemble_instruction(chunk:&Chunk,ip:usize,instruction:Instruction){
    if ip > 0 && chunk.lines[ip] == chunk.lines[ip-1]{
        print!("|  ")
    }
    else{
        print!("{} ",chunk.lines[ip])
    }
    print!("{:04} ",ip);
    println!("{:?}",instruction)
}