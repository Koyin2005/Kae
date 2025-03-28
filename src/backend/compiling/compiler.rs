use std::{rc::Rc, usize};

use crate::{
    backend::{disassembly::disassemble, instructions::{Chunk, Constant, Instruction, Program, ProgramMetadata, StructInfo, VariantInfo}, 
    natives::{native_input, native_panic}, values::{Function, NativeFn, NativeFunction}}, 
    frontend::{ typechecking::{ 
        substituter::{sub_function}, 
        typed_ast::{BinaryOp, GenericName, LogicalOp, NumberKind,UnaryOp}, types::{Type}}}};

pub struct CompileFailed;
pub struct Compiler{
    current_chunk : Chunk,
    constants : Vec<Constant>,
    metadata : Vec<ProgramMetadata>,
    names : Vec<String>,
    scope_depth : usize,
    mono_counter : usize,
}
impl<'a> Compiler{
    pub fn new() -> Self{
        Self { current_chunk: Chunk::default(), constants: Vec::new(), metadata: Vec::new(), names: Vec::new(), scope_depth: 0, mono_counter: 0 }
    }
    pub fn compile(mut self) -> Result<Program,CompileFailed> {
        disassemble("<main>", &self.current_chunk,&self.constants);
        Ok(Program{constants:self.constants,chunk:self.current_chunk,names:self.names.into_iter().map(|name| name.into()).collect(),metadata:self.metadata})
    }
}