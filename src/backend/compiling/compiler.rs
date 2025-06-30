use crate::backend::{
    disassembly::disassemble,
    instructions::{Chunk, Constant, Program, ProgramMetadata},
};

pub struct CompileFailed;
pub struct Compiler {
    current_chunk: Chunk,
    constants: Vec<Constant>,
    metadata: Vec<ProgramMetadata>,
    names: Vec<String>,
}
impl Default for Compiler {
    fn default() -> Self {
        Self::new()
    }
}
impl Compiler {
    pub fn new() -> Self {
        Self {
            current_chunk: Chunk::default(),
            constants: Vec::new(),
            metadata: Vec::new(),
            names: Vec::new(),
        }
    }
    pub fn compile(self) -> Result<Program, CompileFailed> {
        disassemble("<main>", &self.current_chunk, &self.constants);
        Ok(Program {
            constants: self.constants,
            chunk: self.current_chunk,
            names: self.names.into_iter().map(|name| name.into()).collect(),
            metadata: self.metadata,
        })
    }
}
