use crate::{data_structures::IndexVec, define_id, frontend::ast_lowering::hir::BinaryOp, identifiers::{BodyIndex, SymbolIndex, VariableIndex}};

pub enum Constant {
    Int(i64),
    Bool(bool),
    String(SymbolIndex),
}

pub struct Block {
    pub stmts : Vec<Stmt>,
    pub terminator : Terminator
}
pub struct Place{
    local : Local,
}
pub enum RValue {
    Binary(BinaryOp,Operand,Operand),
}
pub enum Operand {
    Constant(Constant),
    Copy(Place)
}
pub enum Stmt{
    Assign(Place,RValue),
    
}
pub enum Terminator {
    Jump(BlockId),
    Switch(Operand,Box<[BlockId]>),
    ConditionalJump(Operand,BlockId,BlockId)
}

define_id!(Local);
define_id!(BlockId);
pub enum LocalKind {
    Variable(VariableIndex),
    Temporary
}
pub struct MirBody{
    pub locals : IndexVec<Local,LocalKind>,
    pub blocks : IndexVec<BlockId,Block>
}


pub struct Mir{
    pub bodies : IndexVec<BodyIndex,MirBody>
}