use std::fmt::Display;

use crate::{data_structures::IndexVec, define_id, frontend::{ast_lowering::hir::{BinaryOp, DefId, UnaryOp}, typechecking::types::generics::GenericArgs}, identifiers::{BodyIndex, FieldIndex, SymbolIndex, VariableIndex, VariantIndex}};

pub mod debug;
pub enum Constant {
    Int(i64),
    Bool(bool),
    String(SymbolIndex),
}

pub struct Block {
    pub stmts : Vec<Stmt>,
    pub terminator : Terminator
}
pub enum PlaceProjection {
    Field(FieldIndex),
    Variant(SymbolIndex,VariantIndex),
    Index(Local)
}
pub struct Place{
    pub local : Local,
    pub projections : Box<[PlaceProjection]>
}

pub enum RValue {
    Use(Operand),
    Binary(BinaryOp,Box<(Operand,Operand)>),
    Unary(UnaryOp,Operand),
    Call(Operand,Box<[Operand]>),
    Array(Box<[Operand]>),
    Adt(Box<(DefId,GenericArgs,Option<VariantIndex>)>,IndexVec<FieldIndex,Operand>),
    Tuple(Box<[Operand]>)
}
pub enum Operand {
    Constant(Constant),
    Load(Place)
}
pub enum Stmt{
    Assign(Place,RValue),
    Nop
}
pub enum Terminator {
    Goto(BlockId),
    Switch(Operand,Box<[(u128,BlockId)]>,BlockId),
    Return,
    Unreachable
}

define_id!(Local);
define_id!(BlockId);

impl Display for BlockId{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("bb{}",self.0))
    }
}
pub enum LocalKind {
    Variable(VariableIndex),
    Temporary
}
pub struct Body{
    pub locals : IndexVec<Local,LocalKind>,
    pub blocks : IndexVec<BlockId,Block>
}


pub struct Mir{
    pub bodies : IndexVec<BodyIndex,Body>
}