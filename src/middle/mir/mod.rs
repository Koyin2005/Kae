use std::fmt::Display;

use crate::{data_structures::IndexVec, define_id, frontend::{ast_lowering::hir::{BinaryOp, BuiltinKind, DefId, UnaryOp}, typechecking::types::{generics::GenericArgs, Type}}, 
    identifiers::{BodyIndex, FieldIndex, SymbolIndex, VariantIndex}};

pub mod debug;

pub enum FunctionKind {
    Anon(DefId),
    Normal(DefId),
    Variant(DefId),
    Builtin(BuiltinKind)
}
pub enum ConstantKind {
    Int(i64),
    Bool(bool),
    String(SymbolIndex),
    ZeroSized,
    Function(FunctionKind,GenericArgs),
}
pub struct  Constant {
    pub ty : Type,
    pub kind : ConstantKind
}
impl From<bool> for Constant{
    fn from(value: bool) -> Self {
        Constant { ty: Type::Bool, kind: ConstantKind::Bool(value) }
    }
}
pub struct Block {
    pub stmts : Vec<Stmt>,
    pub terminator : Option<Terminator>
}
impl Block{
    pub fn expect_terminator(&self) -> &Terminator{
        self.terminator.as_ref().expect("The terminator should be assigned")
    }
}
#[derive(Clone)]
pub enum PlaceProjection {
    Field(FieldIndex),
    Variant(SymbolIndex,VariantIndex),
    Index(Local)
}
#[derive(Clone)]
pub struct Place{
    pub local : Local,
    pub projections : Box<[PlaceProjection]>
}
impl Place{
    pub fn project(self, projection : PlaceProjection) -> Self{
        Self { local: self.local, projections: self.projections.into_vec().into_iter().chain(std::iter::once(projection)).collect() }
    }
}
pub enum RValue {
    Use(Operand),
    Binary(BinaryOp,Box<(Operand,Operand)>),
    Unary(UnaryOp,Operand),
    Call(Operand,Box<[Operand]>),
    Array(Box<[Operand]>),
    Adt(Box<(DefId,GenericArgs,Option<VariantIndex>)>,IndexVec<FieldIndex,Operand>),
    Tuple(Box<[Operand]>),
}
pub enum Operand {
    Constant(Constant),
    Load(Place)
}
pub enum Stmt{
    Assign(Place,RValue),
    Print(Box<[Operand]>),
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
impl Local{
    pub const RETURN_PLACE : Local = Local(0);
}
impl From<Local> for Place{
    fn from(value: Local) -> Self {
        Place { local: value, projections: Box::new([]) }
    }
}
impl Display for BlockId{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("bb{}",self.0))
    }
}
pub struct LocalInfo{
    pub ty : Type
}
pub enum BodyKind {
    Anonymous,
    Function,
    Constructor
}
pub struct BodySource{
    pub id : DefId,
    pub kind : BodyKind,
    pub params : Vec<Type>,
    pub return_type : Type
}
pub struct Body{
    pub source : BodySource,
    pub locals : IndexVec<Local,LocalInfo>,
    pub blocks : IndexVec<BlockId,Block>
}


pub struct Mir{
    pub bodies : IndexVec<BodyIndex,Body>
}