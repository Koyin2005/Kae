use crate::{
    data_structures::IndexVec,
    define_id,
    identifiers::{BodyIndex, FieldIndex, SymbolIndex, VariableIndex, VariantIndex},
};

use super::{
    ast_lowering::hir::{self, BinaryOp, DefId, DefIdMap, LiteralKind, LogicalOp, UnaryOp},
    tokenizing::SourceLocation,
    typechecking::types::{AdtKind, Type, generics::GenericArgs},
};

define_id!(pub ExprId);
define_id!(pub BlockId);
define_id!(pub StmtId);
define_id!(pub ArmId);
define_id!(pub ParamId);
#[derive(Debug)]
pub struct FieldPattern {
    pub field: FieldIndex,
    pub pattern: Pattern,
}
#[derive(Debug)]
pub struct Pattern {
    pub ty: Type,
    pub span: SourceLocation,
    pub kind: PatternKind,
}
#[derive(Debug)]
pub enum PatternKind {
    Binding(SymbolIndex, VariableIndex, Option<Box<Pattern>>),
    Constant(LiteralKind),
    Tuple(Box<[Pattern]>),
    Struct(DefId, GenericArgs, Box<[FieldPattern]>),
    Variant(DefId, GenericArgs, VariantIndex, Box<[Pattern]>),
    Wildcard,
}
#[derive(Debug)]
pub struct FieldExpr {
    pub field: FieldIndex,
    pub expr: ExprId,
}
#[derive(Debug)]
pub struct StructLiteral {
    pub kind: AdtKind,
    pub id: DefId,
    pub generic_args: GenericArgs,
    pub variant: Option<VariantIndex>,
    pub fields: Box<[FieldExpr]>,
}
#[derive(Debug)]
pub struct Expr {
    pub ty: Type,
    pub kind: ExprKind,
    pub span: SourceLocation,
}
#[derive(Debug, Clone, Copy)]
pub enum FunctionKind {
    Method,
    Anon,
    Normal,
    Variant,
}
#[derive(Debug)]
pub struct Function {
    pub id: DefId,
    pub kind: FunctionKind,
    pub generic_args: GenericArgs,
}
#[derive(Debug)]
pub enum ExprKind {
    Literal(LiteralKind),
    Binary(BinaryOp, ExprId, ExprId),
    Unary(UnaryOp, ExprId),
    Logical(LogicalOp, ExprId, ExprId),
    Call(ExprId, Vec<ExprId>),
    Array(Box<[ExprId]>),
    Tuple(Box<[ExprId]>),
    Field(ExprId, FieldIndex),
    Assign(ExprId, ExprId),
    If(ExprId, ExprId, Option<ExprId>),
    Return(Option<ExprId>),
    Variable(VariableIndex),
    Function(Function),
    Builtin(GenericArgs, hir::BuiltinKind),
    Print(Box<[ExprId]>),
    Index(ExprId, ExprId),
    Match(ExprId, Box<[ArmId]>),
    Block(BlockId),
    While(ExprId, ExprId),
    StructLiteral(Box<StructLiteral>),
    NeverCast(ExprId),
}
#[derive(Debug)]
pub struct Stmt {
    pub kind: StmtKind,
}
#[derive(Debug)]
pub enum StmtKind {
    Expr(ExprId),
    Let(Box<Pattern>, ExprId),
}
#[derive(Debug)]
pub struct Block {
    pub stmts: Box<[StmtId]>,
    pub expr: Option<ExprId>,
}
#[derive(Debug)]
pub struct Arm {
    pub pat: Box<Pattern>,
    pub body: ExprId,
}

pub struct Param {
    pub pattern: Pattern,
    pub ty: Type,
}
pub struct ThirBody {
    pub params: IndexVec<ParamId, Param>,
    pub exprs: IndexVec<ExprId, Expr>,
    pub blocks: IndexVec<BlockId, Block>,
    pub stmts: IndexVec<StmtId, Stmt>,
    pub arms: IndexVec<ArmId, Arm>,
}
pub struct Thir {
    pub body_owners: DefIdMap<BodyIndex>,
    pub bodies: IndexVec<BodyIndex, (ThirBody, ExprId)>,
}
