use crate::{data_structures::IndexVec, define_id, identifiers::{BodyIndex, FieldIndex, SymbolIndex, VariableIndex, VariantIndex}};

use super::{ast_lowering::hir::{self, BinaryOp, DefId, LiteralKind, LogicalOp, UnaryOp}, tokenizing::SourceLocation, typechecking::types::{generics::GenericArgs, AdtKind, Type}};

define_id!(ExprId);
define_id!(BlockId);
define_id!(StmtId);
define_id!(ArmId);
pub struct FieldPattern{
    pub field : FieldIndex,
    pub pattern : Pattern
}
pub struct Pattern{
    pub ty: Type,
    pub span: SourceLocation,
    pub kind: PatternKind
}
pub enum PatternKind {
    Binding(SymbolIndex,VariableIndex,Option<Box<Pattern>>),
    Constant(LiteralKind),
    Tuple(Box<[Pattern]>),
    Variant(GenericArgs,DefId,Option<VariantIndex>,Box<[FieldPattern]>),
    Wildcard
}
pub struct FieldExpr{
    pub field : FieldIndex,
    pub expr : ExprId
}
pub struct StructLiteral{
    pub kind : AdtKind,
    pub id : DefId,
    pub variant : Option<VariantIndex>,
    pub fields : Box<[FieldExpr]>
}
pub struct Expr{
    pub ty: Type,
    pub kind: ExprKind,
    pub span: SourceLocation
}

pub enum ExprKind {
    Literal(LiteralKind),
    Binary(BinaryOp,ExprId,ExprId),
    Unary(UnaryOp,ExprId),
    Logical(LogicalOp,ExprId,ExprId),
    Call(ExprId,Vec<ExprId>),
    Array(Box<[ExprId]>),
    Tuple(Box<[ExprId]>),
    Field(ExprId,FieldIndex),
    Assign(ExprId,ExprId),
    If(ExprId,ExprId,Option<ExprId>),
    Return(Option<ExprId>),
    Variable(VariableIndex),
    Definition(GenericArgs,DefId),
    Function(BodyIndex),
    Builtin(GenericArgs,hir::BuiltinKind),
    Print(Box<[ExprId]>),
    Index(ExprId,ExprId),
    Match(ExprId,Box<[ArmId]>),
    Block(BlockId),
    While(ExprId,ExprId),
    StructLiteral(Box<StructLiteral>)
}
pub struct Stmt{
    pub kind : StmtKind
}
pub enum StmtKind {
    Expr{expr:ExprId,drop:bool},
    Let(Box<Pattern>,ExprId),
}
pub struct Block{
    pub stmts : Box<[StmtId]>,
    pub expr : Option<ExprId>
}
pub struct Arm{
    pub pat : Box<Pattern>,
    pub body : ExprId
}

pub struct ThirBody{
    pub exprs : IndexVec<ExprId,Expr>,
    pub blocks : IndexVec<BlockId,Block>,
    pub stmts : IndexVec<StmtId,Stmt>,
    pub arms : IndexVec<ArmId,Arm>
}
pub struct Thir{
    pub bodies : IndexVec<BodyIndex,ThirBody>
}