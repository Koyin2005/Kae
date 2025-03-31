use crate::{data_structures::IndexVec, frontend::{tokenizing::SourceLocation, typechecking::typed_ast::{BinaryOp, LogicalOp, UnaryOp}}, identifiers::GenericParamIndex};

use crate::identifiers::{EnumIndex, FieldIndex, FuncIndex, ItemIndex, MethodIndex, StructIndex, SymbolIndex, VariantIndex, VariableIndex};
pub struct FieldDef{
    pub name : Ident,
    pub ty : Type
}
pub struct VariantDef{
    pub name : Ident,
    pub fields : IndexVec<FieldIndex,FieldDef>
}
pub struct FunctionDef{
    pub generics : Generics,
    pub name : Ident,
    pub function : Function
}
#[derive(Clone,Debug)]
pub struct Function{
    pub params : Vec<Param>,
    pub return_type : Option<Type>,
    pub body : Expr
}

#[derive(Clone,Debug)]
pub struct Param{
    pub pattern : Pattern,
    pub ty : Type
}
pub struct GenericParam(pub Ident);
pub struct Generics{
    pub params : Vec<GenericParam>
}
impl Generics{
    pub fn new()->Self{
        Self{
            params : Default::default()
        }
    }
}
pub enum Item {
    Struct(Generics,VariantDef),
    Enum(Generics,Ident,IndexVec<VariantIndex,VariantDef>),
    Function(FunctionDef),
    Impl(Type,IndexVec<MethodIndex,FunctionDef>)
}
#[derive(Clone,Debug)]
pub struct Expr{
    pub span : SourceLocation,
    pub kind : ExprKind
}
#[derive(Clone,Copy,Debug)]
pub enum LiteralKind {
    Int(i64),
    Float(f64),
    String(SymbolIndex),
    Bool(bool)
}
#[derive(Clone,Debug)]
pub enum ExprKind {
    Literal(LiteralKind),
    Binary(BinaryOp,Box<Expr>,Box<Expr>),
    Unary(UnaryOp,Box<Expr>),
    Logical(LogicalOp,Box<Expr>,Box<Expr>),
    Call(Box<Expr>,Vec<Expr>),
    Print(Vec<Expr>),
    Tuple(Vec<Expr>),
    Array(Vec<Expr>),
    If(Box<Expr>,Box<Expr>,Option<Box<Expr>>),
    Match(Box<Expr>,Vec<MatchArm>),
    While(Box<Expr>,Box<Expr>),
    Path(Path),
    Block(Vec<Stmt>,Option<Box<Expr>>),
    Function(Box<Function>),
    Typename(Type),
    Field(Box<Expr>,Ident),
    Return(Option<Box<Expr>>),
    Index(Box<Expr>,Box<Expr>),
    Assign(Box<Expr>,Box<Expr>),
    StructLiteral(Path,Vec<FieldExpr>),
}
#[derive(Clone,Debug)]
pub struct MatchArm{
    pub pat : Pattern,
    pub body : Expr
}
#[derive(Clone,Copy,Debug)]
pub struct Ident{
    pub index : SymbolIndex,
    pub span : SourceLocation
}
#[derive(Clone,Debug)]
pub struct Stmt{
    pub kind : StmtKind,
    pub span : SourceLocation
}
#[derive(Clone,Debug)]
pub enum StmtKind {
    Expr(Expr),
    Semi(Expr),
    Let(Pattern,Option<Type>,Expr),
    Item(ItemIndex)
}
#[derive(Clone,Debug)]
pub struct Pattern{
    pub kind : PatternKind,
    pub span : SourceLocation
}
#[derive(Clone,Debug)]
pub struct FieldPattern{
    pub name : Ident,
    pub pattern : Pattern
}
#[derive(Clone,Debug)]
pub enum PatternKind {
    Binding(VariableIndex,Ident,Option<Box<Pattern>>),
    Tuple(Vec<Pattern>),
    Literal(LiteralKind),
    Struct(Path,Vec<FieldPattern>),
    Wildcard
}
#[derive(Clone,Debug)]
pub struct Type{
    pub kind : TypeKind,
    pub span : SourceLocation
}
#[derive(Clone,Debug)]
pub enum TypeKind {
    Array(Box<Type>),
    Tuple(Vec<Type>),
    Function(Vec<Type>,Option<Box<Type>>),
    Path(Path)
}
#[derive(Clone,Debug)]
pub struct PathSegment{
    pub def : PathDef,
    pub ident : Ident,
    pub args : Vec<GenericArg>,

}
#[derive(Debug,Clone)]
pub struct GenericArg{
    pub ty : Type
}
#[derive(Clone,Debug)]
pub struct Path{
    pub span : SourceLocation,
    pub def : PathDef,
    pub segments : Vec<PathSegment>
}
#[derive(Clone,Copy,Debug,PartialEq, Eq,Hash)]
pub enum PrimitiveType {
    Int,
    Float,
    Bool,
    String,
    Never,
}
#[derive(Clone,Copy,PartialEq, Eq,Hash,Debug)]
pub enum PathDef {
    Variable(VariableIndex),
    PrimitiveType(PrimitiveType),
    Function(FuncIndex),
    Struct(StructIndex),
    Enum(EnumIndex),
    Variant(EnumIndex,VariantIndex),
    GenericParam(GenericParamIndex,SymbolIndex)
}


#[derive(Clone,Copy,PartialEq, Eq,Hash,Debug)]
pub enum GenericOwner {
    Struct(StructIndex),
    Enum(EnumIndex),
    Function(FuncIndex),
}

#[derive(Clone, Copy,Debug,PartialEq,Eq,Hash)]
pub enum Namespace {
    Value,
    Type
}


#[derive(Clone, Copy,Debug,PartialEq,Eq,Hash)]
pub enum DefKind {
    Function,
    Struct,
    Enum,
    Variant,
}
#[derive(Clone,Debug)]
pub struct FieldExpr{
    pub field : Ident,
    pub expr : Expr,
    pub span : SourceLocation
}

