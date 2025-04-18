use std::fmt::Display;

use fxhash::FxHashMap;

use crate::define_id;
use crate::{data_structures::IndexVec, frontend::tokenizing::SourceLocation};

use crate::identifiers::{ItemIndex, SymbolIndex, SymbolInterner, VariableIndex};
#[derive(Debug,Clone, Copy,Hash,PartialEq,Eq,Default)]
pub struct HirId(u32);
impl HirId{
    pub fn new(id : u32) -> Self{
        HirId(id)
    }

    pub fn next(&self) -> Self{
        Self(self.0 + 1)
    }
}
define_id!(DefId);
pub struct DefIdProvider{
    next : u32
}
impl DefIdProvider{
    pub fn new() -> Self{
        Self { next: 0 }
    }
    pub fn next(&mut self) -> DefId{
        let prev_id = self.next;
        self.next+=1;
        DefId(prev_id)
    }
}
pub struct FieldDef{
    pub name : Ident,
    pub ty : Type
}
pub struct VariantDef{
    pub id : DefId,
    pub name : Ident,
    pub fields : Vec<FieldDef>
}
pub struct FunctionDef{
    pub id : DefId,
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
pub struct GenericParam(pub Ident,pub DefId);
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
pub struct StructDef{
    pub id : DefId,
    pub name : Ident,
    pub generics: Generics,
    pub fields : Vec<FieldDef>
}
pub struct EnumDef{
    pub id : DefId,
    pub name : Ident,
    pub generics:Generics,
    pub variants:Vec<VariantDef>
}
pub enum Item {
    Struct(StructDef),
    Enum(EnumDef),
    Function(FunctionDef),
    Impl(Type,Vec<FunctionDef>)
}
#[derive(Clone,Debug)]
pub struct Expr{
    pub id : HirId,
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

#[derive(Clone, Copy,PartialEq,Debug)]
pub enum BinaryOp{
    Add,
    Subtract,
    Multiply,
    Divide,

    Lesser,
    Greater,
    LesserEquals,
    GreaterEquals,
    Equals,
    NotEquals,
}
#[derive(Clone,Copy,PartialEq,Debug)]
pub enum UnaryOp{
    Negate
}
#[derive(Clone,Copy,PartialEq,Debug,Hash,Eq)]
pub enum ConstructorKind {
    Struct,
    Variant
}
impl Display for BinaryOp{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f,"{}",match self{
            Self::Add => "+",
            Self::Subtract => "-",
            Self::Multiply => "*",
            Self::Divide => "/",
            Self::Lesser => "<",
            Self::LesserEquals => "<=",
            Self::Greater => ">",
            Self::GreaterEquals => ">=",
            Self::Equals => "==",
            Self::NotEquals => "!=",
        })
    }
}

impl Display for UnaryOp{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f,"{}",match self{
            Self::Negate => "-"
        })
    }
}
#[derive(Clone, Copy,Debug)]
pub enum LogicalOp{
    And,
    Or
}
impl Display for LogicalOp{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f,"{}",match self {
            Self::And => "and",
            Self::Or => "or"
        })
    }
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
    Typename(HirId,Type),
    Field(Box<Expr>,Ident),
    Return(Option<Box<Expr>>),
    Index(Box<Expr>,Box<Expr>),
    Assign(Box<Expr>,Box<Expr>),
    MethodCall(Box<Expr>,Ident,Vec<GenericArg>,Vec<Expr>),
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
    pub id : HirId,
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
    pub res : Resolution,
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
    pub final_res : Resolution,
    pub segments : Vec<PathSegment>
}
impl Path{
    pub fn format(&self,interner:&SymbolInterner) -> String{
        let mut full_path = String::new();
        for (i,segment) in self.segments.iter().enumerate(){
            if i>0{
                full_path+="::";
            }
            full_path+=interner.get(segment.ident.index);
        }
        full_path
    }
}
#[derive(Clone,Copy,Debug,PartialEq, Eq,Hash)]
pub enum PrimitiveType {
    Int,
    Float,
    Bool,
    String,
    Never,
}
#[derive(Debug,Clone,Copy,PartialEq,Hash,Eq)]
pub enum Resolution {
    Definition(DefKind,DefId),
    Primitive(PrimitiveType),
    Variable(VariableIndex),
}


#[derive(Clone,Copy,PartialEq, Eq,Hash,Debug)]
pub enum GenericOwner {
    Struct(DefId),
    Enum(DefId),
    Function(DefId),
}



#[derive(Clone, Copy,Debug,PartialEq,Eq,Hash)]
pub enum DefKind {
    Function,
    Struct,
    Enum,
    Param,
    Variant,
}
#[derive(Clone,Debug)]
pub struct FieldExpr{
    pub field : Ident,
    pub expr : Expr,
    pub span : SourceLocation
}


pub struct DefIdMap<T>(FxHashMap<DefId,T>);
impl<T> DefIdMap<T>{
    pub fn new() -> Self{
        Self(FxHashMap::default())
    }
    pub fn insert(&mut self,id:DefId,value:T)->Option<T>{
        self.0.insert(id, value)
    }
    pub fn get(&self,id:DefId) -> Option<&T>{
        self.0.get(&id)
    }
}
impl<T> std::ops::Index<DefId> for DefIdMap<T>{
    type Output = T;
    fn index(&self, index: DefId) -> &Self::Output {
        &self.0[&index]
    }
}
impl<T> std::ops::IndexMut<DefId> for DefIdMap<T>{

    fn index_mut(&mut self, index: DefId) -> &mut Self::Output {
        if let Some(value) = self.0.get_mut(&index){
            value
        }
        else{
            panic!("Expected a value with this id : {:?}",index)
        }
    }
}


pub struct Hir{
    pub items : IndexVec<ItemIndex,Item>,
    pub defs_to_items : DefIdMap<ItemIndex>,
    pub stmts : Vec<Stmt>
}
