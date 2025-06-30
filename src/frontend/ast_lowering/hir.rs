use std::collections::hash_map::Drain;
use std::fmt::Display;
use std::ops::Add;

use fxhash::FxHashMap;

use crate::define_id;
use crate::{data_structures::IndexVec, frontend::tokenizing::SourceLocation};

use crate::identifiers::{BodyIndex, ItemIndex, SymbolIndex, SymbolInterner, VariableIndex};
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, Default)]
pub struct HirId(u32);
impl HirId {
    pub fn new(id: u32) -> Self {
        HirId(id)
    }

    pub fn next(&self) -> Self {
        Self(self.0 + 1)
    }
}
define_id!(pub DefId);
impl Add<u32> for DefId {
    type Output = DefId;
    fn add(self, rhs: u32) -> Self::Output {
        Self(self.0 + rhs)
    }
}
pub struct DefIdProvider {
    next: u32,
}
impl DefIdProvider {
    pub fn new() -> Self {
        Self { next: 0 }
    }
    pub fn next(&mut self) -> DefId {
        let prev_id = self.next;
        self.next += 1;
        DefId(prev_id)
    }
}
pub struct FieldDef {
    pub name: Ident,
    pub ty: Type,
}
pub struct VariantDef {
    pub id: DefId,
    pub name: Ident,
    pub fields: Vec<Type>,
}
pub struct FunctionDef {
    pub id: DefId,
    pub generics: Generics,
    pub name: Ident,
    pub function: Function,
}
#[derive(Clone, Debug)]
pub struct Function {
    pub params: Vec<Type>,
    pub return_type: Option<Type>,
    pub body: BodyIndex,
}

#[derive(Clone, Debug)]
pub struct Param {
    pub pattern: Pattern,
}
pub struct GenericParam(pub Ident, pub DefId);
pub struct Generics {
    pub params: Vec<GenericParam>,
}
impl Generics {
    pub fn new() -> Self {
        Self {
            params: Default::default(),
        }
    }
}
pub struct StructDef {
    pub id: DefId,
    pub name: Ident,
    pub generics: Generics,
    pub fields: Vec<FieldDef>,
}
pub struct EnumDef {
    pub id: DefId,
    pub name: Ident,
    pub generics: Generics,
    pub variants: Vec<VariantDef>,
}
pub struct Impl {
    pub id: DefId,
    pub ty: Type,
    pub span: SourceLocation,
    pub generics: Generics,
    pub methods: Vec<FunctionDef>,
}
pub enum Item {
    Struct(StructDef),
    Enum(EnumDef),
    Function(FunctionDef),
    Impl(Impl),
}
impl Item {
    pub fn def_id(&self) -> DefId {
        match self {
            Self::Enum(enum_def) => enum_def.id,
            Self::Impl(impl_def) => impl_def.id,
            Self::Function(function_def) => function_def.id,
            Self::Struct(struct_def) => struct_def.id,
        }
    }
}
#[derive(Clone, Debug)]
pub struct Expr {
    pub id: HirId,
    pub span: SourceLocation,
    pub kind: ExprKind,
}
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum LiteralKind {
    Int(i64),
    Float(f64),
    String(SymbolIndex),
    Bool(bool),
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum BinaryOp {
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
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum UnaryOp {
    Negate,
}
#[derive(Clone, Copy, PartialEq, Debug, Hash, Eq)]
pub enum ConstructorKind {
    Struct,
    Variant,
}
impl Display for BinaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
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
            }
        )
    }
}

impl Display for UnaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::Negate => "-",
            }
        )
    }
}
#[derive(Clone, Copy, Debug)]
pub enum LogicalOp {
    And,
    Or,
}
impl Display for LogicalOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::And => "and",
                Self::Or => "or",
            }
        )
    }
}
#[derive(Clone, Debug)]
pub struct AnonFunction {
    pub id: DefId,
    pub function: Function,
}
#[derive(Clone, Debug)]
pub enum ExprKind {
    Literal(LiteralKind),
    Binary(BinaryOp, Box<Expr>, Box<Expr>),
    Unary(UnaryOp, Box<Expr>),
    Logical(LogicalOp, Box<Expr>, Box<Expr>),
    Call(Box<Expr>, Vec<Expr>),
    Print(Vec<Expr>),
    Tuple(Vec<Expr>),
    Array(Vec<Expr>),
    If(Box<Expr>, Box<Expr>, Option<Box<Expr>>),
    Match(Box<Expr>, Vec<MatchArm>),
    While(Box<Expr>, Box<Expr>),
    Path(PathExpr),
    Block(Vec<Stmt>, Option<Box<Expr>>),
    Function(Box<AnonFunction>),
    Field(Box<Expr>, Ident),
    Return(Option<Box<Expr>>),
    Index(Box<Expr>, Box<Expr>),
    Assign(Box<Expr>, Box<Expr>),
    MethodCall(Box<Expr>, PathSegment, Vec<Expr>),
    StructLiteral(InferOrPath, Vec<FieldExpr>),
}
#[derive(Clone, Debug)]
pub enum PathExpr {
    Infer(Ident),
    Path(QualifiedPath),
}
#[derive(Clone, Debug)]
pub struct MatchArm {
    pub pat: Pattern,
    pub body: Expr,
}
#[derive(Clone, Copy, Debug)]
pub struct Ident {
    pub index: SymbolIndex,
    pub span: SourceLocation,
}
#[derive(Clone, Debug)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: SourceLocation,
}
#[derive(Clone, Debug)]
pub enum StmtKind {
    Expr(Expr),
    Semi(Expr),
    Let(Pattern, Option<Type>, Expr),
    Item(ItemIndex),
}
#[derive(Clone, Debug)]
pub struct Pattern {
    pub id: HirId,
    pub kind: PatternKind,
    pub span: SourceLocation,
}
#[derive(Clone, Debug)]
pub struct FieldPattern {
    pub id: HirId,
    pub name: Ident,
    pub pattern: Pattern,
}
#[derive(Clone, Debug)]
pub enum InferOrPath {
    Path(QualifiedPath),
    Infer(SourceLocation, Option<Ident>),
}
#[derive(Clone, Debug)]
pub enum PatternKind {
    Binding(VariableIndex, Ident, Option<Box<Pattern>>),
    Tuple(Vec<Pattern>),
    Literal(LiteralKind),
    Variant(InferOrPath, Vec<Pattern>),
    Struct(InferOrPath, Vec<FieldPattern>),
    Path(QualifiedPath),
    Wildcard,
}
#[derive(Clone, Debug)]
pub struct Type {
    pub kind: TypeKind,
    pub span: SourceLocation,
}
impl Type {
    pub fn id(&self) -> Option<DefId> {
        match &self.kind {
            TypeKind::Path(QualifiedPath::FullyResolved(path)) => path.final_res.def_id(),
            _ => None,
        }
    }
    pub fn format(&self, interner: &SymbolInterner) -> String {
        match &self.kind {
            TypeKind::Array(ty) => format!("[{}]", ty.format(interner)),
            TypeKind::Path(path) => path.format(interner),
            TypeKind::Tuple(elements) => format!(
                "({})",
                &elements
                    .iter()
                    .enumerate()
                    .map(|(i, element)| {
                        if i > 0 {
                            format!(",{}", element.format(interner))
                        } else {
                            format!("{}", element.format(interner))
                        }
                    })
                    .collect::<String>()
            ),
            TypeKind::Function(params, return_type) => {
                let params = &params
                    .iter()
                    .enumerate()
                    .map(|(i, element)| {
                        if i > 0 {
                            format!(",{}", element.format(interner))
                        } else {
                            format!("{}", element.format(interner))
                        }
                    })
                    .collect::<String>();
                if let Some(return_type) = return_type.as_ref() {
                    format!("fun({})->{}", params, return_type.format(interner))
                } else {
                    format!("fun({})->()", params)
                }
            }
        }
    }
}
#[derive(Clone, Debug)]
pub enum TypeKind {
    Array(Box<Type>),
    Tuple(Vec<Type>),
    Function(Vec<Type>, Option<Box<Type>>),
    Path(QualifiedPath),
}
#[derive(Clone, Debug)]
pub struct PathSegment {
    pub res: Resolution,
    pub ident: Ident,
    pub args: Vec<GenericArg>,
}
#[derive(Debug, Clone)]
pub struct GenericArg {
    pub ty: Type,
}
impl PathSegment {
    pub fn format<'a>(&self, interner: &'a SymbolInterner) -> &'a str {
        interner.get(self.ident.index)
    }
}
#[derive(Clone, Debug)]
pub enum QualifiedPath {
    FullyResolved(Path),
    TypeRelative(Box<Type>, PathSegment),
}
impl QualifiedPath {
    pub fn format(&self, interner: &SymbolInterner) -> String {
        match self {
            Self::FullyResolved(path) => path.format(interner),
            Self::TypeRelative(ty, segment) => {
                format!("{}::{}", ty.format(interner), segment.format(interner))
            }
        }
    }
    pub fn span(&self) -> SourceLocation {
        match self {
            Self::FullyResolved(path) => path.span,
            Self::TypeRelative(ty, segment) => {
                SourceLocation::new(ty.span.start_line, segment.ident.span.end_line)
            }
        }
    }
}
#[derive(Clone, Debug)]
pub struct Path {
    pub span: SourceLocation,
    pub final_res: Resolution,
    pub segments: Vec<PathSegment>,
}
impl Path {
    pub fn format(&self, interner: &SymbolInterner) -> String {
        let mut full_path = String::new();
        for (i, segment) in self.segments.iter().enumerate() {
            if i > 0 {
                full_path += "::";
            }
            full_path += segment.format(interner);
        }
        full_path
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PrimitiveType {
    Int,
    Float,
    Bool,
    String,
    Never,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BuiltinKind {
    Panic,
}
#[derive(Debug, Clone, Copy, PartialEq, Hash, Eq)]
pub enum Resolution {
    Definition(DefKind, DefId),
    Primitive(PrimitiveType),
    Variable(VariableIndex),
    Builtin(BuiltinKind),
    SelfType(DefId),
    None,
}
impl Resolution {
    pub fn is_type(&self) -> bool {
        match self {
            Self::Definition(DefKind::Enum | DefKind::Struct | DefKind::Param, _)
            | Self::SelfType(_)
            | Self::Primitive(_) => true,
            _ => false,
        }
    }
    pub fn def_id(&self) -> Option<DefId> {
        match self {
            &Self::Definition(_, id) => Some(id),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum DefKind {
    AnonFunction,
    Function,
    Struct,
    Enum,
    Param,
    Variant,
    Method,
}
#[derive(Clone, Debug)]
pub struct FieldExpr {
    pub id: HirId,
    pub field: Ident,
    pub expr: Expr,
    pub span: SourceLocation,
}

#[derive(Debug)]
pub struct DefIdMap<T>(FxHashMap<DefId, T>);
impl<T> DefIdMap<T> {
    pub fn new() -> Self {
        Self(FxHashMap::default())
    }
    pub fn drain(&mut self) -> Drain<'_, DefId, T> {
        self.0.drain()
    }
    pub fn insert(&mut self, id: DefId, value: T) -> Option<T> {
        self.0.insert(id, value)
    }
    pub fn get(&self, id: DefId) -> Option<&T> {
        self.0.get(&id)
    }
    pub fn iter(&self) -> DefIdMapIter<'_, T> {
        DefIdMapIter(self.0.iter())
    }
    pub fn entry(&mut self, id: DefId) -> std::collections::hash_map::Entry<'_, DefId, T> {
        self.0.entry(id)
    }
}
impl<T> std::ops::Index<DefId> for DefIdMap<T> {
    type Output = T;
    fn index(&self, index: DefId) -> &Self::Output {
        &self.0[&index]
    }
}
impl<T> std::ops::IndexMut<DefId> for DefIdMap<T> {
    fn index_mut(&mut self, index: DefId) -> &mut Self::Output {
        if let Some(value) = self.0.get_mut(&index) {
            value
        } else {
            panic!("Expected a value with this id : {:?}", index)
        }
    }
}

pub struct DefIdMapIter<'a, T>(std::collections::hash_map::Iter<'a, DefId, T>);
impl<'a, T> Iterator for DefIdMapIter<'a, T> {
    type Item = (DefId, &'a T);
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(&id, val)| (id, val))
    }
}

pub struct Body {
    pub span: SourceLocation,
    pub params: Vec<Param>,
    pub value: Expr,
}
pub enum BodyOwner {
    Function(DefId),
    AnonFunction(DefId),
}
pub struct Hir {
    pub items: IndexVec<ItemIndex, Item>,
    pub defs_to_items: DefIdMap<ItemIndex>,
    pub owner_to_bodies: DefIdMap<BodyIndex>,
    pub body_owners: IndexVec<BodyIndex, BodyOwner>,
    pub bodies: IndexVec<BodyIndex, Body>,
}
