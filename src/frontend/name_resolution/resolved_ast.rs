use std::collections::BTreeSet;

use crate::frontend::{parsing::ast::{LiteralKind, NodeId, PathSegment, Symbol}, tokenizing::SourceLocation, typechecking::{typed_ast::{BinaryOp, LogicalOp, UnaryOp}, types::Type}};

use super::{resolver::Scope, FieldIndex, VariableIndex};
#[derive(Clone)]
pub struct ResolvedExpr{
    pub span : SourceLocation,
    pub kind : ResolvedExprKind
}
#[derive(Clone,Copy)]
pub enum ConstructorKind{
    Enum,
    Struct
}
#[derive(Clone)]
pub enum ResolvedExprKind {
    Literal(LiteralKind),
    LocalVar,
    GlobalVar,
    Call(Box<ResolvedExpr>,Vec<ResolvedExpr>),
    Print(Vec<ResolvedExpr>),
    Binary(BinaryOp,Box<ResolvedExpr>,Box<ResolvedExpr>),
    Logical(LogicalOp,Box<ResolvedExpr>,Box<ResolvedExpr>),
    Unary(UnaryOp,Box<ResolvedExpr>),
    Return(Option<Box<ResolvedExpr>>),
    Field(Box<ResolvedExpr>,Symbol),
    Block{
        scope : Scope,
        stmts : Vec<ResolvedStmt>,
        expr : Option<Box<ResolvedExpr>>
    },
    Tuple(Vec<ResolvedExpr>),
    Array(Vec<ResolvedExpr>),
    Assign,
    Unit,
    Constructor{
        kind : ConstructorKind,
        fields : Vec<ConstructorField>
    },
    Typename(Type),
    Match(Box<ResolvedExpr>,Vec<ResolvedMatchArm>),
    Index(Box<ResolvedExpr>,Box<ResolvedExpr>),
    While(Box<ResolvedExpr>,Box<ResolvedExpr>),
    If(Box<ResolvedExpr>,Box<ResolvedExpr>,Option<Box<ResolvedExpr>>),
    FunctionExpr(Box<ResolvedFunction>),
    MethodCall(Box<ResolvedExpr>,PathSegment,Vec<ResolvedExpr>)
}

#[derive(Clone)]
pub struct ConstructorField{
    pub field : FieldIndex,
    pub expr : ResolvedExpr
}


#[derive(Clone)]
pub enum ResolvedStmt{
    Let(ResolvedPattern,Option<Type>,ResolvedExpr),
    Expr(ResolvedExpr),
    Semi(ResolvedExpr)
}
#[derive(Clone)]
pub struct  ResolvedPattern {
    pub span : SourceLocation,
    pub kind : ResolvedPatternKind
}

#[derive(Clone)]
pub struct ConstructorPatternField{
    pub field : FieldIndex,
    pub pattern : ResolvedPattern
}
#[derive(Clone)]
pub enum ResolvedPatternKind {
    Literal(LiteralKind),
    Unit,
    Tuple(Vec<ResolvedPattern>),
    Wildcard,
    Binding(VariableIndex,Option<Box<ResolvedPattern>>),
    Constructor(ConstructorKind,Vec<ConstructorPatternField>)
    
}

impl ResolvedPattern{
    pub fn find_bindings(&self,variables:&mut BTreeSet<VariableIndex>) {
        match &self.kind{
            &ResolvedPatternKind::Binding(binding, ref pattern) => {
                variables.insert(binding);
                if let Some(pattern) = pattern.as_ref(){
                    pattern.find_bindings(variables);
                }
            },
            ResolvedPatternKind::Tuple(elements) => elements.iter().for_each(|element| element.find_bindings(variables)),
            ResolvedPatternKind::Constructor(_, fields) => fields.iter().for_each(|field|{
                field.pattern.find_bindings(variables);
            }),
            ResolvedPatternKind::Unit | ResolvedPatternKind::Wildcard | ResolvedPatternKind::Literal(_) => {}
        }
    }
}
#[derive(Clone)]
pub struct ResolvedMatchArm{
    pub scope : Scope,
    pub pattern : ResolvedPattern,
    pub body : ResolvedExpr
}

#[derive(Clone)]
pub struct ResolvedFunctionParam{
    pub pattern : ResolvedPattern,
    pub ty : Type
}
#[derive(Clone)]
pub struct ResolvedFunction{
    pub scope : Scope,
    pub params : Vec<ResolvedFunctionParam>,
    pub return_type : Type,
    pub body : ResolvedExpr
}