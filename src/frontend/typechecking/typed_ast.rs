use std::fmt::Display;


use crate::{data_structures::IndexVec, define_id, frontend::{ast_lowering::hir::{self, Ident}, tokenizing::SourceLocation}, identifiers::{EnumIndex, FieldIndex, FuncIndex, GenericParamIndex, StructIndex, SymbolIndex, VariableIndex, VariantIndex}};

use super::types::Type;

#[derive(Clone, Copy,Debug)]
pub enum NumberKind {
    Int(i64),
    Float(f64),
}
#[derive(Clone,Debug)]
pub struct Expr{
    pub span : SourceLocation,
    pub ty : Type,
    pub kind : ExprKind
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
    Struct(StructIndex),
    Variant(EnumIndex,VariantIndex)
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
pub struct PatternMatchArm{
    pub span : SourceLocation,
    pub pattern : Pattern,
    pub body : Expr,

}
#[derive(Clone,Debug)]
pub enum AssignmentTargetKind{
    Variable(VariableIndex),
    Index{
        lhs : Box<Expr>,
        rhs : Box<Expr>
    },
    Field{
        lhs : Box<Expr>,
        index : FieldIndex
    }
}
#[derive(Clone,Debug)]
pub enum ExprKind{
    Literal(hir::LiteralKind),
    Array(Vec<Expr>),
    Tuple(Vec<Expr>),
    Binary{
        op : BinaryOp,
        left : Box<Expr>,
        right : Box<Expr>
    },
    Logical{
        op : LogicalOp,
        left : Box<Expr>,
        right : Box<Expr>
    },
    Unary{
        op : UnaryOp,
        operand : Box<Expr>
    },
    If{
        condition : Box<Expr>,
        then_branch : Box<Expr>,
        else_branch : Option<Box<Expr>>
    },
    Block{
        stmts : Vec<Stmt>,
        expr : Option<Box<Expr>>
    },
    Index{
        lhs : Box<Expr>,
        rhs : Box<Expr>
    },
    Variable(VariableIndex),
    Print(Vec<Expr>),
    Match{
        matchee : Box<Expr>,
        arms : Vec<PatternMatchArm>
    },
    While{
        condition : Box<Expr>,
        body : Box<Expr>
    },
    Assign{
        lhs : Box<Expr>,
        rhs : Box<Expr>
    },
    Function(FuncIndex),
    AnonFunction(Function),
    Call{
        callee : Box<Expr>,
        args : Vec<Expr>
    },
    Return{
        expr : Option<Box<Expr>>
    },
    GetGeneric{
        name : GenericName,
        args : Vec<Type>
    },
    Typename(Type),
    Field(Box<Expr>,FieldIndex),
    Constructor{
        kind : ConstructorKind,
        fields : Vec<FieldExpr>
    },
}
#[derive(Clone,Debug)]
pub struct FieldExpr{
    pub index : FieldIndex,
    pub expr : Expr
}
#[derive(Clone,Debug)]
pub enum StmtKind {
    Expr(Expr),
    Let{
        pattern : Pattern,
        expr : Expr
    },
}

#[derive(Clone,Debug)]
pub struct Stmt{
    pub kind : StmtKind
}
#[derive(Clone,Debug)]
pub struct Pattern{
    pub span : SourceLocation,
    pub kind : PatternKind,
    pub ty : Type
}
#[derive(Clone,Debug)]
pub struct FieldPattern{
    pub index : FieldIndex,
    pub pattern : Pattern
}
#[derive(Clone,Debug)]
pub enum PatternKind{
    Binding(VariableIndex,Option<Box<Pattern>>),
    Wildcard,
    Tuple(Vec<Pattern>),
    Literal(hir::LiteralKind),
    Constructor{
        kind : ConstructorKind,
        fields : Vec<FieldPattern>
    },

}
#[derive(Clone,Debug)]
pub struct Function{
    pub signature : FunctionSignature,
    pub body : Box<Expr>,
}

#[derive(Clone,Debug)]
pub struct FunctionParam{
    pub pattern : Pattern,
    pub ty : Type
}
#[derive(Clone,Debug)]
pub struct FunctionSignature{
    pub params : Vec<FunctionParam>,
    pub return_type : Type
}
#[derive(Clone,Debug)]
pub struct Method{
    pub receiver_info : Option<bool>,
    pub name : Ident,
    pub is_generic : bool,
    pub function : Function
}

#[derive(Clone,Debug)]
pub enum GenericName{
    Function(FuncIndex),
    Method{
        ty : Type,
        method_name : String
    }
}
define_id!(FunctionId,doc = "An identifier for a fully type checked function.");

#[derive(Clone,Debug)]
pub struct Generics{
    pub names : IndexVec<GenericParamIndex,SymbolIndex>
}