use std::{fmt::Display, rc::Rc};

use crate::frontend::{parsing::ast::Symbol, tokenizing::SourceLocation};

use super::types::{EnumId, StructId, Type};
#[derive(Clone, Copy,Debug)]
pub enum NumberKind {
    Int(i64),
    Float(f64),
}
#[derive(Clone,Debug)]
pub struct TypedExprNode{
    pub location : SourceLocation,
    pub ty : Type,
    pub kind : TypedExprNodeKind
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
#[derive(Clone, Copy,PartialEq,Debug)]
pub enum UnaryOp{
    Negate
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
pub struct TypedPatternMatchArm{
    pub location : SourceLocation,
    pub ty : Type,
    pub pattern : PatternNode,
    pub expr : TypedExprNode,

}
#[derive(Clone,Debug)]
pub enum TypedAssignmentTargetKind{
    Variable(String),
    Index{
        lhs : Box<TypedExprNode>,
        rhs : Box<TypedExprNode>
    },
    Field{
        lhs : Box<TypedExprNode>,
        name : Symbol
    }
}
#[derive(Clone,Debug)]
pub struct TypedAssignmentTarget{
    pub location : SourceLocation,
    pub ty : Type,
    pub kind : TypedAssignmentTargetKind
}
#[derive(Clone,Debug,Copy)]
pub enum InitKind{
    Variant(EnumId,usize),
    Struct(StructId)
}
#[derive(Clone,Debug)]
pub enum TypedExprNodeKind{
    Unit,
    Number(NumberKind),
    String(Rc<str>),
    Bool(bool),
    Array(Vec<TypedExprNode>),
    Tuple(Vec<TypedExprNode>),
    Binary{
        op : BinaryOp,
        left : Box<TypedExprNode>,
        right : Box<TypedExprNode>
    },
    Logical{
        op : LogicalOp,
        left : Box<TypedExprNode>,
        right : Box<TypedExprNode>
    },
    Unary{
        op : UnaryOp,
        operand : Box<TypedExprNode>
    },
    If{
        condition : Box<TypedExprNode>,
        then_branch : Box<TypedExprNode>,
        else_branch : Option<Box<TypedExprNode>>
    },
    Block{
        stmts : Vec<TypedStmtNode>,
        expr : Option<Box<TypedExprNode>>
    },
    Index{
        lhs : Box<TypedExprNode>,
        rhs : Box<TypedExprNode>
    },
    Get(String),
    Print(Vec<TypedExprNode>),
    Match{
        matchee : Box<TypedExprNode>,
        arms : Vec<TypedPatternMatchArm>
    },
    While{
        condition : Box<TypedExprNode>,
        body : Box<TypedExprNode>
    },
    Assign{
        lhs : TypedAssignmentTarget,
        rhs : Box<TypedExprNode>
    },
    Function(TypedFunction),
    Call{
        callee : Box<TypedExprNode>,
        args : Vec<TypedExprNode>
    },
    Return{
        expr : Option<Box<TypedExprNode>>
    },
    GetGeneric{
        name : String,
        args : Vec<Type>
    },
    TypenameOf(Type),
    Field(Box<TypedExprNode>,Symbol),
    StructInit{
        kind : InitKind,
        fields : Vec<(String,TypedExprNode)>
    },
    MethodCall{
        by_ref : bool,
        lhs : Box<TypedExprNode>,
        method : Symbol,
        args : Vec<TypedExprNode>
    },
    GetMethod{
       ty : Type,
       method : Symbol 
    }
}
#[derive(Clone,Debug)]
pub enum TypedStmtNode {
    ExprWithSemi(TypedExprNode),
    Expr(TypedExprNode),
    Let{
        pattern : PatternNode,
        expr : TypedExprNode
    },
    Fun{
        name : Symbol,
        function : TypedFunction
    },
    GenericFunction{
        name : Symbol,
        generic_params : Vec<usize>,
        function : TypedFunction,
    },
    Struct{
        name : Symbol,
        generic_params : Vec<usize>,
        fields : Vec<(String,Type)>
    },
    Enum{
        name : Symbol,
        variants : Vec<TypedEnumVariant>
    },
    Impl{
        ty : Type,
        methods : Vec<TypedMethod>,
    },
}
#[derive(Clone,Debug)]
pub struct PatternNode{
    pub location : SourceLocation,
    pub kind : PatternNodeKind
}
#[derive(Clone,Debug)]
pub enum PatternNodeKind{
    Name(String),
    Wildcard,
    Tuple(Vec<PatternNode>),
    Int(i64),
    Float(f64),
    String(String),
    Bool(bool),
    Struct{
        ty : Type,
        fields : Vec<(String,PatternNode)>
    },
    Array(Vec<PatternNode>,Option<Box<PatternNode>>,Vec<PatternNode>),
    Is(Symbol,Box<PatternNode>)

}
#[derive(Clone,Debug)]
pub struct TypedFunction{
    pub signature : TypedFunctionSignature,
    pub body : Box<TypedExprNode>,
}

#[derive(Clone,Debug)]

pub struct TypedFunctionSignature{
    pub params : Vec<(PatternNode,Type)>,
    pub return_type : Type
}
#[derive(Clone,Debug)]
pub struct TypedEnumVariant{
    pub name : Symbol,
    pub fields : Vec<(Symbol,Type)>,
}

#[derive(Clone,Debug)]
pub struct TypedMethod{
    pub receiver_info : Option<bool>,
    pub name : Symbol,
    pub function : TypedFunction
}