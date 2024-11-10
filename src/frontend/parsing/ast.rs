use std::fmt::Display;

use crate::frontend::tokenizing::SourceLocation;

pub struct ParsedAssignmentTarget{
    pub location : SourceLocation,
    pub kind : ParsedAssignmentTargetKind
}
pub enum ParsedAssignmentTargetKind {
    Name(String),
    Index{
        lhs : Box<ExprNode>,
        rhs : Box<ExprNode>
    },
    Field{
        lhs : Box<ExprNode>,
        field : Symbol
    }
}
#[derive(Clone)]
pub enum LiteralKind {
    Int(i64),
    Float(f64),
    String(String),
    Bool(bool)
}
pub struct PatternMatchArmNode{
    pub location : SourceLocation,
    pub pattern : ParsedPatternNode,
    pub expr : ExprNode
}
pub enum ExprNodeKind {
    Literal(LiteralKind),
    Get(String),
    GetGeneric(String,ParsedGenericArgs),
    BinaryOp{
        op : ParsedBinaryOp,
        left : Box<ExprNode>,
        right : Box<ExprNode>
    },
    Unary{
        op : ParsedUnaryOp,
        operand : Box<ExprNode>
    },
    Logical{
        op : ParsedLogicalOp,
        left : Box<ExprNode>,
        right : Box<ExprNode>
    },
    Grouping(Box<ExprNode>),
    Match{
        matchee : Box<ExprNode>,
        arms : Vec<PatternMatchArmNode>
    },
    While{
        condition : Box<ExprNode>,
        body : Box<ExprNode>
    },
    If{
        condition : Box<ExprNode>,
        then_branch : Box<ExprNode>,
        else_branch : Option<Box<ExprNode>>
    },
    Block{
        stmts : Vec<StmtNode>,
        expr : Option<Box<ExprNode>>
    },
    Array(Vec<ExprNode>),
    Index{
        lhs : Box<ExprNode>,
        rhs : Box<ExprNode>
    },
    Tuple(Vec<ExprNode>),
    Print(Vec<ExprNode>),
    Assign{
        lhs : ParsedAssignmentTarget,
        rhs : Box<ExprNode>
    },
    Function(Box<ParsedFunction>),
    Call{
        callee : Box<ExprNode>,
        args : Vec<ExprNode>
    },
    Return(Option<Box<ExprNode>>),
    TypenameOf(ParsedType),
    Property(Box<ExprNode>,Symbol),
    StructInit{
        name : Symbol,
        generic_args : Option<ParsedGenericArgs>,
        fields : Vec<(Symbol,ExprNode)>
    }
}
pub enum ParsedBinaryOp {
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
impl Display for ParsedBinaryOp{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f,"{}",match self{
            ParsedBinaryOp::Add => "+",
            ParsedBinaryOp::Subtract => "-",
            ParsedBinaryOp::Multiply => "*",
            ParsedBinaryOp::Divide => "/",
            ParsedBinaryOp::Lesser => "<",
            ParsedBinaryOp::Greater => ">=",
            ParsedBinaryOp::LesserEquals => "<=",
            ParsedBinaryOp::GreaterEquals => "<=",
            ParsedBinaryOp::Equals => "==",
            ParsedBinaryOp::NotEquals => "!=",
        })
    }
}


#[derive(Clone, Copy)]
pub enum ParsedUnaryOp {
    Negate
}

impl Display for ParsedUnaryOp{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f,"{}",match self {
            ParsedUnaryOp::Negate => "-"
        })
    }
}
#[derive(Clone, Copy)]
pub enum ParsedLogicalOp {
    And,
    Or
}
impl Display for ParsedLogicalOp{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f,"{}",match self{
            ParsedLogicalOp::And => "and",
            ParsedLogicalOp::Or => "or"
        })
    }
}
pub struct ExprNode{
    pub location : SourceLocation,
    pub kind : ExprNodeKind
}

pub struct ParsedGenericParam(pub Symbol);
pub struct ParsedGenericParams(pub Vec<ParsedGenericParam>);

pub struct ParsedEnumVariant{
    pub name : Symbol,
    pub fields : Vec<(Symbol,ParsedType)>
}
pub enum StmtNode{
    Expr{
        expr : ExprNode,
        has_semi : bool
    },
    Let{
        pattern : ParsedPatternNode,
        expr : ExprNode,
        ty : Option<ParsedType>
    },
    Fun{
        name : Symbol,
        generic_params : Option<ParsedGenericParams>,
        function : ParsedFunction
    },
    Struct{
        name : Symbol,
        generic_params : Option<ParsedGenericParams>,
        fields : Vec<(Symbol,ParsedType)>
    },
    Enum{
        name : Symbol,
        variants : Vec<ParsedEnumVariant>
    }
}
#[derive(Clone)]
pub enum ParsedPatternNodeKind {
    Name(String),
    Tuple(Vec<ParsedPatternNode>),
    Literal(LiteralKind),
    Struct{
        name : ParsedPath,
        generic_args : Option<ParsedGenericArgs>,
        fields : Vec<(Symbol,ParsedPatternNode)>
    },
    Array(Vec<ParsedPatternNode>,Option<Box<ParsedPatternNode>>,Vec<ParsedPatternNode>),
    Wildcard
}



#[derive(Clone)]
pub struct ParsedPatternNode{
    pub location : SourceLocation,
    pub kind : ParsedPatternNodeKind
}
#[derive(Clone,Debug)]
pub struct Symbol{
    pub content : String,
    pub location : SourceLocation
}

#[derive(Clone)]
pub enum ParsedType{
    Name(Symbol),
    Array(Box<ParsedType>),
    Tuple(Vec<ParsedType>),
    Fun(Vec<ParsedType>,Option<Box<ParsedType>>),
    NameWithArgs(Symbol,ParsedGenericArgs),
}

pub struct ParsedParam{
    pub pattern : ParsedPatternNode,
    pub ty : ParsedType
}

pub struct ParsedFunction{
    pub params : Vec<ParsedParam>,
    pub return_type : Option<ParsedType>,
    pub body : ExprNode
}
#[derive(Clone)]
pub struct ParsedGenericArgs{
    pub location : SourceLocation,
    pub types : Vec<ParsedType>
}


#[derive(Clone)]
pub struct PathSegment{
    pub name : Symbol,
    pub generic_args : Option<ParsedGenericArgs>
}
#[derive(Clone)]
pub struct ParsedPath{
    pub head : PathSegment,
    pub segments : Vec<PathSegment>,
    pub location : SourceLocation
}