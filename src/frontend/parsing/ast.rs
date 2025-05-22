use std::fmt::Display;

use crate::{frontend::tokenizing::SourceLocation, identifiers::SymbolIndex};

#[derive(Clone, Copy,Debug,Hash,PartialEq,Eq,PartialOrd, Ord)]
pub struct NodeId(usize);
impl NodeId{
    pub const FIRST : Self = Self(0);
    pub fn next(&self)->Self{
        Self(self.0 + 1)
    }
}
pub struct ParsedAssignmentTarget{
    pub location : SourceLocation,
    pub kind : ParsedAssignmentTargetKind
}
pub enum ParsedAssignmentTargetKind {
    Name(Path),
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
    pub id : NodeId,
    pub location : SourceLocation,
    pub pattern : ParsedPatternNode,
    pub expr : ExprNode
}
pub enum ExprNodeKind {
    Literal(LiteralKind),
    GetPath(InferPath),
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
    Instantiate{
        lhs : Box<ExprNode>,
        args : ParsedGenericArgs
    },
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
    Function(FunctionSig,Box<ExprNode>),
    Call{
        callee : Box<ExprNode>,
        args : Vec<ExprNode>
    },
    Return(Option<Box<ExprNode>>),
    TypenameOf(ParsedType),
    Property(Box<ExprNode>,Symbol),
    StructInit{
        path : InferPath,
        fields : Vec<(Symbol,ExprNode)>
    },
    MethodCall{
        receiver:Box<ExprNode>,
        method : PathSegment,
        args : Vec<ExprNode>
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
    pub id : NodeId,
    pub kind : ExprNodeKind
}

pub struct ParsedGenericParam(pub Symbol);
pub struct ParsedGenericParams(pub NodeId,pub Vec<ParsedGenericParam>);

pub struct ParsedEnumVariant{
    pub name : Symbol,
    pub fields : Vec<(Symbol,ParsedType)>
}

pub struct StructDef{ 
    pub name : Symbol,
    pub id : NodeId,
    pub generic_params : Option<ParsedGenericParams>,
    pub fields : Vec<(Symbol,ParsedType)>
}
pub struct EnumDef{
    pub name : Symbol,
    pub id : NodeId,
    pub generic_params : Option<ParsedGenericParams>,
    pub variants : Vec<ParsedEnumVariant>
}
pub struct Impl{
    pub span : SourceLocation,
    pub id : NodeId,
    pub generic_params : Option<ParsedGenericParams>,
    pub ty : ParsedType,
    pub methods : Vec<ParsedMethod>
}
pub struct FuncDef{
    pub id : NodeId,
    pub function : ParsedFunction
}
pub enum Item {
    Fun(FuncDef),
    Struct(StructDef),
    Enum(EnumDef),
    Impl(Impl)
}
pub enum StmtNode{
    Expr{
        expr : ExprNode,
        has_semi : bool
    },
    Let{
        id : NodeId,
        pattern : ParsedPatternNode,
        expr : ExprNode,
        ty : Option<ParsedType>
    },
    Item(Item)
}
#[derive(Clone)]
pub enum ParsedPatternNodeKind {
    Is(Symbol,Box<ParsedPatternNode>),
    Name(SymbolIndex),
    Tuple(Vec<ParsedPatternNode>),
    Literal(LiteralKind),
    Struct{
        path : InferPath,
        fields : Vec<(Symbol,ParsedPatternNode)>
    },
    Path(Path),
    Infer(Symbol),
    Wildcard
}


#[derive(Clone)]
pub struct ParsedPatternNode{
    pub location : SourceLocation,
    pub id : NodeId,
    pub kind : ParsedPatternNodeKind
}
#[derive(Clone,Debug,Copy)]
pub struct Symbol{
    pub content : SymbolIndex,
    pub location : SourceLocation
}

#[derive(Clone,Debug)]
pub enum ParsedType{
    Path(Path),
    Array(SourceLocation,Box<ParsedType>),
    Tuple(SourceLocation,Vec<ParsedType>),
    Fun(SourceLocation,Vec<ParsedType>,Option<Box<ParsedType>>),
}

pub struct ParsedParam{
    pub pattern : ParsedPatternNode,
    pub ty : ParsedType,
    pub by_ref : bool,
}

pub struct ParsedMethod{
    pub id : NodeId,
    pub has_receiver : bool,
    pub function : ParsedFunction,
}
pub struct FunctionProto{
    pub name : Symbol,
    pub generic_params : Option<ParsedGenericParams>,
    pub sig : FunctionSig
}
pub struct FunctionSig{
    pub params : Vec<ParsedParam>,
    pub return_type : Option<ParsedType>,
}
pub struct ParsedFunction{
    pub proto : FunctionProto,
    pub body : ExprNode
}
#[derive(Clone,Debug)]
pub struct ParsedGenericArgs{
    pub location : SourceLocation,
    pub types : Vec<ParsedType>
}


#[derive(Clone,Debug)]
pub struct PathSegment{
    pub name : Symbol,
    pub generic_args : Option<ParsedGenericArgs>,
    pub location : SourceLocation
}
#[derive(Clone,Debug)]
pub struct Path{
    pub segments : Vec<PathSegment>,
    pub location : SourceLocation,
}
impl From<Path> for InferPath{
    fn from(value: Path) -> Self {
        Self { location: value.location, infer_path: InferPathKind::Path(value) }
    }
}
#[derive(Clone)]
pub struct InferPath{
    pub location : SourceLocation,
    pub infer_path : InferPathKind
}
#[derive(Clone)]
pub enum InferPathKind {
    Path(Path),
    Infer(Option<Symbol>)
}