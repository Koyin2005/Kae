use super::{tokenizing::SourceLocation, typechecking::types::Type};

pub struct Expr{
    pub ty: Type,
    pub kind: ExprKind,
    pub span: SourceLocation
}
pub enum ExprKind {
    Literal
}