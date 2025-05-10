use crate::identifiers::{SymbolIndex, SymbolInterner};
use super::parsing::ast;

pub mod hir;
pub mod ast_lower;
pub mod name_finding;
pub mod resolve;
pub mod scope;
impl From<ast::Symbol> for hir::Ident{
    fn from(value: ast::Symbol) -> Self {
        hir::Ident{
            index:value.content,
            span:value.location
        }
    }
}