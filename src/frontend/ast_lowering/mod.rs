use std::collections::HashMap;

use crate::{data_structures::IndexVec, identifiers::SymbolIndex};
use super::parsing::ast;

pub mod hir;
pub mod ast_lower;
pub mod name_finding;
pub struct SymbolInterner{
    idents : IndexVec<SymbolIndex,String>,
    ident_map : HashMap<String,SymbolIndex>
}
impl SymbolInterner{
    pub fn new()->Self{
        Self { idents: Default::default() ,ident_map : HashMap::default() }
    }
    pub fn intern(&mut self,identifier : String) -> SymbolIndex{
        if let Some(ident) = self.ident_map.get(&identifier){
            return *ident;
        }
        let ident = self.idents.push(identifier.clone());
        self.ident_map.insert(identifier, ident);
        ident
    }
    pub fn intern_symbol(&mut self,symbol:ast::Symbol) -> hir::Ident{
        let index = self.intern(symbol.content);
        hir::Ident{
            span:symbol.location,
            index
        }
    }
    pub fn get(&self,ident : SymbolIndex) -> &str{
        &self.idents[ident]
    }   
}
