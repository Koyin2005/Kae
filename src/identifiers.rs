

use std::collections::HashMap;

use crate::{data_structures::IndexVec, define_id};

define_id!(SymbolIndex);
define_id!(ItemIndex);
define_id!(ScopeIndex);
define_id!(VariableIndex);

pub struct GlobalSymbols{
    len_symbol : SymbolIndex,
}
impl GlobalSymbols{
    pub fn new(interner:&mut SymbolInterner) -> Self{
        Self{ 
            len_symbol: interner.intern("len".to_string())
        }
    }
    pub fn len_symbol(&self) -> SymbolIndex{
        self.len_symbol
    }
}
pub struct SymbolInterner{
    idents : IndexVec<SymbolIndex,String>,
    ident_map : HashMap<String,SymbolIndex>,
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
    pub fn get(&self,ident : SymbolIndex) -> &str{
        &self.idents[ident]
    }   
}
