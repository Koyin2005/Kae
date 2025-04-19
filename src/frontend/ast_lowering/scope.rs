use fxhash::FxHashMap;

use crate::identifiers::SymbolIndex;

use super::hir::Resolution;

#[derive(Debug,Clone,Copy,PartialEq, Eq)]
pub enum ScopeKind {
    Normal,
    Function,
    Type
}
#[derive(Debug)]
pub struct Scope{
    bindings : FxHashMap<SymbolIndex,Resolution>,
    kind : ScopeKind
}

impl Scope{
    pub fn new(kind : ScopeKind) -> Self{
        Self { bindings: FxHashMap::default(),kind}
    }
    pub fn kind(&self) -> ScopeKind{
        self.kind
    }
    pub fn add_binding(&mut self,id:SymbolIndex,res:Resolution)->Option<Resolution>{
        self.bindings.insert(id, res)
    }

    pub fn get_binding(&self,id:SymbolIndex)->Option<Resolution>{
        self.bindings.get(&id).copied()
    }
}

#[derive(Debug)]
pub struct NameSpaces{
    names_to_scopes : FxHashMap<Resolution,Scope>,
}
impl NameSpaces{
    pub fn new() -> Self{
        Self { names_to_scopes: FxHashMap::default() }
    }
    pub fn define_namespace(&mut self,name:Resolution,scope:Scope){
        self.names_to_scopes.insert(name, scope);
    }
    pub fn get_namespace(&self,name:Resolution) -> Option<&Scope>{
        self.names_to_scopes.get(&name)
    }
    pub fn expect_namespace(&self,name:Resolution) -> &Scope{
        self.get_namespace(name).expect(&format!("There should be a namespace for '{:?}'",name))
    }
}
