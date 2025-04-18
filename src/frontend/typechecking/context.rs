use crate::frontend::ast_lowering::hir::{DefKind, Resolution, DefId, DefIdMap, Ident, Path};

use super::types::{generics::GenericArgs, Type};

pub struct FieldDef{
    pub name : Ident,
    pub ty : Type
}
pub struct StructDef{
    pub name : Ident,
    pub fields: Vec<FieldDef>
}
#[derive(Clone,Debug)]
pub struct FuncSig{
    pub params : Vec<Type>,
    pub return_type : Type
}

impl FuncSig{
    pub fn as_type(&self) -> Type{
        Type::new_function(self.params.clone(), self.return_type.clone())
    }
}


pub struct Generics{
    pub owner_id : DefId,
    pub param_names : Vec<Ident>,
}
pub struct FunctionDef{
    pub name : Ident,
    pub sig : FuncSig
}
pub struct TypeContext{
    pub(super) structs : DefIdMap<StructDef>,
    pub(super) functions : DefIdMap<FunctionDef>,
    pub(super) variant_map : DefIdMap<DefId>,
    pub(super) generics_map : DefIdMap<Generics>,
    pub(super) params_to_indexes : DefIdMap<u32>,
    pub(super) child_to_owner_map : DefIdMap<DefId>,
    pub(super) name_map : DefIdMap<Ident>
}
impl TypeContext{
    pub fn new() -> Self{
        Self { structs: DefIdMap::new(), 
            functions : DefIdMap::new(), 
            variant_map : DefIdMap::new(),
            name_map : DefIdMap::new(),
            generics_map:DefIdMap::new(),
            params_to_indexes : DefIdMap::new(),
            child_to_owner_map : DefIdMap::new()
        }
    }
    pub fn ident(&self,id:DefId) -> Ident{
        self.name_map[id]
    }
    pub fn expect_index_for(&self,param_def_id:DefId) -> u32{
        self.params_to_indexes[param_def_id]
    }
    pub fn expect_owner_of(&self,child:DefId) -> DefId{
        self.child_to_owner_map.get(child).copied().expect("There should be an owner for this child")
    }
    pub fn expect_generics_for(&self,owner_id:DefId) -> &Generics{
        self.generics_map.get(owner_id).expect("There should be some generics here")
    
    }
    
}