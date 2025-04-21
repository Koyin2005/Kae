use fxhash::FxBuildHasher;
use indexmap::IndexMap;

use crate::{frontend::{ast_lowering::hir::{DefId, DefIdMap, Ident}, tokenizing::SourceLocation}, identifiers::SymbolIndex};

use super::types::Type;

pub struct FieldDef{
    pub name : Ident,
    pub ty : Type
}
pub struct StructDef{
    pub name : Ident,
    pub fields: Vec<FieldDef>
}
pub struct VariantDef{
    pub id : DefId,
    pub name : Ident,
    pub fields : Vec<FieldDef>,
}
pub struct EnumDef{
    pub name : Ident,
    pub variants : Vec<VariantDef>
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
pub struct MethodDef{
    pub name : Ident,
    pub has_receiver : bool,
    pub sig : FuncSig
}
pub struct Impl{
    pub span : SourceLocation,
    pub ty : Type,
    pub methods : Vec<DefId>
}
pub struct TypeContext{
    pub(super) structs : DefIdMap<StructDef>,
    pub(super) enums : DefIdMap<EnumDef>,
    pub(super) functions : DefIdMap<FunctionDef>,
    pub(super) generics_map : DefIdMap<Generics>,
    pub(super) params_to_indexes : DefIdMap<u32>,
    pub(super) methods : DefIdMap<MethodDef>,
    pub(super) child_to_owner_map : DefIdMap<DefId>,
    pub(super) impls : DefIdMap<Impl>,
    pub(super) name_map : DefIdMap<Ident>,
    pub(super) ty_impl_map : IndexMap<Type,Vec<DefId>,FxBuildHasher>,
}
impl TypeContext{
    pub fn new() -> Self{
        Self { 
            structs: DefIdMap::new(), 
            functions : DefIdMap::new(), 
            name_map : DefIdMap::new(),
            generics_map:DefIdMap::new(),
            methods: DefIdMap::new(),
            enums: DefIdMap::new(),
            params_to_indexes : DefIdMap::new(),
            child_to_owner_map : DefIdMap::new(),
            impls : DefIdMap::new(),
            ty_impl_map : IndexMap::default()
        }
    }
    pub fn get_methods(&self,ty:&Type,method_name:SymbolIndex) -> Vec<(DefId,&MethodDef)>{
        let mut valid_methods = Vec::new();
        if let Some(impls) =  self.ty_impl_map.get(ty){
            for impl_ in impls.iter().map(|&impl_| &self.impls[impl_]){
                valid_methods.extend(impl_.methods.iter().filter_map(|&method|{
                    let method_def = &self.methods[method];
                    (method_def.name.index == method_name).then_some((method,method_def))
                }));
            }
        }
        
        valid_methods
    }
    pub fn ident(&self,id:DefId) -> Ident{
        self.name_map.get(id).copied().expect(&format!("There should be an ident for this id {:?}",id))
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