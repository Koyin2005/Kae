use crate::{data_structures::IndexVec, frontend::ast_lowering::hir::Ident, identifiers::{FieldIndex, FuncIndex, StructIndex}};

use super::types::Type;

pub struct FieldDef{
    pub name : Ident,
    pub ty : Type
}
pub struct StructDef{
    pub name : Ident,
    pub fields: IndexVec<FieldIndex,FieldDef>
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

pub struct FunctionDef{
    pub name : Ident,
    pub generics : Vec<Ident>,
    pub sig : FuncSig
}
pub struct TypeContext{
    pub(super) structs : IndexVec<StructIndex,StructDef>,
    pub(super) functions : IndexVec<FuncIndex,FunctionDef>
}
impl TypeContext{
    pub fn new() -> Self{
        Self { structs: IndexVec::new(), functions : IndexVec::new()}
    }
    pub fn expect_struct(&self,index:StructIndex) -> &StructDef{
        self.structs.get(index).expect("There should be a struct at this index")
    }

    pub fn expect_function(&self,index:FuncIndex) -> &FunctionDef{
        self.functions.get(index).expect("There should be a function sig at this index")
    }
}