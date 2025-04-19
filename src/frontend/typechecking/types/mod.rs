use generics::GenericArgs;

use crate::{frontend::ast_lowering::hir::DefId, identifiers::SymbolIndex};


pub mod lowering;
pub mod generics;
pub mod format;
pub mod subst;
pub mod collect;
#[derive(Clone,Copy,Debug,PartialEq,Eq,Hash)]
pub enum AdtKind {
    Struct,
    Enum
}
#[derive(Clone,Debug,PartialEq,Eq,Hash)]
pub enum Type {
    Int,
    Float,
    Bool,
    String,
    Never,
    Error,
    Param(u32,SymbolIndex),
    Function(Vec<Type>,Box<Type>),
    Array(Box<Type>),
    Tuple(Vec<Type>),
    Adt(GenericArgs,DefId,AdtKind),
}

impl Type{
    pub fn is_closed(&self) -> bool{
        match self{
            Type::Int | Type::Bool | Type::String | Type::Never | Type::Error | Type::Float => true,
            Type::Array(elements) => elements.is_closed(),
            Type::Function(params, return_ty) => return_ty.is_closed() && params.iter().all(|param| param.is_closed()),
            Type::Adt(args, _,_) => args.iter().all(|param| param.is_closed()),
            Type::Tuple(elements) => elements.iter().all(|element| element.is_closed()),
            Type::Param(_,_) => false
        }
    }
    pub fn new_struct(args:GenericArgs,id:DefId) -> Self{
        Self::Adt(args, id, AdtKind::Struct)
    }
    pub fn new_enum(args:GenericArgs,id:DefId) -> Self{
        Self::Adt(args, id, AdtKind::Enum)
    }
    pub fn new_unit() -> Self{
        Self::Tuple(vec![])
    }
    pub fn new_function(params : Vec<Self>, return_type : Self) -> Self{
        Self::Function(params, Box::new(return_type))
    } 
    pub fn new_tuple(elements : Vec<Self>) -> Self{
        Self::Tuple(elements)
    }
    pub fn new_array(element : Self) -> Self{
        Self::Array(Box::new(element))
    }
    pub fn new_error() -> Self{
        Type::Error
    }
    pub fn is_error(&self) -> bool{
        matches!(&self,Type::Error)
    }
    pub fn is_never(&self) -> bool{
        matches!(&self,Type::Never)
    }
    pub fn is_unit(&self) -> bool{
        matches!(&self,Type::Tuple(elements) if elements.is_empty())
    }
}