use generics::GenericArgs;

use crate::identifiers::{EnumIndex, StructIndex, SymbolIndex};


pub mod lowering;
pub mod generics;
pub mod format;

#[derive(Clone,Debug,PartialEq)]
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
    Enum(GenericArgs,EnumIndex),
    Struct(GenericArgs,StructIndex)
}

impl Type{
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