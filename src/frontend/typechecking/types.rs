use std::fmt::Display;

use indexmap::IndexMap;

use super::{generics::substitute, names::{Environment, StructId, Structs}};

#[derive(Clone, Copy,PartialEq, Eq,Debug)]
pub struct FunctionId(usize);

impl FunctionId{
    pub const DEFAULT : Self = FunctionId(0);

    pub fn next(&self)->Self{
        Self(self.0+1)
    }
}

impl Default for FunctionId{
    fn default() -> Self {
        Self::DEFAULT
    }
}

pub type GenericArgs = IndexMap<String,Type>;

#[derive(Clone,PartialEq,Debug)]
pub enum Type {
    Int,
    Float,
    Bool,
    String,
    Never,
    Unit,
    Array(Box<Type>),
    Tuple(Vec<Type>),
    Function{
        generic_args : GenericArgs,
        params : Vec<Type>, 
        return_type : Box<Type>
    },
    Param{
        name : String,
        index : usize,
    },
    Struct{
        generic_args :  GenericArgs,
        id : StructId,
        name : String,
    },
    Unknown,

}
impl Type{
    pub fn get_field(&self,field_name:&str,structs:&Structs)->Option<Type>{
        match (self,field_name){
            (Type::Array(..),"length") => Some(Type::Int),
            (Type::Struct { generic_args, id, .. },field_name) => {
                structs.get_struct_info(id)
                    .and_then(|struct_| struct_.get_field(&field_name)
                    .map(|(_,ty)| {
                        let ty = ty.clone();
                        if !generic_args.is_empty() { substitute(ty, generic_args)} else { ty }
                }))
            }
            _ => None
        }
    }
    pub fn is_unknown(&self)->bool{
        match self{
            Type::Unknown => true,
            Type::Array(element) => element.is_unknown(),
            Type::Tuple(elements) => elements.iter().any(|ty| ty.is_unknown()),
            Type::Function { params, return_type,.. } => params.iter().any(|ty| ty.is_unknown()) || return_type.is_unknown(),
            _ => false
        }
    }

    pub fn get_generic_args(&self)->Option<GenericArgs>{
        match self{
            Type::Function { generic_args, .. } => {
                if generic_args.is_empty() { None} else {
                    Some(generic_args.clone())
                }
            },
            _ => None
        }
    }

    pub fn is_closed(&self)->bool{
        match self{
            Type::Array(element_type) => element_type.is_closed(),
            Type::Param{..} => false,
            Type::Tuple(elements) => elements.iter().all(|ty| ty.is_closed()),
            Type::Function { generic_args, params, return_type } => 
                generic_args.values().all(|ty| ty.is_closed()) && params.iter().all(|param| param.is_closed()) && return_type.is_closed(),
            _ => true,
        }
    }

}
impl Display for Type{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self{
            Type::Int => write!(f,"int"),
            Type::Float => write!(f,"float"),
            Type::String => write!(f,"string"),
            Type::Bool => write!(f,"bool"),
            Type::Never => write!(f,"never"),
            Type::Unit => write!(f,"()"),
            Type::Array(element) => write!(f,"[{}]",element),
            Type::Tuple(elements) => {
                write!(f,"(")?;
                for (i,ty) in elements.iter().enumerate(){
                    if i>0{
                        write!(f,",")?;
                    }
                    write!(f,"{}",ty)?;
                }
                write!(f,")")
            },
            Type::Function { params, return_type,.. } => {
                write!(f,"(")?;
                for (i,param) in params.iter().enumerate(){
                    if i>0{
                        write!(f,",")?;
                    }
                    write!(f,"{}",param)?;
                }
                write!(f,")->{}",return_type)
            },
            Type::Param { name ,..} => write!(f,"{}",name),
            Type::Unknown => write!(f,"_"),
            Type::Struct { generic_args, name,.. } => {
                write!(f,"{}",name)?;
                if !generic_args.is_empty(){
                    write!(f,"[")?;
                    for (i,arg) in generic_args.values().enumerate(){
                        if i>0{
                            write!(f,",")?;
                        }
                        write!(f,"{}",arg)?;
                    }
                    write!(f,"]")
                }
                else{
                    Ok(())
                }
            }
        }
    }
}