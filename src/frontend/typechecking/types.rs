use crate::{data_structures::IntoIndex, frontend::ast_lowering::SymbolInterner, identifiers::{EnumIndex, GenericParamIndex, StructIndex, SymbolIndex}};
use super::TypeContext;


#[derive(Debug,Clone,Hash,PartialEq,Eq)]
pub struct GenericParamType{
    pub name : SymbolIndex,
    pub index : GenericParamIndex
}
#[derive(Clone,Debug,Hash,PartialEq,Eq)]
pub enum Type {
    Int,
    Float,
    Bool,
    String,
    Never,
    Array(Box<Type>),
    Tuple(Vec<Type>),
    Function(GenericArgs,Vec<Type>,Box<Type>),
    Param(GenericParamType),
    Struct(GenericArgs,StructIndex),
    Enum(GenericArgs,EnumIndex),
    Unknown,

}
impl Type{
    pub const fn new_unit()->Self{
        Type::Tuple(vec![])
    }
    pub fn is_unit(&self)->bool{
        matches!(self,Type::Tuple(elements) if elements.is_empty())
    }
    pub fn is_unknown(&self)->bool{
        match self{
            Type::Unknown => true,
            Type::Array(element) => element.is_unknown(),
            Type::Tuple(elements) => elements.iter().any(|ty| ty.is_unknown()),
            Type::Function(_, params, return_type) => params.iter().any(|ty| ty.is_unknown()) || return_type.is_unknown(),
            _ => false
        }
    }
    pub fn substitute(&self,generic_args:&GenericArgs) -> Self{
        match self{
            Type::Int | Type::Bool | Type::Unknown | Type::Float | Type::String | Type::Never => self.clone(),
            Type::Array(element) => Type::Array(Box::new(element.substitute(generic_args))),
            Type::Tuple(elements) => Type::Tuple(elements.iter().map(|element| element.substitute(generic_args)).collect()),
            Type::Function(func_generic_args,params,return_type ) => 
                Type::Function(
                    func_generic_args.substitute(generic_args),
                    params.iter().map(|param| param.substitute(generic_args)).collect(), 
                    Box::new(return_type.substitute(generic_args))
                ),
            &Type::Struct(ref struct_generic_args, index) => Type::Struct(struct_generic_args.substitute(generic_args), index),
            &Type::Enum(ref enum_generic_args, index) => Type::Enum(enum_generic_args.substitute(generic_args),index),
            ty @ Type::Param(param) => generic_args.get(param.index).map_or_else(|| ty.clone(), |arg| arg.ty.clone())
            

        }
    }
    pub fn get_generic_args(&self)->Option<GenericArgs>{
        match self{
            Type::Function(generic_args, .. ) |
            Type::Enum(generic_args, ..)|
            Type::Struct(generic_args, ..) => {
                if generic_args.is_empty() { 
                    None
                } 
                else {
                    Some(generic_args.clone())
                }
            },
            _ => None
        }
    }

    pub fn is_closed(&self)->bool{
        match self{
            Type::Array(element_type) => element_type.is_closed(),
            Type::Param(..) => false,
            Type::Tuple(elements) => elements.iter().all(|ty| ty.is_closed()),
            Type::Function(generic_args, params, return_type ) => 
                generic_args.0.iter().all(|arg| arg.ty.is_closed()) && params.iter().all(|param| param.is_closed()) && return_type.is_closed(),
            Type::Struct(generic_args, ..) | 
            Type::Enum(generic_args, .. )  => generic_args.iter().all(|arg| arg.ty.is_closed()),
            _ => true,
        }
    }
    pub fn display_type<'a>(&'a self,ctxt:&'a TypeContext,interner:&'a SymbolInterner) -> String{
        match self{
            Type::Int => "int".to_string(),
            Type::Float => "float".to_string(),
            Type::String => "string".to_string(),
            Type::Bool => "bool".to_string(),
            Type::Never => "never".to_string(),
            Type::Array(element) => format!("[{}]",element.display_type(ctxt, interner)),
            Type::Tuple(elements) => {
                let mut displayed_string = String::with_capacity(2);
                displayed_string.push('(');
                for (i,element) in elements.iter().enumerate(){
                    if i>0{
                        displayed_string.push(',');
                    }
                    displayed_string.push_str(&format!("{}",element.display_type(ctxt, interner)));
                }
                displayed_string
            },
            Type::Function(_,params, return_type) => {
                let mut displayed_string = String::from("fun(");
                for (i,param) in params.iter().enumerate(){
                    if i>0{
                        displayed_string.push(',');
                    }
                    displayed_string.push_str(&format!("{}",param.display_type(ctxt, interner)));
                }
                displayed_string.push_str(&format!(")->{}",return_type.display_type(ctxt, interner)));
                displayed_string
            },
            Type::Param(param_info) => format!("{}",interner.get(param_info.name)),
            Type::Unknown => format!("_"),
            Type::Enum(generic_args,index) => {
                format!("{}{}",interner.get(ctxt.enums[*index].name.index),generic_args.display(ctxt, interner))
            },
            Type::Struct(generic_args, index) => {
                format!("{}{}",interner.get(ctxt.structs[*index].name.index),generic_args.display(ctxt, interner))
            }
        }
    } 
}
pub struct GenericArgIter<'a>(std::slice::Iter<'a,GenericArg>);
impl<'a> Iterator for GenericArgIter<'a>{
    type Item = &'a GenericArg;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

pub struct GenericArgIterMut<'a>(std::slice::IterMut<'a,GenericArg>);
impl<'a> Iterator for GenericArgIterMut<'a>{
    type Item = &'a mut GenericArg;
    fn next(&mut self) -> Option<Self::Item>{
        self.0.next()
    }
}
#[derive(Clone,Debug,Hash,PartialEq,Eq)]
pub struct GenericArgs(Vec<GenericArg>);

#[derive(Clone,Debug,Hash,PartialEq,Eq)]
pub struct GenericArg{
    pub ty : Type
}
impl GenericArgs{
    pub fn new()->Self{
        Self(Vec::new())
    }
    pub fn len(&self)->usize{
        self.0.len()
    }
    fn substitute(&self,other_generic_args:&GenericArgs) -> Self{
        Self(self.0.iter().map(|arg|{
           GenericArg{ty: arg.ty.substitute(other_generic_args)}
        }).collect())
    }
    pub fn is_empty(&self)->bool { self.0.is_empty() }
    pub fn get(&self,index:GenericParamIndex) -> Option<&GenericArg> {
        self.0.get(index.as_index() as usize)
    }
    pub fn iter(&self) -> GenericArgIter<'_>{
        GenericArgIter(self.0.iter())
    }
    pub fn iter_mut(&mut self) -> GenericArgIterMut<'_>{
        GenericArgIterMut(self.0.iter_mut())
    }
    fn display(&self,ctxt:&TypeContext,interner:&SymbolInterner) -> String{
        if !self.is_empty(){
            let mut displayed_string = String::from('[');
            for (i,arg) in self.0.iter().enumerate(){
                if i>0{
                    displayed_string.push(',');
                }
                displayed_string.push_str(&format!("{}",arg.ty.display_type(ctxt, interner)));
            }
            displayed_string.push(']');
            displayed_string
        }
        else{
            String::from("[]")
        }
    }
}
