use std::collections::VecDeque;

use fxhash::FxHashMap;
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
#[derive(Clone,Debug,Eq,Hash)]
pub enum Type {
    Int,
    Float,
    Bool,
    String,
    Never,
    Error,
    SelfAlias(DefId),
    Param(u32,SymbolIndex),
    Function(Vec<Type>,Box<Type>),
    Array(Box<Type>),
    Tuple(Vec<Type>),
    Adt(GenericArgs,DefId,AdtKind),
}
impl PartialEq for Type{
    fn eq(&self, other: &Self) -> bool {
        match (self,other){
            (Self::Int,Self::Int) => true,
            (Self::Float,Self::Float) => true,
            (Self::String,Self::String) => true,
            (Self::Never,Self::Never) => true,
            (Self::Error,Self::Error) => true,
            (Self::Bool,Self::Bool) => true,
            (Self::Param(index,_),Self::Param(other_index,_)) => index == other_index,
            (Self::Function(params,return_ty),Self::Function(other_params,other_return_ty)) if params.len() == other_params.len() => {
                params == other_params && return_ty == other_return_ty
            },
            (Self::Tuple(elements),Self::Tuple(other_elements)) if elements.len() == other_elements.len() => {
                elements == other_elements
            },
            (Self::Adt(generic_args,id,kind),Self::Adt(other_generic_args,other_id,other_kind)) if generic_args.len() == other_generic_args.len() && id == other_id && kind ==  other_kind => {
                generic_args == other_generic_args
            },
            (Self::Array(element),Self::Array(other_element)) => element == other_element,
            (Self::SelfAlias(id),Self::SelfAlias(other)) => id == other,
            _ => false
        }
    }
}
impl Type{
    pub fn iter(&self) -> TypeIterator{
        TypeIterator { ty: VecDeque::from([self]) }
    }
    ///Finds a substitution from self to other
    pub fn get_substitution<'a>(&'a self,other:&'a Self) -> Option<FxHashMap<u32,&'a Self>>{
        match(self,other){
            (&Self::Param(index,_),ty) | (ty,&Self::Param(index,_)) => {
                Some(vec![(index,ty)].into_iter().collect())
            },
            (Self::Function(params,return_type),Self::Function(other_params,other_return_type)) => {
                if params.len() != other_params.len() { return None};
                let mut subst = FxHashMap::default();
                for (ty,other) in params.iter().zip(other_params.iter()){
                    subst.extend(ty.get_substitution(other)?);
                }
                subst.extend(return_type.get_substitution(other_return_type)?);
                Some(subst)
            },
            (Self::Adt(generic_args,id,kind),Self::Adt(other_generic_args,other_id,other_kind)) => {
                if id != other_id || kind != other_kind || generic_args.len() != other_generic_args.len(){
                    return None;
                }
                let mut subst = FxHashMap::default();
                for (arg,other_arg) in generic_args.iter().zip(other_generic_args.iter()){
                    subst.extend(arg.get_substitution(other_arg)?);
                }
                Some(subst)
            },
            (Self::Tuple(fields),Self::Tuple(other_fields)) => {
                if fields.len() != other_fields.len() { return None;}
                let mut subst = FxHashMap::default();
                for (field,other_field) in fields.iter().zip(other_fields.iter()){
                    subst.extend(field.get_substitution(other_field)?);
                }
                Some(subst)
            },
            (ty,other_ty) => if ty == other_ty {
                Some(FxHashMap::default())
            } else {
                None
            }
        }
    }
    pub fn get_generic_args(&self) -> Option<&GenericArgs>{
        match self{
            Self::Adt(args,_,_) => Some(args),
            _ => None
        }
    }
    pub fn as_adt(&self) -> Option<(&GenericArgs,DefId,AdtKind)>{
        match self{
            &Self::Adt(ref generic_args,id,kind) => Some((generic_args,id,kind)),
            _ => None
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
    pub fn new_self_alias(trait_ : DefId) -> Self{
        Self::SelfAlias(trait_)
    }
    pub fn new_error() -> Self{
        Type::Error
    }
    pub fn is_error(&self) -> bool{
        matches!(&self,Type::Error) 
    }
    pub fn has_error(&self) -> bool{
        self.iter().any(|ty| ty.is_error())
    }
    pub fn is_never(&self) -> bool{
        matches!(&self,Type::Never)
    }
    pub fn is_unit(&self) -> bool{
        matches!(&self,Type::Tuple(elements) if elements.is_empty())
    }
}

pub struct TypeIterator<'a>{
    ty : VecDeque<&'a Type>,
}

impl<'a> Iterator for TypeIterator<'a>{
    type Item = &'a Type;
    fn next(&mut self) -> Option<Self::Item> {
        match self.ty.pop_front(){
            Some(ty) => {
                match ty{
                    Type::Function(params,return_type) => {
                        self.ty.extend(params);
                        self.ty.push_back(return_type);
                    },
                    Type::Adt(generic_args,_,_) => {
                        self.ty.extend(generic_args.iter());
                    },
                    Type::Tuple(elements) => {
                        self.ty.extend(elements);
                    },
                    Type::Array(ty) => {
                        self.ty.push_back(ty);
                    },
                    _ => {}
                }
                Some(ty)
            },
            None => {
                None
            }
        }
    }
}

#[cfg(test)]
mod tests{
    use super::Type;

    #[test]
    fn test_func(){
        let ty = Type::Tuple(vec![
            Type::Int,
            Type::Function(Vec::new(), Box::new(Type::Bool))
        ]);
        let mut iter = ty.iter();
        assert_eq!(iter.next(),Some(&Type::Tuple(vec![
            Type::Int,
            Type::Function(Vec::new(), Box::new(Type::Bool))
        ])));
        assert_eq!(iter.next(),Some(&Type::Int));
        assert_eq!(iter.next(),Some(&Type::Function(Vec::new(), Box::new(Type::Bool))));
        assert_eq!(iter.next(),Some(&Type::Bool));
    }
}