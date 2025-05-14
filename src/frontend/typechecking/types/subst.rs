use fxhash::FxHashMap;

use crate::frontend::{ast_lowering::hir::DefId, typechecking::context::FuncSig};

use super::{generics::GenericArgs, Type};
#[derive(Clone)]
pub struct TypeSubst<'a>{
    subst : FxHashMap<u32,&'a Type>,
}

impl<'a> TypeSubst<'a>{
    pub fn empty() -> Self{
        Self { subst: FxHashMap::default() }
    }
    pub fn new_with_base(generic_args:&'a GenericArgs,base:u32) -> Self{
        Self { subst: generic_args.iter().enumerate().map(|(i,ty)|{
            (i as u32 + base,ty)
        }).collect() }
    }
    pub fn new_from(subst:FxHashMap<u32,&'a Type>) -> Self{
        Self { subst }
    }
    pub fn new(generic_args:&'a GenericArgs) -> Self{
        Self { subst :generic_args.iter().enumerate().map(|(i,ty)|{
            (i as u32,ty)
        }).collect()}
    }
}

impl<'a> Subst for TypeSubst<'a>{
    
    fn instantiate_type(&self,ty:&Type) -> Type{
        match ty{
            &Type::Param(index,_) => {
                if let Some(&&ty) = self.subst.get(&index).as_ref(){
                    ty.clone()
                }   
                else{
                    ty.clone()
                }
            },
            _ => self.super_instantiate_type(ty)

        }
    }
}
pub trait Subst : Sized{
    fn instantiate_type(&self,ty:&Type) -> Type;
    fn instantiate_types<'b,I:Iterator<Item = &'b Type>>(&self,types:I) -> Vec<Type>{
        types.map(|ty| self.instantiate_type(ty)).collect()
    }
    fn instantiate_signature(&self,sig:&FuncSig) -> FuncSig{
        FuncSig { params: self.instantiate_types(sig.params.iter()), return_type: self.instantiate_type(&sig.return_type) }
    }
    fn super_instantiate_type(&self,ty:&Type) -> Type{
        match ty{
            &Type::Param(index,name) => { Type::Param(index,name) },
            Type::Function(params,return_type) => Type::new_function(self.instantiate_types(params.iter()), self.instantiate_type(return_type)),
            Type::Array(element_type) => Type::new_array(self.instantiate_type(element_type)),
            &Type::Adt(ref generic_args,id,kind) => Type::Adt(GenericArgs::new(self.instantiate_types(generic_args.iter())), id, kind),
            Type::Tuple(elements) => Type::new_tuple(self.instantiate_types(elements.iter())),
            Type::Int => Type::Int,
            Type::Bool => Type::Bool,
            Type::Never => Type::Never,
            Type::String => Type::String,
            Type::Float => Type::Float,
            Type::Error => Type::Error,
            &Type::SelfAlias(id) => Type::SelfAlias(id)

        }
    }
    fn chain<U:Subst>(self,next:U) -> ChainedSubst<Self,U>{
        ChainedSubst { first: self, second: next }
    } 
}

pub struct SelfTypeSubst<'a>{
    pub ty : &'a Type,
    pub id : DefId
}
impl<'a,T:Subst> Subst for &'a T{
    fn instantiate_type(&self,ty:&Type) -> Type {
        (*self).instantiate_type(ty)
    }
}
impl<'a> Subst for SelfTypeSubst<'a>{
    fn instantiate_type(&self,ty:&Type) -> Type {
        match ty{
            &Type::SelfAlias(id) if id == self.id => self.ty.clone(),
            _ => self.super_instantiate_type(ty)
        }
    }
}
pub struct ChainedSubst<Subst1,Subst2>{
    pub first : Subst1,
    pub second : Subst2
}
impl<T:Subst,U:Subst> Subst for ChainedSubst<T,U>{
    fn instantiate_type(&self,ty:&Type) -> Type {
        self.second.instantiate_type(&self.first.instantiate_type(ty))
    }
}