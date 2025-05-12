use super::types::{generics::GenericArgs, Type};

pub mod check;
pub mod env;
mod ops;


#[derive(Clone,Debug)]
pub(super) enum Expectation{
    HasType(Type),
    CoercesTo(Type),
    None
}
#[derive(Debug)]
pub enum InferError{
    TypesNotEqual(Type,Type),

}
#[derive(Debug)]
pub struct TypeInfer(Vec<Option<Type>>,u32);

impl TypeInfer{
    pub fn new(count:usize,base:u32) -> Self{
        Self(vec![None;count],base)
    }
    pub fn complete(self) -> bool{
        self.0.iter().all(|ty| ty.as_ref().is_some_and(|ty| ty.is_closed()))
    }
    pub fn get_subst(&self,ty1:&Type) -> Option<Type>{
        match ty1{
            &Type::Param(index,_) => {
                self.0.get((index - self.1) as usize).cloned().flatten()
            },
            Type::Tuple(elements) => {
                Some(Type::Tuple(elements.iter().map(|element| self.get_subst(element)).collect::<Option<Vec<_>>>()?))
            },
            Type::Array(element_type) => self.get_subst(element_type).map(|element_type| Type::new_array(element_type)),
            Type::Function(params, return_type) => {
                params.into_iter().map(|param| self.get_subst(param)).collect::<Option<Vec<_>>>().and_then(|params|{
                    self.get_subst(return_type).map(|return_type|{
                        Type::new_function(params, return_type)
                    })
                })
            },
            &Type::Adt(ref generic_args,id,kind) => {
                Some(Type::Adt(GenericArgs::new(generic_args.iter().map(|ty|self.get_subst(ty)).collect::<Option<Vec<_>>>()?), id, kind))
            }
            ty => if ty.is_closed() {Some(ty.clone())} else {None}
        }
    }
    pub fn infer(&mut self,expected:&Type,ty:&Type) -> Result<(),InferError>{
        match (expected,ty){
            (&Type::Param(index, _),ty2) => {
                if index<self.1{
                    return Ok(());
                }
                let stored_ty = &mut self.0[(index - self.1) as usize];
                if let Some(old_ty) = stored_ty{
                    if old_ty != ty2{
                        return Err(InferError::TypesNotEqual(old_ty.clone(), ty2.clone()));
                    }
                    else{
                        return Ok(());
                    }
                }
                *stored_ty = Some(ty2.clone());
                Ok(())
            },
            (Type::Tuple(elements1),Type::Tuple(elements2)) if elements1.len() == elements2.len() => {
                elements1.iter().zip(elements2.iter()).try_for_each(|(element1,element2)|{
                    self.infer(element1,element2)
                })
            },
            (Type::Function(params1,return_type1),Type::Function(params2,return_type2)) if params1.len() == params2.len() => {
                params1.iter().zip(params2.iter()).try_for_each(|(param1,param2)|{
                    self.infer(param1,param2)
                })?;
                self.infer(&return_type1, &return_type2)
            },
            (Type::Array(element_type),Type::Array(element_type2))  => {
                self.infer(&element_type, &element_type2)
            },
            (Type::Adt(generic_args,_,_),Type::Adt(other_generic_args,_,_)) => {
                for (arg,other) in generic_args.iter().zip(other_generic_args.iter()){
                    self.infer(arg, other)?;
                }
                Ok(())
            }
            _ => {
                Ok(())
            }
        }
    }

}