use fxhash::FxHashMap;

use crate::frontend::typechecking::context::FuncSig;

use super::{generics::GenericArgs, Type};
#[derive(Clone)]
pub struct TypeSubst<'a>{
    subst : FxHashMap<u32,&'a Type>
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

    pub fn instantiate_type(&self,ty:&Type) -> Type{
        match ty{
            &Type::Param(index,_) => {
                if let Some(&&ty) = self.subst.get(&index).as_ref(){
                    ty.clone()
                }   
                else{
                    ty.clone()
                }
            },
            Type::Function(params,return_type) => Type::new_function(params.iter().map(|param| self.instantiate_type(param)).collect(), self.instantiate_type(return_type)),
            Type::Array(element_type) => Type::new_array(self.instantiate_type(element_type)),
            &Type::Adt(ref generic_args,id,kind) => Type::Adt(GenericArgs::new(generic_args.iter().map(|arg| self.instantiate_type(arg)).collect()), id, kind),
            Type::Tuple(elements) => Type::new_tuple(elements.iter().map(|element| self.instantiate_type(element)).collect()),
            Type::Int => Type::Int,
            Type::Bool => Type::Bool,
            Type::Never => Type::Never,
            Type::String => Type::String,
            Type::Float => Type::Float,
            Type::Error => Type::Error

        }
    }
    pub fn instantiate_signature(&self,sig:&FuncSig) -> FuncSig{
        FuncSig { params: sig.params.iter().map(|param|{ self.instantiate_type(param)}).collect(), return_type: self.instantiate_type(&sig.return_type) }
    }
}
