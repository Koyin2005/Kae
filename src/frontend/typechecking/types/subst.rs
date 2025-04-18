use crate::frontend::typechecking::context::FuncSig;

use super::{generics::GenericArgs, Type};

pub struct TypeSubst<'a>{
    subst : &'a GenericArgs
}
impl<'a> TypeSubst<'a>{
    pub fn new(subst:&'a GenericArgs ) -> Self{
        Self { subst }
    }

    pub fn instantiate_type(&self,ty:&Type) -> Type{
        match ty{
            &Type::Param(index,_) => {
                self.subst.get(index as usize).clone()
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