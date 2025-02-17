use indexmap::IndexMap;

use super::types::{GenericParamType, Type};

pub struct InferenceFailed;

pub fn infer_types(lookup:&mut IndexMap<Type,Option<Type>>,expected : & Type, ty : & Type)->Result<(),InferenceFailed>{
    match (expected,ty) {
        (param @ Type::Param(_),ty) => {
            if let Some(Some(old_ty)) = lookup.insert(param.clone(), Some(ty.clone())) {
                if &old_ty != ty{
                    return Err(InferenceFailed);
                }
            }
            Ok(())
        },
        (Type::Array(element),Type::Array(other)) => {
            infer_types(lookup, element, other)
        },
        (Type::Tuple(elements),Type::Tuple(other_elements)) if elements.len() == other_elements.len() => {
            elements.iter().zip(other_elements.iter()).try_for_each(|(expected,other)| infer_types(lookup, expected, other))
        },
        (Type::Function { generic_args, params, return_type },Type::Function { generic_args:other_generic_args, params:other_params, return_type:other_return_type }) 
        if params.len() == other_params.len() && generic_args.len() == other_generic_args.len() => {
            generic_args.iter().zip(other_generic_args).try_for_each(|(arg,other)| infer_types(lookup, arg, other))?;
            params.iter().zip(other_params).try_for_each(|(param,other_param)| infer_types(lookup, param, other_param))?;
            infer_types(lookup, return_type, other_return_type)
        },
        (Type::Struct { generic_args, id, .. },Type::Struct { generic_args:other_generic_args, id:other_id, .. })  if id == other_id => {
            generic_args.iter().zip(other_generic_args).try_for_each(|(arg,other)| infer_types(lookup, arg, other))
        },
        (Type::Enum { generic_args, id, .. },Type::Enum { generic_args:other_generic_args, id:other_id, .. }) if id == other_id => {
            generic_args.iter().zip(other_generic_args).try_for_each(|(arg,other)| infer_types(lookup, arg, other))
        },
        (Type::EnumVariant { generic_args, id, variant_index,.. },Type::EnumVariant { generic_args:other_generic_args, id:other_id, variant_index:other_variant_index,.. }) 
        if id == other_id && variant_index == other_variant_index => {
            generic_args.iter().zip(other_generic_args).try_for_each(|(arg,other)| infer_types(lookup, arg, other))
        },
        (_,_) => { Ok(())}
    }
}
pub fn substitute(ty:Type,generic_args:&[Type])->Type{
    match ty.clone(){
        ty @ Type::Param(GenericParamType{index,..}) => generic_args.get(index.0 as usize).cloned().unwrap_or(ty),
        Type::Array(element_type) => Type::Array(Box::new(substitute(*element_type, generic_args))),
        Type::Function { generic_args:mut func_generic_args, params, return_type } => {
            func_generic_args.iter_mut().for_each(|arg|{
                *arg = substitute(arg.clone(), generic_args)
            });

            let params = params.into_iter().map(|param| substitute(param,generic_args)).collect();
            let return_type = substitute(*return_type,generic_args);
            Type::Function { generic_args: func_generic_args, params, return_type:Box::new(return_type) }
        },
        Type::Tuple(elements) => Type::Tuple(elements.into_iter().map(|ty| substitute(ty, generic_args)).collect()),
        Type::Struct { generic_args:mut struct_generic_args, id, name } => {
            struct_generic_args.iter_mut().for_each(|arg|{
                *arg = substitute(arg.clone(), generic_args)
            });
            Type::Struct { generic_args:struct_generic_args, id, name }
        },
        Type::Enum { generic_args:mut enum_generic_args, id, name } => {
            enum_generic_args.iter_mut().for_each(|arg|{
                *arg = substitute(arg.clone(), generic_args)
            });
            Type::Enum { generic_args: enum_generic_args, id, name }
        },
        Type::EnumVariant { generic_args:mut enum_generic_args, id,variant_index, name } => {
            enum_generic_args.iter_mut().for_each(|arg|{
                *arg = substitute(arg.clone(), generic_args)
            });
            Type::EnumVariant { generic_args: enum_generic_args, id, name ,variant_index}
        },
        _ => ty
    }
}
