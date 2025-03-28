use indexmap::IndexMap;

use super::types::Type;

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
        (Type::Function(generic_args, params, return_type ),Type::Function (other_generic_args, other_params, other_return_type)) 
        if params.len() == other_params.len() && generic_args.len() == other_generic_args.len() => {
            generic_args.iter().zip(other_generic_args.iter()).try_for_each(|(arg,other)| infer_types(lookup, &arg.ty, &other.ty))?;
            params.iter().zip(other_params).try_for_each(|(param,other_param)| infer_types(lookup, param, other_param))?;
            infer_types(lookup, return_type, other_return_type)
        },
        (Type::Struct(generic_args, index),Type::Struct(other_generic_args,other_index))  if index == other_index => {
            generic_args.iter().zip(other_generic_args.iter()).try_for_each(|(arg,other)| infer_types(lookup, &arg.ty, &other.ty))
        },
        (Type::Enum(generic_args, index),Type::Enum (other_generic_args, other_index)) if index == other_index => {
            generic_args.iter().zip(other_generic_args.iter()).try_for_each(|(arg,other)| infer_types(lookup, &arg.ty, &other.ty))
        },
        (_,_) => { Ok(())}
    }
}