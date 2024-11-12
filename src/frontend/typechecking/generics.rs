use super::types::{GenericArgs, Type};


pub fn substitute(ty:Type,generic_args:&GenericArgs)->Type{
    match ty{
        Type::Param { name, index } => generic_args.get(&index).cloned().unwrap_or_else(|| Type::Param { name, index }),
        Type::Array(element_type) => Type::Array(Box::new(substitute(*element_type, generic_args))),
        Type::Function { generic_args:func_generic_args, params, return_type } => {
            let func_generic_args = func_generic_args.into_iter().map(|(name,ty)|{
                (name,substitute(ty, generic_args))
            }).collect();

            let params = params.into_iter().map(|param| substitute(substitute(param, &func_generic_args),generic_args)).collect();
            let return_type = substitute(substitute(*return_type, &func_generic_args),generic_args);

            Type::Function { generic_args: func_generic_args, params, return_type:Box::new(return_type) }
        },
        Type::Tuple(elements) => Type::Tuple(elements.into_iter().map(|ty| substitute(ty, generic_args)).collect()),
        Type::Struct { generic_args:struct_generic_args, id, name } => {
            
            let struct_generic_args = struct_generic_args.into_iter().map(|(name,ty)|{
                (name,substitute(ty, generic_args))
            }).collect();
            Type::Struct { generic_args:struct_generic_args, id, name }
        },
        Type::Enum { generic_args:enum_generic_args, id, name } => {
            let enum_generic_args = enum_generic_args.into_iter().map(|(name,ty)|{
                (name,substitute(ty, generic_args))
            }).collect();
            Type::Enum { generic_args: enum_generic_args, id, name }
        },
        Type::EnumVariant { generic_args:enum_generic_args, id,variant_index, name } => {
            let enum_generic_args = enum_generic_args.into_iter().map(|(name,ty)|{
                (name,substitute(ty, generic_args))
            }).collect();
            Type::EnumVariant { generic_args: enum_generic_args, id, name ,variant_index}
        },
        _ => ty
    }
}
