use std::collections::HashMap;

use super::types::Type;


pub fn substitute(ty:Type,generic_args:&[Type])->Type{
    match ty{
        ty @ Type::Param { index,.. } => generic_args.get(index).cloned().unwrap_or_else(|| ty),
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
