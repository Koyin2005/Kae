use crate::{frontend::{ast_lowering::hir, typechecking::{context::TypeContext, error::TypeError}}, SymbolInterner};

use super::{generics::GenericArgs, AdtKind, Type};

pub struct TypeLower<'a>{
    interner:&'a SymbolInterner,
    context:&'a TypeContext
}
impl<'a> TypeLower<'a>{
    pub fn new(interner:&'a SymbolInterner,context:&'a TypeContext)->Self{
        Self { 
            interner,
            context
        }
    }
    pub fn lower(&self,ty:&hir::Type) -> Type{
        match &ty.kind{
            hir::TypeKind::Array(element) => Type::new_array(self.lower(element)),
            hir::TypeKind::Function(params, return_type) => 
                Type::new_function(params.iter().map(|param| self.lower(param)).collect(), return_type.as_ref().map_or(Type::new_unit(), |ty| self.lower(ty))),
            hir::TypeKind::Tuple(elements) => Type::new_tuple(elements.into_iter().map(|element| self.lower(element)).collect()),
            hir::TypeKind::Path(path) => {
                match path.final_res{
                    hir::Resolution::Primitive(ty) => {
                        match ty{
                            hir::PrimitiveType::Int => Type::Int,
                            hir::PrimitiveType::Bool => Type::Bool,
                            hir::PrimitiveType::Float => Type::Float,
                            hir::PrimitiveType::Never => Type::Never,
                            hir::PrimitiveType::String => Type::String
                        }
                    },
                    hir::Resolution::Definition(hir::DefKind::Enum,id) => Type::Adt(GenericArgs::new_empty(), id,AdtKind::Enum),
                    hir::Resolution::Definition(hir::DefKind::Struct,id) => Type::Adt(GenericArgs::new_empty(), id,AdtKind::Struct),
                    hir::Resolution::Definition(hir::DefKind::Param, id) => {
                        let generics = self.context.expect_generics_for(self.context.expect_owner_of(id));
                        let index = self.context.expect_index_for(id);
                        let symbol = generics.param_names[index as usize].index;
                        Type::Param(index, symbol)
                    }
                    _ => {
                        TypeError.emit(format!("Cannot use '{}' as type.",path.format(self.interner)), path.span);
                        Type::new_error()
                    }
                }
            }
        }
    }
    
}