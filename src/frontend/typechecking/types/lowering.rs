use crate::{frontend::{ast_lowering::hir::{self, DefKind, GenericArg, Path, Resolution}, typechecking::{context::TypeContext, error::TypeError}}, SymbolInterner};

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
    pub fn lower_generic_args(&self,generic_args:&[GenericArg]) -> GenericArgs{
        GenericArgs::new(generic_args.iter().map(|arg|{
            self.lower_type(&arg.ty)
        }).collect())
    }
    pub fn get_generic_args(&self,path:&Path) -> Option<GenericArgs>{
        let generic_args = match path.final_res{
            Resolution::Definition(DefKind::Function, id) => {
                let segment = path.segments.iter().rev().find(|segment|{
                    matches!(segment.res,Resolution::Definition(DefKind::Function, seg_id) if seg_id == id)
                })?;
                &segment.args
            },
            Resolution::Definition(DefKind::Struct,id) => {
                let segment = path.segments.iter().rev().find(|segment|{
                    matches!(segment.res,Resolution::Definition(DefKind::Struct, seg_id) if seg_id == id)
                })?;
                &segment.args
            },
            Resolution::Definition(DefKind::Enum, id) => {
                let segment = path.segments.iter().rev().find(|segment|{
                    matches!(segment.res,Resolution::Definition(DefKind::Enum, seg_id) if seg_id == id)
                })?;
                &segment.args
            },
            Resolution::Definition(DefKind::Variant,id) => {
                let segment = path.segments.iter().rev().find(|segment|{
                    matches!(segment.res,Resolution::Definition(DefKind::Enum, seg_id) if seg_id == self.context.expect_owner_of(id))
                })?;
                &segment.args
            },
            Resolution::Primitive(_) | Resolution::Variable(_) | Resolution::Definition(DefKind::Param, _) => return Some(GenericArgs::new_empty())
        };
        Some(self.lower_generic_args(generic_args))
    }
    pub fn lower_type(&self,ty:&hir::Type) -> Type{
        match &ty.kind{
            hir::TypeKind::Array(element) => Type::new_array(self.lower_type(element)),
            hir::TypeKind::Function(params, return_type) => 
                Type::new_function(params.iter().map(|param| self.lower_type(param)).collect(), return_type.as_ref().map_or(Type::new_unit(), |ty| self.lower_type(ty))),
            hir::TypeKind::Tuple(elements) => Type::new_tuple(elements.into_iter().map(|element| self.lower_type(element)).collect()),
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
                    hir::Resolution::Definition(hir::DefKind::Enum,id) => Type::Adt(self.get_generic_args(path).expect("Should defo have generic args"), id,AdtKind::Enum),
                    hir::Resolution::Definition(hir::DefKind::Struct,id) => Type::Adt(self.get_generic_args(path).expect("Should defo have generic args"), id,AdtKind::Struct),
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