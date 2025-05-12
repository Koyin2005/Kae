use crate::{frontend::{ast_lowering::hir::{self, DefKind, GenericArg, QualifiedPath, Resolution}, typechecking::{context::TypeContext, error::TypeError}}, SymbolInterner};

use super::{format::TypeFormatter, generics::GenericArgs, AdtKind, Type};

pub struct TypeLower<'a>{
    interner:&'a SymbolInterner,
    context:&'a TypeContext,
    self_type : Option<Type>
}
impl<'a> TypeLower<'a>{
    pub fn new(interner:&'a SymbolInterner,context:&'a TypeContext,self_type:Option<Type>)->Self{
        Self { 
            interner,
            context,
            self_type
        }
    }
    pub fn lower_generic_args(&self,generic_args:&[GenericArg]) -> GenericArgs{
        GenericArgs::new(generic_args.iter().map(|arg|{
            self.lower_type(&arg.ty)
        }).collect())
    }
    pub fn get_generic_args(&self,path:&QualifiedPath) -> Option<GenericArgs>{
        let generic_args = match path{
            QualifiedPath::TypeRelative(_,segment) => {
                &segment.args
            },
            QualifiedPath::Resolved(path) => {
                match path.final_res{
                    Resolution::None => {
                        let segment = path.segments.iter().rev().find(|segment|{
                            !matches!(segment.res,Resolution::None)
                        })?;
                        &segment.args
                    },
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
                    Resolution::Primitive(_) | Resolution::Variable(_) | Resolution::Definition(DefKind::Param, _) | Resolution::SelfType | Resolution::Builtin(_) => return Some(GenericArgs::new_empty())
                }
            }
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
                match path{
                    QualifiedPath::Resolved(resolved_path) => {
                        match resolved_path.final_res{
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
                                let symbol = generics.param_names[(index - generics.base) as usize].index;
                                Type::Param(index, symbol)
                            },
                            Resolution::SelfType => {
                                self.self_type.clone().expect("Should always have a self type whenever Self appears")
                            }
                            _ => {
                                TypeError.emit(format!("Cannot use '{}' as type.",resolved_path.format(self.interner)), resolved_path.span);
                                Type::new_error()
                            }
                        }
                    },
                    QualifiedPath::TypeRelative(ty,segment) => {
                        let ty = self.lower_type(&ty);
                        if !self.context.get_methods(&ty, segment.ident.index).is_empty(){
                            TypeError.emit(format!("Cannot use method {} of type {} as type.",TypeFormatter::new(self.interner, self.context).format_type(&ty),self.interner.get(segment.ident.index)), segment.ident.span);
                        }
                        else{
                            TypeError.emit(format!("{} has no member {}.",TypeFormatter::new(self.interner, self.context).format_type(&ty),self.interner.get(segment.ident.index)), segment.ident.span);
                        }
                        Type::new_error()

                    }
                }
            }
        }
    }
    
}