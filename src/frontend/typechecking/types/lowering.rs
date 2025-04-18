use crate::{data_structures::{IndexVec, IntoIndex}, frontend::{ast_lowering::hir::{self, Ident}, typechecking::context::{FieldDef, FuncSig, FunctionDef, StructDef, TypeContext}}, identifiers::{FuncIndex, StructIndex}};

use super::{generics::GenericArgs, Type};

pub enum LoweredItem {
    Struct(StructIndex),
    Function(FuncIndex,Vec<hir::Pattern>,hir::Expr)
}
pub struct TypeLower{
    structs : IndexVec<StructIndex,StructDef>,
    functions : IndexVec<FuncIndex,FunctionDef>
}
impl TypeLower{
    pub fn new()->Self{
        Self { 
            structs : IndexVec::new(),
            functions : IndexVec::new()
        }
    }
    pub fn into_context(self) -> TypeContext{
        TypeContext{
            structs : self.structs,
            functions : self.functions
        }
    }
    pub fn lower(&mut self,ty:&hir::Type) -> Type{
        match &ty.kind{
            hir::TypeKind::Array(element) => Type::new_array(self.lower(element)),
            hir::TypeKind::Function(params, return_type) => 
                Type::new_function(params.iter().map(|param| self.lower(param)).collect(), return_type.as_ref().map_or(Type::new_unit(), |ty| self.lower(ty))),
            hir::TypeKind::Tuple(elements) => Type::new_tuple(elements.into_iter().map(|element| self.lower(element)).collect()),
            hir::TypeKind::Path(path) => {
                match path.def{
                    hir::PathDef::PrimitiveType(ty) => {
                        match ty{
                            hir::PrimitiveType::Int => Type::Int,
                            hir::PrimitiveType::Bool => Type::Bool,
                            hir::PrimitiveType::Float => Type::Float,
                            hir::PrimitiveType::Never => Type::Never,
                            hir::PrimitiveType::String => Type::String
                        }
                    },
                    hir::PathDef::Enum(enum_index) => Type::Enum(GenericArgs::new_empty(), enum_index),
                    hir::PathDef::Struct(index) => Type::Struct(GenericArgs::new_empty(), index),
                    hir::PathDef::GenericParam(index, name) => Type::Param(index.as_index(),name),
                    _ => todo!("THE PATHS ")
                }
            }
        }
    }
    pub fn lower_generic_params(&mut self,generics:hir::Generics) -> Vec<Ident>{
        generics.params.into_iter().map(|param|{
            param.0
        }).collect()
    }
    pub fn lower_item(&mut self,item:hir::Item) -> LoweredItem{
        match item{
            hir::Item::Struct(generics, variant_def) => {
                self.lower_generic_params(generics);
                let lowered_struct = StructDef { 
                    name : variant_def.name,
                    fields: variant_def.fields.into_iter().map(|field|{
                        let field_ty = self.lower(&field.ty);
                        FieldDef { name: field.name, ty: field_ty }
                    }).collect()
                };
                let struct_index = self.structs.push(lowered_struct);
                LoweredItem::Struct(struct_index)
            },
            hir::Item::Function(function_def) => {
                let generics = self.lower_generic_params(function_def.generics);
                let (patterns,input_types) = {
                    let mut patterns = Vec::with_capacity(function_def.function.params.len());
                    let mut input_types = Vec::with_capacity(function_def.function.params.len());
                    function_def.function.params.into_iter().for_each(|param|{
                        patterns.push(param.pattern);
                        input_types.push(self.lower(&param.ty));
                    });
                    (patterns,input_types)
                };
                let return_type = function_def.function.return_type.map(|param_ty| self.lower(&param_ty)).unwrap_or(Type::new_unit());
                let sig = FuncSig { params: input_types, return_type };
                let func_index = self.functions.push(FunctionDef { name: function_def.name, generics, sig });
                LoweredItem::Function(func_index,patterns,function_def.function.body)
            },
            _ => todo!("REST OF ITEMS TO LOWER")
        }
    }
    
}