use fxhash::FxHashMap;
use typed_ast::ConstructorKind;
use types::{GenericArgs, Type};

use crate::{data_structures::{IndexVec, IntoIndex}, identifiers::{EnumIndex, FieldIndex, StructIndex, SymbolIndex, VariableIndex, VariantIndex}};

use super::ast_lowering::hir::Ident;

pub mod typechecker;
pub mod typed_ast;
pub mod types;
mod patterns;
pub mod generics;
pub mod substituter;
mod env;

pub struct TypeContext{
    pub enums : IndexVec<EnumIndex,EnumDef>,
    pub structs : IndexVec<StructIndex,StructDef>,
    pub variables : IndexVec<VariableIndex,SymbolIndex>,

    field_indexes : FxHashMap<ConstructorKind,FxHashMap<SymbolIndex,FieldIndex>>
}

impl TypeContext{
    pub fn new()->Self{
        Self { enums: IndexVec::new(), structs: IndexVec::new(), variables: IndexVec::new(), field_indexes: FxHashMap::default() }
    }
    pub fn get_field_index(&mut self,constructor:ConstructorKind,field:SymbolIndex) -> Option<FieldIndex>{
        self.get_field_indexes(constructor).get(&field).copied()
    }
    pub fn get_field_type(&self,constructor:ConstructorKind,generic_args:&GenericArgs,field:FieldIndex) -> Type{
        match constructor{
            ConstructorKind::Struct(struct_index)=> {
                let field_type = &self.structs[struct_index].fields[field].ty;
                if generic_args.is_empty() { field_type.clone() } else { field_type.substitute(generic_args) }
            },
            ConstructorKind::Variant(enum_index,variant_index ) => {
                let field_type = &self.enums[enum_index].variants[variant_index].0.fields[field].ty;
                if generic_args.is_empty() { field_type.clone() } else { field_type.substitute(generic_args) }
            }
        }
    }
    pub fn get_field_indexes(&mut self,constructor:ConstructorKind) -> &FxHashMap<SymbolIndex,FieldIndex>{
        self.field_indexes.entry(constructor).or_insert_with(||{
            match constructor{
                ConstructorKind::Struct(struct_index) => {
                    self.structs[struct_index].fields.iter().enumerate().map(|(i,field)|{
                        (field.name.index,FieldIndex::new(i as u32))
                    }).collect()
                },
                ConstructorKind::Variant(enum_index, variant_index) => {
                    self.enums[enum_index].variants[variant_index].0.fields.iter().enumerate().map(|(i,field)|{
                        (field.name.index,FieldIndex::new(i as u32))
                    }).collect()
                }
            }
        })
    }
}

pub struct FieldDef{
    pub name : Ident,
    pub ty : types::Type
}
pub struct VariantDef(StructDef);
pub struct EnumDef{
    pub name : Ident,
    pub variants : IndexVec<VariantIndex,VariantDef>
}
pub struct StructDef{
    pub name : Ident,
    pub fields : IndexVec<FieldIndex,FieldDef>

}