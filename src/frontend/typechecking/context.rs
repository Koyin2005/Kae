use crate::{data_structures::IntoIndex, frontend::{ast_lowering::hir::{self, DefId, DefIdMap, Ident}, tokenizing::SourceLocation}, identifiers::{SymbolIndex, VariantIndex}, GlobalSymbols};

use super::{ types::{generics::GenericArgs, subst::{Subst, TypeSubst}, AdtKind, Type}};

pub struct FieldDef{
    pub name : Ident,
    pub ty : Type
}
pub struct StructDef{
    pub name : Ident,
    pub fields: Vec<FieldDef>
}
pub struct VariantDef{
    pub id : DefId,
    pub name : Ident,
    pub fields : Vec<Type>
}
pub struct EnumDef{
    pub name : Ident,
    pub variants : Vec<VariantDef>
}
#[derive(Clone,Debug)]
pub struct FuncSig{
    pub params : Vec<Type>,
    pub return_type : Type
}

impl FuncSig{
    pub fn as_type(&self) -> Type{
        Type::new_function(self.params.clone(), self.return_type.clone())
    }
}

pub struct GenericConstraint{
    pub span : SourceLocation
}

pub struct Generics{
    pub owner_id : DefId,
    pub parent_count : usize,
    pub param_names : Vec<Ident>,
}
impl Generics{
    pub fn param_at(&self,index:usize) -> Ident{
        self.param_names[index - self.parent_count]
    }
}
pub struct FunctionDef{
    pub name : Ident,
    pub sig : FuncSig
}
pub struct Impl{
    pub span : SourceLocation,
    pub ty : Type,
    pub methods : Vec<DefId>
}
#[derive(Clone,Copy)]
pub struct TraitMethod{
    pub id : DefId,
    pub has_default_impl : bool
}
pub struct Trait{
    pub span : SourceLocation,
    pub methods : Vec<TraitMethod>
}
pub enum TypeMember<'a>{
    Variant(DefId,GenericArgs,&'a VariantDef),
    Method{
        receiver_generic_args: GenericArgs,
        sig : FuncSig,
        id : DefId
    }
}


pub struct TypeContext{
    pub(super) structs : DefIdMap<StructDef>,
    pub(super) enums : DefIdMap<EnumDef>,
    pub(super) generics_map : DefIdMap<Generics>,
    pub(super) params_to_indexes : DefIdMap<u32>,
    pub(super) method_has_receiver : DefIdMap<bool>,
    pub(super) child_to_owner_map : DefIdMap<DefId>,
    pub(super) impls : DefIdMap<Impl>,
    pub(super) impl_ids : Vec<DefId>,
    pub(super) name_map : DefIdMap<Ident>,
    pub(super) signatures : DefIdMap<FuncSig>,
    pub(super) type_ids_to_method_impls : DefIdMap<Vec<DefId>>,
    pub(super) has_receiver : DefIdMap<bool>,
}
impl TypeContext{
    pub fn new() -> Self{
        Self { 
            structs: DefIdMap::new(), 
            name_map : DefIdMap::new(),
            generics_map:DefIdMap::new(),
            method_has_receiver: DefIdMap::new(),
            enums: DefIdMap::new(),
            params_to_indexes : DefIdMap::new(),
            child_to_owner_map : DefIdMap::new(),
            impls : DefIdMap::new(),
            impl_ids : Vec::new(),
            signatures : DefIdMap::new(),
            type_ids_to_method_impls : DefIdMap::new(),
            has_receiver : DefIdMap::new()
        }
    }
    pub fn get_member_ids(&self, ty: &Type, name : SymbolIndex) -> Vec<(hir::DefKind,DefId)>{
        let mut members = if let &Type::Adt(_,id,AdtKind::Enum) = ty {
            self.enums[id].variants.iter().filter_map(|variant|(self.ident(variant.id).index == name).then_some((hir::DefKind::Variant,variant.id))).collect()
        } else { Vec::new()};

        members.extend(self.get_method_ids(ty).into_iter().filter_map(|id| (self.ident(id).index == name).then_some((hir::DefKind::Method,id))));
        members

    }
    pub fn get_variant_ids(&self, ty:&Type) -> Vec<DefId>{
        if let &Type::Adt(_,id,AdtKind::Enum) = ty {
            self.enums[id].variants.iter().map(|variant| variant.id).collect()
        }
        else{
            Vec::new()
        }
    }
    pub fn get_method_ids(&self,ty:& Type) -> Vec<DefId>{
        if let &Type::Adt(_,id,_) = ty {
            let Some(methods) = self.type_ids_to_method_impls.get(id) else {
                return Vec::new();
            };
            return methods.clone();
        }
        Vec::new()
    }
    pub fn ident(&self,id:DefId) -> Ident{
        self.name_map.get(id).copied().expect(&format!("There should be an ident for this id {:?}",id))
    }
    pub fn expect_index_for(&self,param_def_id:DefId) -> u32{
        self.params_to_indexes[param_def_id]
    }
    pub fn get_owner_of(&self,child:DefId) -> Option<DefId>{
        self.child_to_owner_map.get(child).copied()
    }
    pub fn expect_owner_of(&self,child:DefId) -> DefId{
        self.child_to_owner_map.get(child).copied().expect("There should be an owner for this child")
    }
    pub fn get_generics_for(&self,owner_id:DefId) -> Option<&Generics>{
        self.generics_map.get(owner_id)
    }
    pub fn expect_generics_for(&self,owner_id:DefId) -> &Generics{
        self.generics_map.get(owner_id).expect("There should be some generics here")
    }
    pub fn get_variant_index(&self,variant_id:DefId) -> Option<VariantIndex>{
        self.child_to_owner_map.get(variant_id).copied().and_then(|owner| 
            self.enums.get(owner)).and_then(|enum_| enum_.variants.iter().position(|variant| variant.id == variant_id).map(|variant_index| VariantIndex::new(variant_index as u32))
        )
    }
    pub fn expect_struct(&self, struct_id: DefId) -> &StructDef{
        self.structs.get(struct_id).expect("There should be a struct")
    }
    pub fn expect_variant(&self,variant_id:DefId) -> &VariantDef{
        self.get_variant(variant_id).expect("There should be a variant")
    }
    pub fn get_variant(&self,variant_id:DefId) -> Option<&VariantDef>{
        self.child_to_owner_map.get(variant_id).copied().and_then(|owner| self.enums.get(owner)).and_then(|enum_| enum_.variants.iter().find(|variant| variant.id == variant_id))
    }
    pub fn get_variant_of(&self,enum_id:DefId,name:SymbolIndex) -> Option<&VariantDef>{
        self.enums[enum_id].variants.iter().find(|variant| variant.name.index == name)
    }
    pub fn get_generic_count(&self,res:&hir::Resolution) -> usize{
        match res{
            &hir::Resolution::Definition(hir::DefKind::Struct|hir::DefKind::Enum|hir::DefKind::Function | hir::DefKind::Method,id) => {
                self.expect_generics_for(id).param_names.len()
            },
            hir::Resolution::Variable(_) | 
            hir::Resolution::Definition(hir::DefKind::Variant|hir::DefKind::Param, _) | 
            hir::Resolution::Primitive(_) | 
            hir::Resolution::Builtin(hir::BuiltinKind::Panic)|
            hir::Resolution::SelfType(_) | hir::Resolution::None => 0
        }
    }
    pub fn is_type_recursive(&self,ty:&Type,id:DefId)->bool{
        match ty{
            Type::Int | Type::Float | Type::Bool | Type::String | Type::Error | Type::Never | Type::Param(_,_) => false,
            Type::Function(_,_) | Type::Array(_) => false,
            Type::Tuple(elements) => {
                elements.iter().any(|element| self.is_type_recursive(element, id))
            },
            &Type::Adt(ref generic_args,type_id, kind) => {
                match kind{
                    _ if type_id == id => true,
                    AdtKind::Struct => {
                        self.structs[type_id].fields.iter().any(|field|{
                            self.is_type_recursive(&TypeSubst::new(generic_args).instantiate_type(&field.ty), id)
                        })
                    },
                    AdtKind::Enum => {
                        self.enums[type_id].variants.iter().any(|variant|{
                            variant.fields.iter().any(|variant_ty|{
                                self.is_type_recursive(&TypeSubst::new(generic_args).instantiate_type(variant_ty), id)
                            })
                        })
                    }
                }
            }
        }
    }
    pub fn get_member(&self,_:&GlobalSymbols,ty:&Type,member:Ident) -> Option<TypeMember>{
        self.get_member_ids(ty,member.index).first().copied().map(|(kind,id)|{
            match kind{
                hir::DefKind::Method => {
                    let (generic_args,_,_) = ty.as_adt().expect("Only an adt can have a method on it (for now)");
                    TypeMember::Method { receiver_generic_args: generic_args.clone(), sig: self.signatures[id].clone(), id }
                },
                hir::DefKind::Variant => {
                    let (generic_args,_,_) = ty.as_adt().expect("Only an adt can have variants");
                    TypeMember::Variant(id,generic_args.clone(),self.get_variant(id).expect("This should be a variant"))
                },
                _ => unreachable!("Can only have a method or variant here")
            }
        })
    }
    pub fn get_variant_by_index(&self, enum_id: DefId, index: VariantIndex) -> &VariantDef{
        &self.enums[enum_id].variants[index.as_index() as usize]
    }
    pub fn expect_variants_for(&self, enum_id: DefId) -> Vec<VariantIndex>{
        (0..self.enums[enum_id].variants.len()).map(|variant| VariantIndex::new(variant as u32)).collect()
    }
    pub fn field_defs(&self, struct_id: DefId) -> &[FieldDef]{
        &self.structs[struct_id].fields
    }
}