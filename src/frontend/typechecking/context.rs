use fxhash::FxHashMap;

use crate::{frontend::{ast_lowering::hir::{self, DefId, DefIdMap, Ident, QualifiedPath}, tokenizing::SourceLocation}, identifiers::SymbolIndex};

use super::{types::{generics::GenericArgs, Type}};

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
    pub fields : Vec<FieldDef>,
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


pub struct Generics{
    pub owner_id : DefId,
    pub parent_count : usize,
    pub param_names : Vec<Ident>,
    pub constraints : FxHashMap<u32,QualifiedPath>,
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
pub struct MethodDef{
    pub name : Ident,
    pub has_receiver : bool,
    pub sig : FuncSig
}
pub struct Impl{
    pub span : SourceLocation,
    pub ty : Type,
    pub trait_ : Option<QualifiedPath>,
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
        receiver_generic_params:Option<&'a Generics>,
        sig : FuncSig,
        id : Option<DefId>
    }
}
pub struct TypeContext{
    pub(super) structs : DefIdMap<StructDef>,
    pub(super) enums : DefIdMap<EnumDef>,
    pub(super) functions : DefIdMap<FunctionDef>,
    pub(super) generics_map : DefIdMap<Generics>,
    pub(super) params_to_indexes : DefIdMap<u32>,
    pub(super) methods : DefIdMap<MethodDef>,
    pub(super) child_to_owner_map : DefIdMap<DefId>,
    pub(super) impls : DefIdMap<Impl>,
    pub(super) impl_ids : Vec<DefId>,
    pub(super) traits : DefIdMap<Trait>,
    pub(super) name_map : DefIdMap<Ident>,
}
impl TypeContext{
    pub fn new() -> Self{
        Self { 
            structs: DefIdMap::new(), 
            functions : DefIdMap::new(), 
            name_map : DefIdMap::new(),
            generics_map:DefIdMap::new(),
            methods: DefIdMap::new(),
            enums: DefIdMap::new(),
            params_to_indexes : DefIdMap::new(),
            child_to_owner_map : DefIdMap::new(),
            impls : DefIdMap::new(),
            traits: DefIdMap::new(),
            impl_ids : Vec::new()
        }
    }
    pub fn as_trait_with_span(&self,path:&hir::QualifiedPath) -> (Option<DefId>,SourceLocation){
        let (trait_,span) = match path{
            hir::QualifiedPath::Resolved(path) => {
                if let hir::Resolution::Definition(hir::DefKind::Trait,id) = path.final_res{
                    (Some(id),path.span)
                }
                else{
                    (None,path.span)
                }
            },
            hir::QualifiedPath::TypeRelative(ty,_) => (None,ty.span)
        };
        (trait_,span)

    }
    pub fn get_default_trait_methods<'a>(&'a self,ty:&'a Type,method_name:SymbolIndex) -> Vec<(DefId,DefId,&'a MethodDef,GenericArgs)>{
        let mut valid_methods = Vec::new();
        for &id in self.impl_ids.iter(){
            let impl_ = &self.impls[id];
            let ty_with_impl = &impl_.ty;
            if let Some((Some(trait_id),_)) = impl_.trait_.as_ref().map(|trait_| self.as_trait_with_span(&trait_)){
                let trait_ = &self.traits[trait_id];
                if let Some(generic_args) = self.get_generic_args_for(ty,ty_with_impl, self.expect_generics_for(id), GenericArgs::new_empty()){
                    if self.ty_impls_trait(ty, trait_id){
                        valid_methods.extend(trait_.methods.iter().filter_map(|&method|{
                            let method_def = &self.methods[method.id];
                            (method_def.name.index == method_name && method.has_default_impl).then_some((id,method.id,method_def,generic_args.clone()))
                        }));
                    }
                }
            }
        }
        valid_methods.reverse();
        valid_methods
    }
    pub fn get_generic_args_for(&self,ty:&Type,impl_type:&Type,generics:&Generics,parent_args:GenericArgs)->Option<GenericArgs>{
        let substitution = impl_type.get_substitution(ty)?;
        let parent_count = parent_args.len();
        Some(GenericArgs::new(generics.param_names.iter().enumerate().map(|(i,param_name)|{
            if let Some(&ty) = substitution.get(&(i as u32)){
                ty.clone()
            }
            else{
                Type::Param((i + parent_count) as u32,param_name.index)
            }
        }).collect()).rebase(&parent_args))
    }
    pub fn get_methods<'a>(&'a self,ty:&'a Type,method_name:SymbolIndex) -> Vec<(DefId,&'a MethodDef,GenericArgs)>{
        let mut valid_methods = Vec::new();
        for &id in self.impl_ids.iter(){
            let impl_ = &self.impls[id];
            let ty_with_impl = &impl_.ty;
            if let Some(generic_args) = self.get_generic_args_for(ty, ty_with_impl, self.expect_generics_for(id), GenericArgs::new_empty()){
                if impl_.trait_.as_ref().is_some_and(|trait_path| self.as_trait_with_span(trait_path).0.is_some_and(|trait_|self.ty_impls_trait(ty, trait_,))){
                    valid_methods.extend(impl_.methods.iter().filter_map(|&method|{
                        let method_def = &self.methods[method];
                        (method_def.name.index == method_name).then_some((method,method_def,generic_args.clone()))
                    }));
                }
            }
        }
        valid_methods.reverse();
        valid_methods
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
    pub fn get_variant(&self,variant_id:DefId) -> Option<&VariantDef>{
        self.child_to_owner_map.get(variant_id).copied().and_then(|owner| self.enums.get(owner)).and_then(|enum_| enum_.variants.iter().find(|variant| variant.id == variant_id))
    }
    pub fn get_variant_of(&self,enum_id:DefId,name:SymbolIndex) -> Option<&VariantDef>{
        self.enums[enum_id].variants.iter().find(|variant| variant.name.index == name)
    }
    pub fn get_generic_count(&self,res:&hir::Resolution) -> usize{
        match res{
            &hir::Resolution::Definition(hir::DefKind::Struct|hir::DefKind::Enum|hir::DefKind::Function|hir::DefKind::Trait,id) => self.expect_generics_for(id).param_names.len(),
            hir::Resolution::Variable(_) | 
            hir::Resolution::Definition(hir::DefKind::Variant|hir::DefKind::Param, _) | 
            hir::Resolution::Primitive(_) | 
            hir::Resolution::Builtin(hir::BuiltinKind::Panic)|
            hir::Resolution::SelfType | hir::Resolution::None | hir::Resolution::SelfAlias(_) => 0
        }
    }
    pub fn expect_generic_constraints(&self,id: DefId) -> Vec<Option<&QualifiedPath>>{
            let generics = self.expect_generics_for(id);
            (0..generics.param_names.len()).map(|i|{
                generics.constraints.get(&(i as u32))
            }).collect()
    }
    pub fn get_generic_constraints(&self,res:&hir::Resolution) -> Vec<Option<&QualifiedPath>>{
        match res{
            &hir::Resolution::Definition(hir::DefKind::Struct|hir::DefKind::Enum|hir::DefKind::Function|hir::DefKind::Trait,id) => {
                self.expect_generic_constraints(id)
            },
            hir::Resolution::Variable(_) | 
            hir::Resolution::Definition(hir::DefKind::Variant|hir::DefKind::Param, _) | 
            hir::Resolution::Primitive(_) | 
            hir::Resolution::Builtin(hir::BuiltinKind::Panic)|
            hir::Resolution::SelfType | hir::Resolution::None | hir::Resolution::SelfAlias(_) => Vec::new()
        }
    }
    pub fn ty_impls_trait(&self,ty:&Type,trait_:DefId) -> bool {
        self.impls.iter().any(|(id,impl_)|{
            if !impl_.trait_.as_ref().is_some_and(|path| self.as_trait_with_span(path).0.is_some_and(|id| id == trait_)){
                return false;
            }
            let Some(impl_generic_args) = self.get_generic_args_for(ty, &impl_.ty, self.expect_generics_for(id), GenericArgs::new_empty()) else {
                return false;
            };
            let constraints = self.expect_generic_constraints(id);
            let all_constraints_valid = impl_generic_args.iter().zip(constraints.iter()).all(|(arg,constraint)|{
                if let Some(trait_) = constraint.as_ref().and_then(|constraint|{
                    self.as_trait_with_span(constraint).0
                }){
                    self.ty_impls_trait(arg, trait_)
                }
                else{
                    true
                }
            });
            all_constraints_valid
        })
    }
}