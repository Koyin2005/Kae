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
        receiver_generic_params:Option<&'a Generics>,
        sig : FuncSig,
        id : Option<DefId>
    }
}

pub struct MethodPick{
    pub owner : DefId,
    pub owner_generic_args : GenericArgs,
    pub method_id : DefId,
    pub has_receiver : bool,
    ///May contain self parameter if has_receiver is true
    pub sig : FuncSig
}


pub struct MethodLookup<'a>{
    pub generic_params : Option<&'a Generics>,
    pub base_generic_args : GenericArgs,
    pub sig : FuncSig,
    pub has_receiver : bool,
    pub id : Option<DefId>
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
    pub(super) signatures : DefIdMap<FuncSig>
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
            signatures : DefIdMap::new()
        }
    }
    /*Maps ty's generic args to impl_type's generic args (If the type's are supposed to be the same)*/
    pub fn map_generic_args(&self,ty:&Type,impl_type:&Type,generics:&Generics,parent_args:GenericArgs)->Option<GenericArgs>{
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
    pub fn get_methods<'a>(&'a self,ty:&'a Type,method_name:SymbolIndex) -> Vec<MethodPick>{
        let mut valid_methods = Vec::new();
        for &impl_id in self.impl_ids.iter(){
            let impl_ = &self.impls[impl_id];
            let ty_with_impl = &impl_.ty;
            //Try an inherent method
            let generics = self.expect_generics_for(impl_id);
            if let Some(generic_args) = self.map_generic_args(ty, ty_with_impl, generics, GenericArgs::new_empty()){
                //Find all methods on this impl that share this name
                valid_methods.extend(impl_.methods.iter().copied().filter_map(|method_id|{
                    if self.ident(method_id).index == method_name{
                        let has_receiver = self.method_has_receiver[method_id];
                        Some(MethodPick{
                            owner:impl_id,
                            owner_generic_args : generic_args.clone(),
                            method_id,
                            has_receiver : has_receiver,
                            sig : self.signatures[method_id].clone(),

                        })
                    }
                    else{
                        None
                    }
                }));
                
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
    pub fn get_variant_index(&self,variant_id:DefId) -> Option<VariantIndex>{
        self.child_to_owner_map.get(variant_id).copied().and_then(|owner| 
            self.enums.get(owner)).and_then(|enum_| enum_.variants.iter().position(|variant| variant.id == variant_id).map(|variant_index| VariantIndex::new(variant_index as u32))
        )
    }
    pub fn get_variant(&self,variant_id:DefId) -> Option<&VariantDef>{
        self.child_to_owner_map.get(variant_id).copied().and_then(|owner| self.enums.get(owner)).and_then(|enum_| enum_.variants.iter().find(|variant| variant.id == variant_id))
    }
    pub fn get_variant_of(&self,enum_id:DefId,name:SymbolIndex) -> Option<&VariantDef>{
        self.enums[enum_id].variants.iter().find(|variant| variant.name.index == name)
    }
    pub fn get_generic_count(&self,res:&hir::Resolution) -> usize{
        match res{
            &hir::Resolution::Definition(hir::DefKind::Struct|hir::DefKind::Enum|hir::DefKind::Function,id) => self.expect_generics_for(id).param_names.len(),
            hir::Resolution::Variable(_) | 
            hir::Resolution::Definition(hir::DefKind::Variant|hir::DefKind::Param, _) | 
            hir::Resolution::Primitive(_) | 
            hir::Resolution::Builtin(hir::BuiltinKind::Panic)|
            hir::Resolution::SelfType | hir::Resolution::None => 0
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
                            variant.fields.iter().any(|field|{
                                self.is_type_recursive(&TypeSubst::new(generic_args).instantiate_type(&field.ty), id)
                            })
                        })
                    }
                }
            }
        }
    }


    pub fn get_member(&self,symbols:&GlobalSymbols,ty:&Type,member:Ident) -> Option<TypeMember>{
        if let Some((generic_args,id,AdtKind::Enum)) = ty.as_adt(){
            if let Some(variant) = self.get_variant_of(id, member.index){
                return Some(TypeMember::Variant(id,generic_args.clone(), variant));
            }
        }
        self.get_method(symbols,ty, member,true).map(|MethodLookup { generic_params,base_generic_args, sig,id,has_receiver:_ }|{
            TypeMember::Method { receiver_generic_args:base_generic_args,receiver_generic_params: generic_params, sig,id}
        })
    }
    
    pub fn get_method(&self,symbols:&GlobalSymbols,ty:&Type,method_ident:Ident,keep_receiver:bool) -> Option<MethodLookup>{
        let method_index = method_ident.index;
        if let Type::Array(_) | Type::String = ty{
            if method_ident.index == symbols.len_symbol(){
                return Some(MethodLookup{
                    generic_params : None,
                    sig : FuncSig { params: vec![], return_type: Type::Int },
                    base_generic_args : GenericArgs::new_empty(),
                    id : None,
                    has_receiver : true
                });
            }
        }   
        self.get_methods(ty, method_index).pop().map(|method|{
            let generics = self.expect_generics_for(method.method_id);
            let sig = {
                let mut sig = method.sig;
                if method.has_receiver && !keep_receiver{
                    sig.params.remove(0);
                }
                sig
            };
            MethodLookup{generic_params:Some(generics),base_generic_args:method.owner_generic_args,sig,id:Some(method.method_id),has_receiver:method.has_receiver}
        })
    }
}