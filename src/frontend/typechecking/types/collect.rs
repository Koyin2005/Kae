use fxhash::FxHashMap;

use crate::{data_structures::IndexVec, frontend::{ast_lowering::hir::{self, DefId, Ident, Item}, typechecking::context::{EnumDef, FieldDef, FuncSig, FunctionDef, Generics, Impl, MethodDef, StructDef, Trait, TraitMethod, TypeContext, VariantDef}}, identifiers::ItemIndex, GlobalSymbols, SymbolInterner};

use super::{lowering::TypeLower, Type};

pub struct ItemCollector<'a>{
    context : TypeContext,
    interner : &'a SymbolInterner,
    symbols : &'a GlobalSymbols,
    next_param_index : u32
}

impl<'a> ItemCollector<'a>{
    pub fn new(interner:&'a SymbolInterner,symbols:&'a GlobalSymbols)->Self{
        Self { 
            context: TypeContext::new(), 
            interner,
            symbols,
            next_param_index : 0
        }
    }
    fn lower_type_with(&self,ty:&hir::Type,lowered_ty:&Type) -> Type{
        TypeLower::new(self.interner, &self.context,Some(lowered_ty.clone())).lower_type(ty)
    }
    fn lower_type(&self,ty:&hir::Type) -> Type{
        TypeLower::new(self.interner, &self.context,None).lower_type(ty)
    }
    fn add_name(&mut self,id:DefId,name:Ident){
        self.context.name_map.insert(id, name);
    }
    fn add_child(&mut self,owner_id:DefId,child:DefId){
        self.context.child_to_owner_map.insert(child, owner_id);
    }
    fn collect_generic_defs(&mut self,owner_id:DefId,generics:&hir::Generics){
        let parent_count = self.next_param_index as usize;
        let mut constraints = FxHashMap::default();
        let param_names = generics.params.iter().map(|&hir::GenericParam(name,id,ref generic_constraint)|{
            let index = self.next_param_index;
            self.next_param_index += 1;
            self.add_name(id, name);
            self.add_child(owner_id, id);
            self.context.params_to_indexes.insert(id, index);
            if let Some(constraint) = generic_constraint{
                constraints.insert(index, constraint.0.clone());
            }
            name
        }).collect();
        self.context.generics_map.insert(owner_id, Generics{
            parent_count,
            owner_id,
            param_names,
            constraints
        });
    }
    fn collect_defs(&mut self,item:&Item) -> bool{
        let old_generic_param_count = self.next_param_index;
        let collect_more_info = match item{
            Item::Struct(struct_def) => {
                self.add_name(struct_def.id, struct_def.name);
                self.collect_generic_defs(struct_def.id,&struct_def.generics);
                self.context.structs.insert(struct_def.id, StructDef{
                    name:struct_def.name,
                    fields : Vec::new()
                });
                true
            },
            Item::Function(function_def) => {
                self.add_name(function_def.id, function_def.name);
                self.collect_generic_defs(function_def.id, &function_def.generics);
                true
            },
            Item::Enum(enum_def) => {
                self.add_name(enum_def.id, enum_def.name);
                self.collect_generic_defs(enum_def.id, &enum_def.generics);
                let variants = enum_def.variants.iter().map(|variant|{
                    self.add_child(enum_def.id, variant.id);
                    self.add_name(variant.id, variant.name);
                    VariantDef{
                        id:variant.id,
                        name:variant.name,
                        fields:vec![]
                    }
                }).collect();
                self.context.enums.insert(enum_def.id, EnumDef{
                    name:enum_def.name,
                    variants
                });
                true
            },
            &Item::Impl(id,_,ref generics,ref methods,_) => {
                self.collect_generic_defs(id, generics);
                let old_count = self.next_param_index;
                for method in methods{
                    self.add_child(id, method.id);
                    self.collect_generic_defs(method.id, &method.generics);
                    self.next_param_index = old_count;
                }
                true
            },
            Item::Trait(trait_) => {
                self.collect_generic_defs(trait_.id, &trait_.generics);
                let old_count = self.next_param_index;
                for method in &trait_.methods{
                    self.add_child(trait_.id, method.id);
                    self.collect_generic_defs(method.id, &method.generics);
                    self.next_param_index = old_count;
                }
                true
            }
        };
        self.next_param_index = old_generic_param_count;
        collect_more_info
    }
    fn collect_info(&mut self,item:&Item){
        match item{
            Item::Struct(struct_def) => {
                let fields =  struct_def.fields.iter().map(|field|{
                    FieldDef{
                        name:field.name,
                        ty : self.lower_type(&field.ty)
                    }
                }).collect::<Vec<_>>();
                self.context.structs[struct_def.id].fields.extend(fields);

            },
            Item::Function(function_def) => {
                self.context.functions.insert(function_def.id, FunctionDef { 
                    name: function_def.name, 
                    sig: FuncSig { 
                        params: function_def.function.params.iter().map(|param| self.lower_type(&param.ty)).collect(), 
                        return_type: function_def.function.return_type.as_ref().map_or(Type::new_unit(), |ty| self.lower_type(&ty))
                    } 
                });
            },
            Item::Enum(enum_def) => {
                for (i,variant) in enum_def.variants.iter().enumerate(){
                    let fields =  variant.fields.iter().map(|field|{
                        FieldDef{
                            name:field.name,
                            ty : self.lower_type(&field.ty)
                        }
                    }).collect::<Vec<_>>();
                    self.context.enums[enum_def.id].variants[i].fields.extend(fields);
                }
            },
            &Item::Impl(id,ref ty,_,ref methods,ref trait_path) => {
                let self_type = self.lower_type(ty);
                let mut method_ids = Vec::new();
                for method in methods{
                    let has_receiver = method.function.params.first().is_some_and(|param| matches!(param.pattern.kind,hir::PatternKind::Binding(_,name,_) if name.index == self.symbols.lower_self_symbol()));
                    method_ids.push(method.id);
                    self.add_name(method.id, method.name);
                    self.context.methods.insert(method.id, MethodDef{
                        name:method.name,
                        has_receiver,
                        sig:FuncSig { 
                            params: method.function.params.iter().map(|param| self.lower_type_with(&param.ty,&self_type)).collect(), 
                            return_type: method.function.return_type.as_ref().map_or(Type::new_unit(), |ty| self.lower_type_with(&ty,&self_type))
                        } 
                    });
                }
                self.context.impl_ids.push(id);
                self.context.impls.insert(id, Impl{
                    span:ty.span,
                    ty:self_type,
                    methods:method_ids,
                    trait_:trait_path.clone()
                });
            },
            Item::Trait(trait_) => {
                let self_type = Type::Error;
                let mut methods = Vec::new();
                for method in &trait_.methods{
                    let has_receiver = method.params.first().is_some_and(|param| matches!(param.pattern.kind,hir::PatternKind::Binding(_,name,_) if name.index == self.symbols.lower_self_symbol()));
                    methods.push(TraitMethod{id:method.id,has_default_impl:method.body.is_some()});
                    self.add_name(method.id, method.name);
                    self.context.methods.insert(method.id, MethodDef{
                        name:method.name,
                        has_receiver,
                        sig:FuncSig { 
                            params: method.params.iter().map(|param| self.lower_type_with(&param.ty,&self_type)).collect(), 
                            return_type: method.return_type.as_ref().map_or(Type::new_unit(), |ty| self.lower_type_with(&ty,&self_type))
                        } 
                    });
                }
                self.context.name_map.insert(trait_.id, trait_.name);
                self.context.traits.insert(trait_.id, Trait{
                    span:trait_.span,
                    methods
                });

                
            }
        }
    }
    pub fn collect(mut self,items:&IndexVec<ItemIndex,Item>) -> TypeContext{
        let mut items_with_info = vec![];
        for item in items.iter(){
            if self.collect_defs(item){
                items_with_info.push(item);
            }
        }
        for item in items_with_info{
            self.collect_info(item);
        }
        self.context
    }

}


