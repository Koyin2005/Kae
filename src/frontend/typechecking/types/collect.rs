use crate::{data_structures::IndexVec, frontend::{ast_lowering::hir::{self, DefId, Ident, Item}, typechecking::context::{EnumDef, FieldDef, FuncSig, FunctionDef, Generics, Impl, StructDef, TypeContext, VariantDef}}, identifiers::ItemIndex, GlobalSymbols, SymbolInterner};

use super::{lowering::TypeLower, Type};

pub struct ItemCollector<'a>{
    context : TypeContext,
    interner : &'a SymbolInterner,
    symbols : &'a GlobalSymbols
}

impl<'a> ItemCollector<'a>{
    pub fn new(interner:&'a SymbolInterner,symbols:&'a GlobalSymbols)->Self{
        Self { 
            context: TypeContext::new(), 
            interner,
            symbols
        }
    }
    fn lower_type_with(&self,ty:&hir::Type,lowered_ty:&Type) -> Type{
        TypeLower::new(self.interner, &self.context,Some(lowered_ty)).lower_type(ty)
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
        let param_names = generics.params.iter().enumerate().map(|(i,&hir::GenericParam(name,id))|{
            self.add_name(id, name);
            self.add_child(owner_id, id);
            self.context.params_to_indexes.insert(id, i as u32);
            name
        }).collect();
        self.context.generics_map.insert(owner_id, Generics{
            owner_id,
            param_names,
        });
    }
    fn collect_defs(&mut self,item:&Item) -> bool{
        match item{
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
            &Item::Impl(id,_,ref methods) => {
                for method in methods{
                    self.add_child(id, method.id);
                    self.collect_generic_defs(method.id, &method.generics);
                }
                true
            }
        }
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
            &Item::Impl(id,ref ty,ref methods) => {
                let self_type = self.lower_type(ty);
                let methods = methods.iter().map(|method|{
                    let has_receiver = method.function.params.first().is_some_and(|param| matches!(param.pattern.kind,hir::PatternKind::Binding(_,name,_) if name.index == self.symbols.lower_self_symbol()));
                    (method.id,has_receiver,FunctionDef{
                        name:method.name,
                        sig: FuncSig { 
                            params: method.function.params.iter().map(|param| self.lower_type_with(&param.ty,&self_type)).collect(), 
                            return_type: method.function.return_type.as_ref().map_or(Type::new_unit(), |ty| self.lower_type_with(&ty,&self_type))
                        } 
                    })
                }).collect::<Vec<_>>();
                self.context.ty_impl_map.entry(self_type.clone()).or_insert(Vec::new()).push(id);
                self.context.impls.insert(id, Impl{
                    span:ty.span,
                    ty:self_type,
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


