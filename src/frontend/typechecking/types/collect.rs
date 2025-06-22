use crate::{data_structures::IndexVec, errors::ErrorReporter, frontend::{
        ast_lowering::hir::{self, BodyOwner, DefId, DefKind, Hir, Ident, Item}, 
        typechecking::context::{EnumDef, FieldDef, Generics, Impl, StructDef, TypeContext, VariantDef}}, identifiers::ItemIndex, GlobalSymbols, SymbolInterner};

use super::{ lowering::TypeLower, Type};

pub struct ItemCollector<'a>{
    context : TypeContext,
    interner : &'a SymbolInterner,
    symbols : &'a GlobalSymbols,
    next_param_index : u32,
    error_reporter : ErrorReporter,
    items : &'a IndexVec<ItemIndex,Item>,
    hir : &'a Hir
}

impl<'a> ItemCollector<'a>{
    pub fn new(symbol_interner: &'a SymbolInterner, symbols: &'a GlobalSymbols,items: &'a IndexVec<ItemIndex,Item>,hir:&'a Hir) -> Self{
        Self { 
            context: TypeContext::new(), 
            interner: symbol_interner, 
            symbols, 
            next_param_index: 0, 
            error_reporter: ErrorReporter::new(true),
            items,
            hir
        }
    }
    fn lowerer(&self) -> TypeLower{
        TypeLower::new(self.interner, &self.context, None, &self.error_reporter)
    }
    fn lowerer_with_self(&self, ty: Type) -> TypeLower{
        TypeLower::new(self.interner, &self.context, Some(ty), &self.error_reporter)
    }
    fn add_kind(&mut self, id: DefId, kind: DefKind){
        self.context.kinds.insert(id, kind);
    }
    fn add_name(&mut self, id: DefId, name: Ident){
        self.context.name_map.insert(id, name);
    }
    fn add_child_for(&mut self, parent: DefId, child: DefId){
        self.context.child_to_owner_map.insert(child, parent);
    }
    fn collect_names_for_generics(&mut self, owner : DefId, generics: &'a hir::Generics){
        let parent_count = self.next_param_index;
        let mut param_names = Vec::new();
        for param in generics.params.iter(){
            self.add_name(param.1, param.0);
            self.add_child_for(owner, param.1);
            self.add_kind(param.1, DefKind::Param);
            self.context.params_to_indexes.insert(param.1, self.next_param_index);
            self.next_param_index+=1;
            param_names.push(param.0);
        }
        self.context.generics_map.insert(owner,Generics { owner_id: owner, parent_count:parent_count as usize, param_names });
    }
    fn collect_declarations_for_item(&mut self, item: &'a Item){
        let old_count = self.next_param_index;
        self.next_param_index = 0;
        match item{
            Item::Struct(struct_def) => {
                self.add_name(struct_def.id, struct_def.name);
                self.add_kind(struct_def.id, DefKind::Struct);
                self.collect_names_for_generics(struct_def.id, &struct_def.generics);
            },
            Item::Enum(enum_def) => {
                self.add_name(enum_def.id, enum_def.name);
                self.add_kind(enum_def.id, DefKind::Enum);
                self.collect_names_for_generics(enum_def.id, &enum_def.generics);
                for variant in &enum_def.variants{
                    self.add_name(variant.id,variant.name);
                    self.add_kind(variant.id, DefKind::Variant);
                    self.add_child_for(enum_def.id,variant.id);
                }
            },
            Item::Function(function_def) => {
                self.add_name(function_def.id, function_def.name);
                self.add_kind(function_def.id, DefKind::Function);
                self.collect_names_for_generics(function_def.id, &function_def.generics);
            },
            Item::Impl(impl_) => {
                let Some(type_id) = impl_.ty.id() else {
                    self.error_reporter.emit(format!("Cannot make an impl for non-nominal type '{}'.",impl_.ty.format(self.interner)), impl_.ty.span);
                    return;
                };
                self.collect_names_for_generics(impl_.id,&impl_.generics);
                let parent_count = self.next_param_index;
                for method in &impl_.methods{
                    self.add_name(method.id, method.name);
                    self.add_child_for(impl_.id, method.id);
                    self.add_kind(method.id, DefKind::Method);
                    self.collect_names_for_generics(method.id, &method.generics);
                    self.context.type_ids_to_method_impls.entry(type_id).or_default().push(method.id);
                    self.context.has_receiver.insert(method.id,self.hir.bodies[self.hir.owner_to_bodies[method.id]].params.first().is_some_and(|param|{
                        matches!(param.pattern.kind,hir::PatternKind::Binding(_,name,_) if name.index == self.symbols.lower_self_symbol())
                    }));
                    self.next_param_index = parent_count;
                }
            }
        }
        self.next_param_index = old_count;

    }
    fn collect_definitions_for_items(&mut self, item: &'a Item){
        match item{
            Item::Struct(struct_def) => {
                let id = struct_def.id;
                let struct_def = StructDef { 
                    name: struct_def.name, 
                    fields: struct_def.fields.iter().map(|field|{
                        FieldDef { name: field.name, ty: self.lowerer().lower_type(&field.ty) }
                    }).collect()
                };
                self.context.structs.insert(id, struct_def);
            },
            Item::Enum(enum_def) => {
                let id = enum_def.id;
                let enum_def = EnumDef{
                    name: enum_def.name,
                    variants: enum_def.variants.iter().map(|variant|{
                        VariantDef { 
                            id: variant.id, 
                            name: variant.name, 
                            fields : variant.fields.iter().map(|ty|  self.lowerer().lower_type(ty)).collect(),
                        }
                    }).collect()
                };
                self.context.enums.insert(id, enum_def);
            },
            Item::Function(function_def) => {
                let id = function_def.id;
                let sig = self.lowerer().lower_sig(function_def.function.params.iter(), function_def.function.return_type.as_ref()
                );
                self.context.signatures.insert(id, sig);
            },
            Item::Impl(impl_) => {
                let id = impl_.id;
                let self_ty = self.lowerer().lower_type(&impl_.ty);
                let impl_ = Impl { 
                    span: impl_.span,
                    methods: impl_.methods.iter().map(|method|{
                        let sig = self.lowerer_with_self(self_ty.clone()).lower_sig(method.function.params.iter(), method.function.return_type.as_ref());
                        self.context.signatures.insert(method.id, sig);
                        method.id
                    }).collect(),
                    ty : self_ty
                };
                self.context.impl_ids.push(id);
                self.context.impls.insert(id, impl_);
            }
        }
    }
    pub fn collect(mut self) -> (TypeContext,ErrorReporter){
        /*Declare all names in items*/
        for item in self.items.iter(){
            self.collect_declarations_for_item(item);
        }
        if self.error_reporter.error_occurred() {
            return (self.context,self.error_reporter);
        }
        /*Define all items*/
        for item in self.items.iter(){
            self.collect_definitions_for_items(item);
        }
        for owner in self.hir.body_owners.iter(){
            if let BodyOwner::AnonFunction(id) = owner{
                self.add_kind(*id, DefKind::AnonFunction);
            }
        }
        (self.context,self.error_reporter)
    }
}