use fxhash::FxHashSet;

use crate::{ data_structures::IntoIndex, errors::ErrorReporter, frontend::{ast_lowering::hir, tokenizing::SourceLocation, typechecking::{context::TypeContext, error::TypeError}}, identifiers::VariantIndex, SymbolInterner};

pub fn check_generic_count(error_reporter:&ErrorReporter,expected:usize,got:usize,span:SourceLocation) -> bool{
    if got == expected{
        true
    }
    else{
        error_reporter.emit(format!("Expected '{}' generic arg{} got '{}'.",expected,if expected == 1 { "" } else {"s"},got), span);
        false
    }
}
///Checks whether items are well formed
pub struct ItemCheck<'a>{
    error_reporter : &'a ErrorReporter,
    context : &'a TypeContext,
    ident_interner : &'a SymbolInterner
}

impl<'a> ItemCheck<'a>{
    pub fn new(context: &'a TypeContext, interner: &'a SymbolInterner,error_reporter:&'a ErrorReporter) -> Self{
        ItemCheck { error_reporter, context, ident_interner: interner}
    }
    fn error(&self, msg: String, span: SourceLocation){
        self.error_reporter.emit(msg, span);
    }
    pub fn check_items<'b>(self, items:impl Iterator<Item = &'b hir::Item>) -> Result<(),TypeError>{
        if self.error_reporter.error_occurred() {
            self.error_reporter.emit_all();
            return Err(TypeError);
        }
        for item in items{
            self.check_item(item);
        }
        /*Check for any overlapping implementations for certain methods */
        let mut type_methods = FxHashSet::default();
        for &id in self.context.impl_ids.iter(){
            let impl_ = &self.context.impls[id];
            let impl_ty = &impl_.ty;
            for &method in impl_.methods.iter(){
                let name = self.context.ident(method);
                if !type_methods.insert((impl_ty,name.index)){
                    self.error(format!("Repeated method '{}'.",self.ident_interner.get(name.index)), name.span);
                }
            }
        }
        if self.error_reporter.error_occurred(){
            self.error_reporter.emit_all();
            return Err(TypeError);
        }
        Ok(())
    }
    pub fn check_type(&self, ty: &hir::Type){
        match &ty.kind{
            hir::TypeKind::Array(array) => {
                self.check_type(array);
            },
            hir::TypeKind::Function(params,return_type) => {
                for param in params{
                    self.check_type(param);
                }
                if let Some(return_type) = return_type.as_ref(){
                    self.check_type(return_type);
                }
            },
            hir::TypeKind::Path(path) => {
                match path{
                    hir::QualifiedPath::FullyResolved(path) => {
                        for segment in &path.segments{
                            self.check_generic_count(self.context.get_generic_count(&segment.res), segment.args.len(), segment.ident.span);
                        }
                    },
                    hir::QualifiedPath::TypeRelative(ty,segment) => {
                        self.check_type(&ty);
                        let name = segment.ident;
                        self.error(format!("Cannot use member '{}' of '{}' as type.", self.ident_interner.get(name.index),ty.format(self.ident_interner)), name.span);
                    }
                 }
            },
            hir::TypeKind::Tuple(elements) => {
                for element in elements{
                    self.check_type(element);
                }
            }
        }
    }
    pub fn check_function(&self, function_def: &hir::Function){
        for ty in &function_def.params{
            self.check_type(&ty);
        }
        if let Some(return_type) = function_def.return_type.as_ref(){
            self.check_type(return_type);
        }

    }
    fn check_item(&self,item:&hir::Item){
        match item{
            hir::Item::Struct(struct_def) => {
                let mut repeated_fields = Vec::new();
                let mut seen_fields = FxHashSet::default();
                let mut is_recursive = false;
                for (i,field) in struct_def.fields.iter().enumerate(){
                    if !seen_fields.insert(field.name.index){
                        repeated_fields.push(field.name);
                    }
                    self.check_type(&field.ty);
                    if self.context.is_type_recursive(&self.context.structs[struct_def.id].fields[i].ty, struct_def.id){
                        is_recursive = true;
                    }
                }
                if is_recursive{
                    self.error(format!("Recursive type '{}'.",self.ident_interner.get(struct_def.name.index)),struct_def.name.span);
                }
                for field in repeated_fields{
                    self.error(format!("Repeated field '{}'.",self.ident_interner.get(field.index)),field.span);
                }
            },
            hir::Item::Function(function) => {
                self.check_function(&function.function);
            },
            hir::Item::Enum(enum_def) => {
                for (i,variant) in enum_def.variants.iter().enumerate(){
                    let mut is_recursive = false;
                    for (field_def,field_ty) in 
                        variant.fields.iter().zip(self.context.get_variant_by_index(enum_def.id, VariantIndex::new(i as u32)).fields.iter())
                    {
                        self.check_type(&field_def);
                        if self.context.is_type_recursive(&field_ty, enum_def.id){
                            is_recursive = true;
                        }
                        

                    }
                    if is_recursive{
                        self.error(format!("Recursive type '{}'.",self.ident_interner.get(enum_def.name.index)),enum_def.name.span);
                    }
                }
            },
            &hir::Item::Impl(hir::Impl{id:_,ref ty,generics:ref _generics,ref methods,span:_}) => {
                self.check_type(ty);
                for method in methods{
                    self.check_function(&method.function);
                }
            },
        }
    }

    
    
    pub fn check_generic_count(&self, expected: usize,got: usize, span: SourceLocation) -> bool{
        if got == expected{
            true
        }
        else{
            self.error_reporter.emit(format!("Expected '{}' generic arg{} got '{}'.",expected,if expected == 1 { "" } else {"s"},got), span);
            false
        }
    }
}