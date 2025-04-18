use crate::{data_structures::IndexVec, frontend::{ast_lowering::hir::{self, DefId, Ident, Item}, typechecking::context::{FieldDef, FuncSig, FunctionDef, Generics, StructDef, TypeContext}}, identifiers::ItemIndex, SymbolInterner};

use super::{lowering::TypeLower, Type};

pub struct ItemCollector<'a>{
    context : TypeContext,
    interner : &'a SymbolInterner,
}

impl<'a> ItemCollector<'a>{
    pub fn new(interner:&'a SymbolInterner)->Self{
        Self { 
            context: TypeContext::new(), 
            interner,
        }
    }
    fn lower_type(&self,ty:&hir::Type) -> Type{
        TypeLower::new(self.interner, &self.context).lower(ty)
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
                todo!("Enum collection")
            },
            Item::Impl(_ty,_methods) => {
                todo!("Impl collection")
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
            Item::Enum(_enum_def) => {
                todo!("Enum collection")
            },
            Item::Impl(_ty,_methods) => {
                todo!("Impl collection")
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


