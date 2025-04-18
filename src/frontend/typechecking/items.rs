use crate::frontend::ast_lowering::hir;

///Used for lowering items for type checking
pub struct ItemLower{

}

impl ItemLower{
    fn lower_item(&mut self,item:hir::Item){
        match item{
            hir::Item::Function(function_def) => {

            },
            hir::Item::Struct(generics,struct_def) => {

            },
            hir::Item::Enum(generics,name ,variants) => {

            },
            hir::Item::Impl(ty, methods) => {

            }
        }
    }
}