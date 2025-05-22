use fxhash::FxHashMap;

use crate::frontend::ast_lowering::hir::{self, HirId};

use super::{types::{generics::GenericArgs, Type}};

pub mod check;
pub mod env;
mod ops;


#[derive(Clone,Debug)]
pub(super) enum Expectation{
    HasType(Type),
    CoercesTo(Type),
    None
}
impl Expectation{
    pub fn as_type(&self) -> Option<&Type>{
        if let Expectation::HasType(ty) | Expectation::CoercesTo(ty) = self{
            Some(ty)
        }
        else {
            None
        }
    }
}
#[derive(Debug)]
pub enum InferError{
    TypesNotEqual(Type,Type),

}


pub struct TypeCheckResults{
    pub expr_types : FxHashMap<HirId,Type>,
    pub generic_args : FxHashMap<HirId,GenericArgs>,
    pub resolutions : FxHashMap<HirId,hir::Resolution>
}
impl TypeCheckResults{
    pub fn new() -> Self{
        Self { expr_types: FxHashMap::default(), generic_args: FxHashMap::default(), resolutions: FxHashMap::default() }
    }
}