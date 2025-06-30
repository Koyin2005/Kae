use fxhash::FxHashMap;

use crate::{
    frontend::ast_lowering::hir::{self, HirId},
    identifiers::FieldIndex,
};

use super::{
    context::FuncSig,
    types::{Type, generics::GenericArgs},
};

pub mod check;
pub mod env;
mod ops;

#[derive(Clone, Debug)]
pub(super) enum Expectation {
    HasType(Type),
    CoercesTo(Type),
    None,
}
impl Expectation {
    pub fn as_type(&self) -> Option<&Type> {
        if let Expectation::HasType(ty) | Expectation::CoercesTo(ty) = self {
            Some(ty)
        } else {
            None
        }
    }
}
#[derive(Debug)]
pub enum InferError {
    TypesNotEqual(Type, Type),
}

pub enum Coercion {
    NeverToAny(Type),
}

pub struct TypeCheckResults {
    pub node_types: FxHashMap<HirId, Type>,
    pub generic_args: FxHashMap<HirId, GenericArgs>,
    pub resolutions: FxHashMap<HirId, hir::Resolution>,
    pub fields: FxHashMap<HirId, FieldIndex>,
    pub signatures: FxHashMap<HirId, FuncSig>,
    pub coercions: FxHashMap<HirId, Coercion>,
}
impl TypeCheckResults {
    pub fn new() -> Self {
        Self {
            node_types: FxHashMap::default(),
            generic_args: FxHashMap::default(),
            resolutions: FxHashMap::default(),
            fields: FxHashMap::default(),
            signatures: FxHashMap::default(),
            coercions: FxHashMap::default(),
        }
    }
}
