use std::collections::VecDeque;

use fxhash::FxBuildHasher;
use generics::GenericArgs;
use indexmap::IndexMap;

use crate::{
    data_structures::IntoIndex,
    frontend::{
        ast_lowering::hir::DefId,
        typechecking::{
            context::TypeContext,
            types::subst::{Subst, TypeSubst},
        },
    },
    identifiers::{FieldIndex, SymbolIndex},
};

pub mod collect;
pub mod format;
pub mod generics;
pub mod lowering;
pub mod subst;
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AdtKind {
    Struct,
    Enum,
}
#[derive(Clone, Copy,Debug,PartialEq,Eq,Hash,PartialOrd,Ord)]
pub struct ArraySize(u64);
impl ArraySize{
    pub const ZERO : Self = Self(0);
    pub fn is_zero(self) -> bool{
        self == Self::ZERO
    }
    pub fn new(value: usize) -> Self{
        Self(value.try_into().expect("Can't convert to a usize"))
    }
    pub fn into_size(self) -> usize{
        self.0.try_into().expect("Can't convert to a usize")
    }
}
impl From<usize> for ArraySize{
    fn from(value: usize) -> Self {
        ArraySize(value.try_into().expect("Can't convert usize into u64"))
    }
}
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Type {
    Int,
    Float,
    Bool,
    String,
    Never,
    Error,
    Param(u32, SymbolIndex),
    Function(Vec<Type>, Box<Type>),
    Array(Box<Type>,ArraySize),
    Tuple(Vec<Type>),
    Adt(GenericArgs, DefId, AdtKind),
}
impl Type {
    pub fn iter(&self) -> TypeIterator {
        TypeIterator {
            ty: VecDeque::from([self]),
        }
    }
    pub fn get_substitution<'a>(
        &'a self,
        other: &'a Self,
    ) -> Option<IndexMap<u32, &'a Self, FxBuildHasher>> {
        match (self, other) {
            (&Self::Param(index, _), ty) => Some(vec![(index, ty)].into_iter().collect()),
            (
                Self::Function(params, return_type),
                Self::Function(other_params, other_return_type),
            ) => {
                if params.len() != other_params.len() {
                    return None;
                };
                let mut subst = IndexMap::default();
                for (ty, other) in params.iter().zip(other_params.iter()) {
                    for (index, ty) in ty.get_substitution(other)? {
                        subst.entry(index).or_insert(ty);
                    }
                }
                for (index, ty) in return_type.get_substitution(other_return_type)? {
                    subst.entry(index).or_insert(ty);
                }
                Some(subst)
            }
            (
                Self::Adt(generic_args, id, kind),
                Self::Adt(other_generic_args, other_id, other_kind),
            ) => {
                if id != other_id
                    || kind != other_kind
                    || generic_args.len() != other_generic_args.len()
                {
                    return None;
                }
                let mut subst = IndexMap::default();
                for (arg, other_arg) in generic_args.iter().zip(other_generic_args.iter()) {
                    for (index, ty) in arg.get_substitution(other_arg)? {
                        subst.entry(index).or_insert(ty);
                    }
                }
                Some(subst)
            }
            (Self::Tuple(fields), Self::Tuple(other_fields)) => {
                if fields.len() != other_fields.len() {
                    return None;
                }
                let mut subst = IndexMap::default();
                for (field, other_field) in fields.iter().zip(other_fields.iter()) {
                    for (index, ty) in field.get_substitution(other_field)? {
                        subst.entry(index).or_insert(ty);
                    }
                }
                Some(subst)
            }
            (Self::Array(elements,self_size), Self::Array(other_elements,other_size)) if self_size == other_size => {
                elements.get_substitution(other_elements)
            }
            (ty, other_ty) => {
                if ty == other_ty {
                    Some(IndexMap::default())
                } else {
                    None
                }
            }
        }
    }
    pub fn get_generic_args(&self) -> Option<&GenericArgs> {
        match self {
            Self::Adt(args, _, _) => Some(args),
            _ => None,
        }
    }
    pub fn as_adt(&self) -> Option<(&GenericArgs, DefId, AdtKind)> {
        match self {
            &Self::Adt(ref generic_args, id, kind) => Some((generic_args, id, kind)),
            _ => None,
        }
    }
    pub fn new_struct(args: GenericArgs, id: DefId) -> Self {
        Self::Adt(args, id, AdtKind::Struct)
    }
    pub fn new_adt(args: GenericArgs, id: DefId, kind: AdtKind) -> Self {
        Self::Adt(args, id, kind)
    }
    pub fn new_enum(args: GenericArgs, id: DefId) -> Self {
        Self::Adt(args, id, AdtKind::Enum)
    }
    pub fn new_unit() -> Self {
        Self::Tuple(vec![])
    }
    pub fn new_function(params: Vec<Self>, return_type: Self) -> Self {
        Self::Function(params, Box::new(return_type))
    }
    pub fn new_tuple(elements: Vec<Self>) -> Self {
        Self::Tuple(elements)
    }
    pub fn new_array(element: Self, size: ArraySize) -> Self {
        Self::Array(Box::new(element),size)
    }
    pub fn new_error() -> Self {
        Type::Error
    }
    pub fn is_enum(&self) -> bool {
        matches!(&self, Type::Adt(_, _, AdtKind::Enum))
    }
    pub fn is_error(&self) -> bool {
        matches!(&self, Type::Error)
    }
    pub fn has_error(&self) -> bool {
        self.iter().any(|ty| ty.is_error())
    }
    pub fn is_never(&self) -> bool {
        matches!(&self, Type::Never)
    }
    pub fn is_unit(&self) -> bool {
        matches!(&self,Type::Tuple(elements) if elements.is_empty())
    }
    pub fn index_of(&self) -> Option<Type> {
        match self {
            Self::Array(element_type,_) => Some(*element_type.clone()),
            _ => None,
        }
    }
    pub fn def_id(&self) -> Option<DefId> {
        match self {
            Self::Adt(_, id, _) => Some(*id),
            _ => None,
        }
    }
    pub fn field(&self, ctxt: &TypeContext, field_index: FieldIndex) -> Option<Type> {
        match self {
            Self::Adt(args, id, AdtKind::Struct) => Some(
                TypeSubst::new(args)
                    .instantiate_type(&ctxt.field_defs(*id)[field_index.as_index()].ty),
            ),
            Self::Tuple(elements) => elements.get(field_index.as_index()).cloned(),
            _ => None,
        }
    }
}

pub struct TypeIterator<'a> {
    ty: VecDeque<&'a Type>,
}

impl<'a> Iterator for TypeIterator<'a> {
    type Item = &'a Type;
    fn next(&mut self) -> Option<Self::Item> {
        match self.ty.pop_front() {
            Some(ty) => {
                match ty {
                    Type::Function(params, return_type) => {
                        self.ty.extend(params);
                        self.ty.push_back(return_type);
                    }
                    Type::Adt(generic_args, _, _) => {
                        self.ty.extend(generic_args.iter());
                    }
                    Type::Tuple(elements) => {
                        self.ty.extend(elements);
                    }
                    Type::Array(ty,_) => {
                        self.ty.push_back(ty);
                    }
                    _ => {}
                }
                Some(ty)
            }
            None => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Type;

    #[test]
    fn test_func() {
        let ty = Type::Tuple(vec![
            Type::Int,
            Type::Function(Vec::new(), Box::new(Type::Bool)),
        ]);
        let mut iter = ty.iter();
        assert_eq!(
            iter.next(),
            Some(&Type::Tuple(vec![
                Type::Int,
                Type::Function(Vec::new(), Box::new(Type::Bool))
            ]))
        );
        assert_eq!(iter.next(), Some(&Type::Int));
        assert_eq!(
            iter.next(),
            Some(&Type::Function(Vec::new(), Box::new(Type::Bool)))
        );
        assert_eq!(iter.next(), Some(&Type::Bool));
    }
}
