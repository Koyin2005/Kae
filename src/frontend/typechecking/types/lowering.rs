use crate::{
    errors::ErrorReporter, frontend::{
        ast_lowering::hir::{self, DefKind, GenericArg, Resolution},
        typechecking::{
            context::{FuncSig, GenericParam, TypeContext},
            types::{ArraySize, ConstantSize},
        },
    }, SymbolInterner
};

use super::{AdtKind, Type, format::TypeFormatter, generics::GenericArgs};

pub struct TypeLower<'a> {
    interner: &'a SymbolInterner,
    context: &'a TypeContext<'a>,
    self_type: Option<Type>,
    error_reporter: &'a ErrorReporter,
    ignore_methods: bool,
}
impl<'a> TypeLower<'a> {
    pub fn new(
        interner: &'a SymbolInterner,
        context: &'a TypeContext,
        self_type: Option<Type>,
        error_reporter: &'a ErrorReporter,
    ) -> Self {
        Self {
            interner,
            context,
            self_type,
            error_reporter,
            ignore_methods: false,
        }
    }
    pub fn new_with_ignore_methods(
        interner: &'a SymbolInterner,
        context: &'a TypeContext,
        self_type: Option<Type>,
        error_reporter: &'a ErrorReporter,
    ) -> Self {
        Self {
            interner,
            context,
            self_type,
            error_reporter,
            ignore_methods: true,
        }
    }
    pub fn lower_sig<'b>(
        &self,
        params: impl Iterator<Item = &'b hir::Type>,
        return_type: Option<&'b hir::Type>,
    ) -> FuncSig {
        FuncSig {
            params: params.map(|param| self.lower_type(param)).collect(),
            return_type: return_type
                .map(|return_type| self.lower_type(return_type))
                .unwrap_or_else(Type::new_unit),
        }
    }
    pub fn lower_generic_args(&self, generic_args: &[GenericArg]) -> GenericArgs {
        GenericArgs::new(
            generic_args
                .iter()
                .map(|arg| self.lower_type(&arg.ty))
                .collect(),
        )
    }
    pub fn lower_generic_args_of_path(&self, path: &hir::Path) -> GenericArgs {
        let generic_args = (|| {
            Some(match path.final_res {
                Resolution::None => {
                    let segment = path
                        .segments
                        .iter()
                        .rev()
                        .find(|segment| !matches!(segment.res, Resolution::None))?;
                    &segment.args
                }
                res @ Resolution::Definition(
                    DefKind::Function | DefKind::Struct | DefKind::Enum,
                    _,
                ) => {
                    let segment = path
                        .segments
                        .iter()
                        .rev()
                        .find(|segment| segment.res == res)?;
                    &segment.args
                }
                Resolution::Definition(DefKind::Variant, id) => {
                    let segment = path.segments.iter().rev().find(|segment|{
                            matches!(segment.res,Resolution::Definition(DefKind::Enum, seg_id) if seg_id == self.context.expect_owner_of(id))
                        })?;
                    &segment.args
                }
                Resolution::Definition(DefKind::Method, _) => {
                    unreachable!("Cannot access methods outside of type checking")
                }
                Resolution::Definition(DefKind::AnonFunction, _) => {
                    unreachable!("Cannot use anonymous functions at this point")
                }
                Resolution::Primitive(_)
                | Resolution::Variable(_)
                | Resolution::Definition(DefKind::Param|DefKind::ConstParam, _)
                | Resolution::SelfType(_)
                | Resolution::Builtin(_) => return None,
            })
        })();
        generic_args
            .map(|generic_args| self.lower_generic_args(generic_args))
            .unwrap_or_else(GenericArgs::new_empty)
    }
    fn lower_path(&self, path: &hir::Path) -> Type {
        match path.final_res {
            hir::Resolution::Primitive(ty) => match ty {
                hir::PrimitiveType::Int => Type::Int,
                hir::PrimitiveType::Bool => Type::Bool,
                hir::PrimitiveType::Float => Type::Float,
                hir::PrimitiveType::Never => Type::Never,
                hir::PrimitiveType::String => Type::String,
            },
            hir::Resolution::Definition(hir::DefKind::Enum, id) => {
                Type::Adt(self.lower_generic_args_of_path(path), id, AdtKind::Enum)
            }
            hir::Resolution::Definition(hir::DefKind::Struct, id) => {
                Type::Adt(self.lower_generic_args_of_path(path), id, AdtKind::Struct)
            }
            hir::Resolution::Definition(hir::DefKind::Param, id) => {
                let owner = self.context.expect_owner_of(id);
                let generics = self.context.expect_generics_for(owner);
                let index = generics
                    .id_to_index(id, self.context)
                    .expect("This should be a generic param");
                let GenericParam { id: _, name, index,kind:_ } =
                    generics.param_at(index as usize, self.context);
                Type::Param(index, name.index)
            },
            Resolution::Definition(DefKind::AnonFunction | DefKind::Method, _) => {
                unreachable!("These cannot be produced for a resolution before type checking")
            }
            Resolution::SelfType(_) => self
                .self_type
                .clone()
                .expect("Should always have a self type whenever Self appears"),
            Resolution::Builtin(_)
            | Resolution::Variable(_)
            | Resolution::None
            | Resolution::Definition(DefKind::Variant | DefKind::Function | hir::DefKind::ConstParam, _) => {
                self.error_reporter.emit(
                    format!("Cannot use '{}' as type.", path.format(self.interner)),
                    path.span,
                );
                Type::new_error()
            }
        }
    }

    pub fn lower_const_value(&self, expr: &hir::ConstantExpr) -> ConstantSize{
        match expr.kind{
            hir::ConstantExprKind::Int(value) => ConstantSize::Value(ArraySize(value)),
            hir::ConstantExprKind::Path(ref q_path) => {
                match q_path{
                    hir::QualifiedPath::TypeRelative(_,_) => {
                        self.error_reporter.emit(
                            format!("Cannot use '{}' as const.", q_path.format(self.interner)),
                            q_path.span(),
                        );
                        ConstantSize::Error
                    },
                    hir::QualifiedPath::FullyResolved(path) => {
                        match path.final_res {
                            Resolution::Definition(DefKind::ConstParam,id) => {
                                let owner = self.context.expect_owner_of(id);
                                let generics = self.context.expect_generics_for(owner);
                                let index = generics
                                    .id_to_index(id, self.context)
                                    .expect("This should be a generic param");
                                let GenericParam { id: _, name, index,kind:_ } =
                                    generics.param_at(index as usize, self.context);
                                ConstantSize::Constant(index, name.index)
                            },
                            _ => {
                                self.error_reporter.emit(
                                    format!("Cannot use '{}' as const.", path.format(self.interner)),
                                    q_path.span(),
                                );
                                ConstantSize::Error
                            }
                        }
                    }
                }
            }
        }
    }
    pub fn lower_type(&self, ty: &hir::Type) -> Type {
        match &ty.kind {
            hir::TypeKind::Array(element, size) => {
                Type::new_array(self.lower_type(element), self.lower_const_value(size))
            }
            hir::TypeKind::Function(params, return_type) => Type::new_function(
                params.iter().map(|param| self.lower_type(param)).collect(),
                return_type
                    .as_ref()
                    .map_or(Type::new_unit(), |ty| self.lower_type(ty)),
            ),
            hir::TypeKind::Tuple(elements) => Type::new_tuple(
                elements
                    .iter()
                    .map(|element| self.lower_type(element))
                    .collect(),
            ),
            hir::TypeKind::Path(path) => match path {
                hir::QualifiedPath::TypeRelative(ty, name) => {
                    let ty = self.lower_type(ty);
                    if ty.is_error() {
                        return Type::new_error();
                    }
                    if !self.ignore_methods {
                        self.error_reporter.emit(
                            format!(
                                "Cannot use member '{}' of '{}' as type.",
                                self.interner.get(name.ident.index),
                                TypeFormatter::new(self.interner, self.context).format_type(&ty)
                            ),
                            name.ident.span,
                        );
                    }
                    Type::new_error()
                }
                hir::QualifiedPath::FullyResolved(path) => self.lower_path(path),
            },
        }
    }
    /*Gets the indices of segments in the path taht are allowed to have generic arguments */
    pub fn get_generic_segments(&self, path: &hir::Path) -> Vec<usize> {
        let last = path.segments.len() - 1;
        match path.final_res {
            hir::Resolution::Definition(hir::DefKind::Variant, id) => {
                let segment = path.segments.iter().position(|segment| {
                    segment.res
                        == Resolution::Definition(
                            hir::DefKind::Enum,
                            self.context.expect_owner_of(id),
                        )
                });
                segment.into_iter().collect()
            }
            Resolution::Definition(DefKind::Method, _) => {
                unreachable!("Shouldn't be able to use methods in paths")
            }
            Resolution::Definition(DefKind::AnonFunction, _) => {
                unreachable!("Cannot use anonymous functions here")
            }
            hir::Resolution::Definition(
                hir::DefKind::Struct | hir::DefKind::Function | hir::DefKind::Enum,
                _,
            ) => {
                vec![last]
            }
            hir::Resolution::Builtin(_)
            | hir::Resolution::Primitive(_)
            | hir::Resolution::Variable(_)
            | hir::Resolution::None
            | hir::Resolution::SelfType(_)
            | hir::Resolution::Definition(hir::DefKind::Param | hir::DefKind::ConstParam, _) => {
                vec![]
            }
        }
    }
}
