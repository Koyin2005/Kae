use std::cell::RefCell;

use crate::{
    data_structures::IntoIndex, errors::ErrorReporter, frontend::{
        ast_lowering::hir::{self, DefId, DefIdMap, DefKind, HasSelfParam, Ident},
        tokenizing::SourceLocation,
        typechecking::types::{format::TypeFormatter, lowering::TypeLower, ConstantSize},
    }, identifiers::{FieldIndex, SymbolIndex, VariantIndex}, GlobalSymbols, SymbolInterner
};

use super::types::{
    AdtKind, Type,
    generics::GenericArgs,
    subst::{Subst, TypeSubst},
};
#[derive(Clone, Copy)]
pub struct FieldDef<'hir> {
    pub name: Ident,
    pub id: DefId,
    pub ty: &'hir hir::Type,
}
impl FieldDef<'_> {
    pub fn ty(&self, context: &TypeContext, generic_args: &GenericArgs) -> Type {
        context.type_of(self.id).bind(generic_args)
    }
    pub fn ty_unsubbed(&self, context: &TypeContext) -> Type {
        context.type_of(self.id).skip()
    }
}
pub struct StructDef<'hir> {
    pub name: Ident,
    pub generics: &'hir hir::Generics,
    pub fields: Vec<DefId>,
}
impl<'a> StructDef<'a> {
    pub fn field(&self, field_index: FieldIndex, context: &'a TypeContext) -> FieldDef<'a> {
        context.expect_field(self.fields[field_index.as_index()])
    }
    pub fn fields(&self, context: &'a TypeContext) -> impl ExactSizeIterator<Item = FieldDef<'a>> {
        self.fields.iter().map(|&field|{
            context.expect_field(field)
        })
    }
}
pub struct VariantDef {
    pub id: DefId,
    pub name: Ident,
    pub fields: Vec<DefId>,
}
impl VariantDef {
    pub fn field_ty<'a>(
        &'a self,
        field_index: FieldIndex,
        generic_args: &GenericArgs,
        context: &'a TypeContext,
    ) -> Type {
        context
            .type_of(
                context
                    .expect_variant_field(self.fields[field_index.as_index()])
                    .0,
            )
            .bind(generic_args)
    }
    pub fn field_tys<'a>(
        &'a self,
        generic_args: &GenericArgs,
        context: &'a TypeContext,
    ) -> impl ExactSizeIterator<Item = Type> {
        self.fields.iter().copied().map(move |field| {
            context
                .type_of(context.expect_variant_field(field).0)
                .bind(generic_args)
        })
    }
}
pub struct EnumDef<'hir> {
    pub name: Ident,
    pub generics: &'hir hir::Generics,
    pub variants: Vec<DefId>,
}
#[derive(Clone, Debug)]
pub struct FuncSig {
    pub params: Vec<Type>,
    pub return_type: Type,
}

impl FuncSig {
    pub fn as_type(&self) -> Type {
        Type::new_function(self.params.clone(), self.return_type.clone())
    }
}

pub struct GenericConstraint {
    pub span: SourceLocation,
}

pub struct Generics<'a> {
    pub parent: Option<DefId>,
    pub owner_id: DefId,
    pub parent_count: usize,
    pub params: Vec<GenericParam<'a>>,
}
impl<'a> Generics<'a> {
    pub fn own_count(&self) -> usize {
        self.params.len()
    }
    pub fn id_to_index(&self, id: DefId, context: &TypeContext) -> Option<u32> {
        self.params
            .iter()
            .find_map(|param| (param.id == id).then(|| param.index))
            .or_else(|| {
                self.parent
                    .and_then(|parent| context.expect_generics_for(parent).id_to_index(id, context))
            })
    }
    pub fn iter(&self, context: &'a TypeContext) -> impl Iterator<Item = GenericParam<'a>> {
        if let Some(parent) = self.parent {
            context
                .expect_generics_for(parent)
                .iter(context)
                .chain(self.params.iter().copied())
                .collect()
        } else {
            self.params.iter().copied().collect::<Vec<_>>()
        }
        .into_iter()
    }
    pub fn own_param_indices(&self) -> impl Iterator<Item = usize> {
        self.parent_count..self.parent_count + self.own_count()
    }
    pub fn param_at(&self, index: usize, context: &'a TypeContext) -> GenericParam<'a> {
        if index >= self.parent_count {
            self.params[index - self.parent_count]
        } else {
            context
                .expect_generics_for(self.parent.expect("parent_count is non-zero but no parent"))
                .param_at(index, context)
        }
    }
}

pub struct FunctionDef<'hir> {
    pub name: Ident,
    pub generics: &'hir hir::Generics,
    pub params: Vec<&'hir hir::Type>,
    pub return_ty: Option<&'hir hir::Type>,
}
pub struct Impl<'hir> {
    pub span: SourceLocation,
    pub ty: &'hir hir::Type,
    pub generics: &'hir hir::Generics,
    pub methods: Vec<DefId>,
}
pub enum TypeMember<'a> {
    Variant(DefId, GenericArgs, &'a VariantDef),
    Method {
        receiver_generic_args: GenericArgs,
        sig: FuncSig,
        id: DefId,
    },
}

pub enum Item<'hir> {
    Impl(Impl<'hir>),
    Struct(StructDef<'hir>),
    Enum(EnumDef<'hir>),
    Function(FunctionDef<'hir>),
}
impl Item<'_> {
    pub fn get_ident(&self) -> Option<Ident> {
        match self {
            Self::Struct(struct_def) => Some(struct_def.name),
            Self::Function(function_def) => Some(function_def.name),
            Self::Enum(enum_def) => Some(enum_def.name),
            Self::Impl(_) => None,
        }
    }
    pub fn expect_impl(&self) -> &Impl {
        let Item::Impl(impl_) = self else {
            unreachable!("Should be an impl")
        };
        impl_
    }
    pub fn expect_struct(&self) -> &StructDef {
        let Item::Struct(struct_) = self else {
            unreachable!("Should be a struct")
        };
        struct_
    }
    pub fn expect_enum(&self) -> &EnumDef {
        let Item::Enum(enum_) = self else {
            unreachable!("Should be an enum")
        };
        enum_
    }
    pub fn expect_function(&self) -> &FunctionDef {
        let Item::Function(function_def) = self else {
            unreachable!("Should be a function")
        };
        function_def
    }
}
#[derive(Clone,Debug,Copy)]
pub struct Unbound<T> {
    val: T,
}
impl<T> Unbound<T> {
    pub fn new(val: T) -> Self {
        Unbound { val }
    }
    pub fn skip(self) -> T {
        self.val
    }
    pub fn bind<U: Binder<T>>(self, binder: U) -> T {
        binder.bind(self)
    }
}

pub trait Binder<T> {
    fn bind(&self, unbound: Unbound<T>) -> T;
}
impl Binder<Type> for GenericArgs {
    fn bind(&self, unbound: Unbound<Type>) -> Type {
        TypeSubst::new(self).instantiate_type(&unbound.val)
    }
}
impl Binder<FuncSig> for GenericArgs {
    fn bind(&self, unbound: Unbound<FuncSig>) -> FuncSig {
        TypeSubst::new(self).instantiate_signature(&unbound.val)
    }
}
impl<'a, T, U> Binder<T> for &'a U
where
    U: Binder<T>,
{
    fn bind(&self, unbound: Unbound<T>) -> T {
        (*self).bind(unbound)
    }
}
#[derive(Clone, Copy)]
pub struct GenericParam<'a> {
    pub id: DefId,
    pub index: u32,
    pub name: Ident,
    pub kind : GenericParamKind<'a>
}
#[derive(Clone, Copy)]
pub enum GenericParamKind<'a> {
    Const(&'a hir::Type),
    Type
}
pub enum Node<'hir> {
    Item(Item<'hir>),
    Variant(VariantDef),
    Method(HasSelfParam, FunctionDef<'hir>),
    VariantField(DefId, &'hir hir::Type),
    Field(FieldDef<'hir>),
    Param(GenericParam<'hir>),
}
impl Node<'_> {
    pub fn generics(&self) -> Option<&hir::Generics> {
        match self {
            Self::Method(_, function) => Some(&function.generics),
            Self::Item(item) => match item {
                Item::Enum(enum_def) => Some(&enum_def.generics),
                Item::Function(function_def) => Some(&function_def.generics),
                Item::Struct(struct_def) => Some(&struct_def.generics),
                Item::Impl(impl_def) => Some(&impl_def.generics),
            },
            Self::Field(_) | Self::Variant(_) | Self::VariantField(..) | Self::Param(_) => None,
        }
    }
}

struct Cache{
    ty_map : DefIdMap<Unbound<Type>>,
    sig_map : DefIdMap<Unbound<FuncSig>>
}
pub struct TypeContext<'hir> {
    pub(super) nodes: DefIdMap<Node<'hir>>,
    pub(super) child_to_owner_map: DefIdMap<DefId>,
    pub(super) type_ids_to_method_impls: DefIdMap<Vec<DefId>>,
    pub(super) has_receiver: DefIdMap<bool>,
    pub(super) kinds: DefIdMap<DefKind>,
    cache : RefCell<Cache>,
    pub interner: &'hir SymbolInterner,
    pub reporter: &'hir ErrorReporter,
}
impl<'a> TypeContext<'a> {
    pub fn new(interner: &'a crate::SymbolInterner, error_reporter: &'a ErrorReporter) -> Self {
        Self {
            nodes: DefIdMap::new(),
            child_to_owner_map: DefIdMap::new(),
            type_ids_to_method_impls: DefIdMap::new(),
            cache : RefCell::new(Cache { ty_map: DefIdMap::new(), sig_map : DefIdMap::new() }),
            has_receiver: DefIdMap::new(),
            kinds: DefIdMap::new(),
            interner,
            reporter: error_reporter,
        }
    }
    pub fn signature_for(&self, id: DefId) -> Unbound<FuncSig>{
        if let Some(sig) = self.cache.borrow().sig_map.get(id){
            sig.clone()
        }
        else{
            signature_for(self, id)
        }
    }
    pub fn nodes(&self) -> impl Iterator<Item = (DefId,&Node)>{
        self.nodes.iter()
    }
    pub fn expect_node(&self, id: DefId) -> &Node {
        &self.nodes[id]
    }
    pub fn expect_item(&self, id: DefId) -> &Item {
        let Node::Item(item) = self.expect_node(id) else {
            unreachable!("Expected an item for this node")
        };
        item
    }
    pub fn expect_field(&self, id: DefId) -> FieldDef {
        let &Node::Field(field_def) = self.expect_node(id) else {
            unreachable!("Expected a field def")
        };
        field_def
    }
    pub fn expect_variant_field(&self, id: DefId) -> (DefId, &hir::Type) {
        let &Node::VariantField(_, ty) = self.expect_node(id) else {
            unreachable!("Expected a field def")
        };
        (id, ty)
    }
    pub fn get_member_ids(&self, ty: &Type, name: SymbolIndex) -> Vec<(hir::DefKind, DefId)> {
        let mut members = if let &Type::Adt(_, id, AdtKind::Enum) = ty {
            self.expect_enum(id)
                .variants
                .iter()
                .filter_map(|&variant| {
                    (self.ident(variant).index == name).then_some((hir::DefKind::Variant, variant))
                })
                .collect()
        } else {
            Vec::new()
        };

        members.extend(
            self.get_method_ids(ty).into_iter().filter_map(|id| {
                (self.ident(id).index == name).then_some((hir::DefKind::Method, id))
            }),
        );
        members
    }
    pub fn get_variant_ids(&self, ty: &Type) -> Vec<DefId> {
        if let &Type::Adt(_, id, AdtKind::Enum) = ty {
            self.expect_enum(id)
                .variants
                .iter()
                .map(|&variant| variant)
                .collect()
        } else {
            Vec::new()
        }
    }
    pub fn get_method_ids(&self, ty: &Type) -> Vec<DefId> {
        if let &Type::Adt(_, id, _) = ty {
            let Some(methods) = self.type_ids_to_method_impls.get(id) else {
                return Vec::new();
            };
            return methods.clone();
        }
        Vec::new()
    }
    pub fn ident(&self, id: DefId) -> Ident {
        self.get_ident(id).expect("There should be an ident")
    }
    pub fn get_ident(&self, id: DefId) -> Option<Ident> {
        match self.expect_node(id) {
            Node::Item(item) => item.get_ident(),
            Node::Field(field_def) => Some(field_def.name),
            Node::Method(_, function_def) => Some(function_def.name),
            Node::Variant(variant_def) => Some(variant_def.name),
            Node::VariantField(_, _) => None,
            Node::Param(param) => Some(param.name),
        }
    }
    pub fn expect_root_owner_id(&self, child: DefId) -> DefId {
        match self.expect_node(child) {
            Node::Field(_) | Node::Method(_, _) | Node::Param(_) | Node::Variant(_) => {
                self.expect_owner_of(child)
            }
            &Node::VariantField(id, _) => self.expect_owner_of(self.expect_owner_of(id)),
            _ => panic!("This node can never have a parent"),
        }
    }
    pub fn get_owner_of(&self, child: DefId) -> Option<DefId> {
        self.child_to_owner_map.get(child).copied()
    }
    pub fn expect_owner_of(&self, child: DefId) -> DefId {
        self.child_to_owner_map
            .get(child)
            .copied()
            .expect("There should be an owner for this child")
    }
    pub fn expect_generics_for(&self, owner_id: DefId) -> Generics {
        generics_for(self, owner_id)
    }
    pub fn get_variant_index(&self, variant_id: DefId) -> Option<VariantIndex> {
        self.get_owner_of(variant_id).and_then(|enum_id| {
            self.expect_enum(enum_id)
                .variants
                .iter()
                .position(|&variant| variant == variant_id)
                .map(VariantIndex::new)
        })
    }
    pub fn expect_enum(&self, enum_id: DefId) -> &EnumDef {
        self.expect_item(enum_id).expect_enum()
    }
    pub fn expect_struct(&self, struct_id: DefId) -> &StructDef {
        self.expect_item(struct_id).expect_struct()
    }
    pub fn expect_impl(&self, impl_id: DefId) -> &Impl {
        self.expect_item(impl_id).expect_impl()
    }
    pub fn expect_variant(&self, variant_id: DefId) -> &VariantDef {
        let Node::Variant(variant) = self.expect_node(variant_id) else {
            unreachable!("There should be a variant here")
        };
        variant
    }
    pub fn get_variant_of(&self, enum_id: DefId, name: SymbolIndex) -> Option<&VariantDef> {
        self.expect_enum(enum_id)
            .variants
            .iter()
            .find(|&&variant| self.ident(variant).index == name)
            .map(|&variant| self.expect_variant(variant))
    }
    pub fn get_generic_count(&self, res: &hir::Resolution) -> usize {
        match res {
            &hir::Resolution::Definition(
                hir::DefKind::Struct
                | hir::DefKind::Enum
                | hir::DefKind::Function
                | hir::DefKind::AnonFunction
                | hir::DefKind::Method,
                id,
            ) => self.expect_generics_for(id).own_count(),
            hir::Resolution::Variable(_)
            | hir::Resolution::Definition(
                hir::DefKind::Variant | hir::DefKind::Param | hir::DefKind::ConstParam,
                _,
            )
            | hir::Resolution::Primitive(_)
            | hir::Resolution::Builtin(hir::BuiltinKind::Panic)
            | hir::Resolution::SelfType(_)
            | hir::Resolution::None => 0,
        }
    }
    pub fn is_type_inhabited(&self, ty: &Type) -> bool {
        match ty {
            Type::Bool
            | Type::Error
            | Type::Float
            | Type::Int
            | Type::Param(_, _)
            | Type::String => true,
            Type::Function(_, _) => true,
            Type::Never => false,
            Type::Array(element_type, _) => self.is_type_inhabited(element_type),
            Type::Tuple(elements) => elements
                .iter()
                .all(|element| self.is_type_inhabited(element)),
            Type::Adt(args, id, kind) => match kind {
                AdtKind::Enum => {
                    let variants = self.expect_variants_for(*id);
                    if variants.is_empty() {
                        false
                    } else {
                        variants.iter().any(|&variant| {
                            self.get_variant_by_index(*id, variant)
                                .fields
                                .iter()
                                .all(|&field| {
                                    self.is_type_inhabited(&self.type_of(field).bind(args))
                                })
                        })
                    }
                }
                AdtKind::Struct => self
                    .expect_struct(*id)
                    .fields
                    .iter()
                    .all(|&field| self.is_type_inhabited(&self.type_of(field).bind(args))),
            },
        }
    }
    pub fn is_type_recursive(&self, ty: &Type, id: DefId) -> bool {
        match ty {
            Type::Int
            | Type::Float
            | Type::Bool
            | Type::String
            | Type::Error
            | Type::Never
            | Type::Param(_, _) => false,
            Type::Array(ty, size) => {
                if matches!(size,ConstantSize::Value(size) if size.is_zero()) {
                    false
                } else {
                    self.is_type_recursive(ty, id)
                }
            }
            Type::Function(_, _) => false,
            Type::Tuple(elements) => elements
                .iter()
                .any(|element| self.is_type_recursive(element, id)),
            &Type::Adt(ref generic_args, type_id, kind) => match kind {
                _ if type_id == id => true,
                AdtKind::Struct => self.expect_struct(type_id).fields.iter().any(|&field| {
                    self.is_type_recursive(&self.type_of(field).bind(generic_args), id)
                }),
                AdtKind::Enum => self.expect_enum(type_id).variants.iter().any(|variant| {
                    self.expect_variant(*variant)
                        .fields
                        .iter()
                        .any(|&field_id| {
                            self.is_type_recursive(&self.type_of(field_id).bind(generic_args), id)
                        })
                }),
            },
        }
    }
    pub fn get_member(&self, _: &GlobalSymbols, ty: &Type, member: Ident) -> Option<TypeMember> {
        self.get_member_ids(ty, member.index)
            .first()
            .copied()
            .map(|(kind, id)| match kind {
                hir::DefKind::Method => {
                    let (generic_args, _, _) = ty
                        .as_adt()
                        .expect("Only an adt can have a method on it (for now)");
                    TypeMember::Method {
                        receiver_generic_args: generic_args.clone(),
                        sig: self.signature_for(id).skip(),
                        id,
                    }
                }
                hir::DefKind::Variant => {
                    let (generic_args, _, _) = ty.as_adt().expect("Only an adt can have variants");
                    TypeMember::Variant(id, generic_args.clone(), self.expect_variant(id))
                }
                _ => unreachable!("Can only have a method or variant here"),
            })
    }
    pub fn get_variant_by_index(&self, enum_id: DefId, index: VariantIndex) -> &VariantDef {
        self.expect_variant(self.expect_enum(enum_id).variants[index.as_index()])
    }
    pub fn expect_variants(&self, enum_id: DefId) -> impl ExactSizeIterator<Item = &VariantDef> {
        self.expect_enum(enum_id)
            .variants
            .iter()
            .copied()
            .map(|variant| self.expect_variant(variant))
    }
    pub fn expect_variants_for(&self, enum_id: DefId) -> Vec<VariantIndex> {
        (0..self.expect_enum(enum_id).variants.len())
            .map(VariantIndex::new)
            .collect()
    }
    pub fn field_def(&self, struct_id: DefId, field_index: FieldIndex) -> FieldDef {
        self.expect_field(self.expect_struct(struct_id).fields[field_index.as_index()])
    }
    pub fn variant_fields(&self, variant_id: DefId) -> impl ExactSizeIterator<Item = DefId> {
        self.expect_variant(variant_id)
            .fields
            .iter()
            .copied()
            .map(|field| self.expect_variant_field(field).0)
    }
    pub fn field_defs(&self, struct_id: DefId) -> impl ExactSizeIterator<Item = FieldDef> {
        self.expect_struct(struct_id)
            .fields
            .iter()
            .copied()
            .map(|field| self.expect_field(field))
    }
    pub fn type_of(&self, id: DefId) -> Unbound<Type> {
        if let Some(ty) = self.cache.borrow().ty_map.get(id){
            ty.clone()
        }
        else{
            println!("Call me later {:?}",id);
            let ty = type_of(self, id);
            self.cache.borrow_mut().ty_map.insert(id, ty.clone());
            ty
        }
    }
    pub fn format_full_path(&self, id: DefId, interner: &crate::SymbolInterner) -> String {
        match self.kinds[id] {
            DefKind::AnonFunction => "<anonymous>".to_string(),
            DefKind::Struct
            | DefKind::Function
            | DefKind::Enum
            | DefKind::Param
            | DefKind::ConstParam => interner.get(self.ident(id).index).to_string(),
            DefKind::Method => {
                let impl_id = self.expect_owner_of(id);
                let ty = &self.type_of(impl_id).skip();
                format!(
                    "{}::{}",
                    TypeFormatter::new(interner, self).format_type(ty),
                    interner.get(self.ident(id).index)
                )
            }
            DefKind::Variant => {
                let enum_id = self.expect_owner_of(id);
                format!(
                    "{}::{}",
                    interner.get(self.ident(enum_id).index),
                    interner.get(self.ident(id).index)
                )
            }
        }
    }
    pub fn format_value_path(
        &self,
        id: DefId,
        generic_args: &GenericArgs,
        interner: &crate::SymbolInterner,
    ) -> String {
        match self.kinds[id] {
            DefKind::AnonFunction => "<anonymous>".to_string(),
            DefKind::Struct
            | DefKind::Function
            | DefKind::Enum
            | DefKind::Param
            | DefKind::ConstParam => {
                format!(
                    "{}{}",
                    interner.get(self.ident(id).index),
                    TypeFormatter::new(interner, self).format_generic_args(generic_args)
                )
            }
            DefKind::Method => {
                let impl_id = self.expect_owner_of(id);
                let ty = self.type_of(impl_id).bind(generic_args);
                let generic_args = self.identity_generic_args(id);
                let mut formatter = TypeFormatter::new(interner, self);
                format!(
                    "{}::{}{}",
                    formatter.format_type(&ty),
                    interner.get(self.ident(id).index),
                    formatter.format_generic_args(&generic_args)
                )
            }
            DefKind::Variant => {
                let enum_id = self.expect_owner_of(id);
                format!(
                    "{}{}::{}",
                    interner.get(self.ident(enum_id).index),
                    TypeFormatter::new(interner, self).format_generic_args(generic_args),
                    interner.get(self.ident(id).index)
                )
            }
        }
    }
    pub fn identity_generic_args(&self, id: DefId) -> GenericArgs {
        GenericArgs::new(
            self.expect_generics_for(id)
                .iter(self)
                .map(|param| Type::Param(param.index, param.name.index))
                .collect(),
        )
    }
}

fn type_of(context: &TypeContext, id: DefId) -> Unbound<Type> {
    let lower = TypeLower::new(context.interner, context, None, context.reporter);
    match context.expect_node(id) {
        Node::Item(item) => match item {
            Item::Struct(_) => {
                Unbound::new(Type::new_struct(context.identity_generic_args(id), id))
            }
            Item::Enum(_) => Unbound::new(Type::new_enum(context.identity_generic_args(id), id)),
            Item::Impl(impl_) => Unbound::new(lower.lower_type(impl_.ty)),
            Item::Function(function) => {
                let FuncSig {
                    params,
                    return_type,
                } = lower.lower_sig(function.params.iter().copied(), function.return_ty);
                Unbound::new(Type::new_function(params, return_type))
            }
        },
        Node::Field(field_def) => Unbound::new(lower.lower_type(field_def.ty)),
        Node::VariantField(_, ty) => Unbound::new(lower.lower_type(ty)),
        Node::Method(_, function) => {
            let FuncSig {
                params,
                return_type,
            } = lower.lower_sig(function.params.iter().copied(), function.return_ty);
            Unbound::new(Type::new_function(params, return_type))
        }
        Node::Param(param) => {
            Unbound::new(match param.kind{
                GenericParamKind::Const(ty) => lower.lower_type(ty),
                GenericParamKind::Type => Type::Param(param.index, param.name.index)
            })
        },
        Node::Variant(_) => unreachable!("There is no type for this node"),
    }
}

fn generics_for<'a>(context: &'a TypeContext, id: DefId) -> Generics<'a> {
    let node = context.expect_node(id);
    let parent = match node {
        Node::Field(_)
        | Node::Method(_, _)
        | Node::Param(_)
        | Node::Variant(_)
        | Node::VariantField(..) => Some(context.expect_root_owner_id(id)),
        _ => None,
    };
    let generics = node.generics();
    let parent_generics = parent.map(|parent| context.expect_generics_for(parent));
    let mut index = parent_generics.as_ref().map_or(0, |args| args.own_count());
    Generics {
        parent,
        owner_id: id,
        parent_count: index,

        params: generics.map_or(Vec::new(), |generics| {
            generics
                .params
                .iter()
                .map(|param| GenericParam {
                    id: param.1,
                    index: {
                        let old_index = index;
                        index += 1;
                        old_index as u32
                    },
                    name: param.0,
                    kind : if let Some(ty) = param.2.as_ref(){
                        GenericParamKind::Const(ty)
                    }
                    else{
                        GenericParamKind::Type
                    }
                })
                .collect()
        }),
    }
}

fn signature_for(context: &TypeContext, id: DefId) -> Unbound<FuncSig>{
    match context.expect_node(id){
        Node::Item(Item::Function(function_def)) => 
            Unbound::new(TypeLower::new(context.interner, context, None, context.reporter).lower_sig(function_def.params.iter().copied(), function_def.return_ty)),
        
        Node::Method(_,function_def) => {
            let parent = context.expect_owner_of(id);
            let self_ty = context.type_of(parent).skip();
            Unbound::new(TypeLower::new(context.interner, context, Some(self_ty), context.reporter).lower_sig(function_def.params.iter().copied(), function_def.return_ty))
        },
        Node::Item(_) | Node::Field(_) | Node::Param(_) | Node::Variant(_) | Node::VariantField(..) => unreachable!("This node can never have a signature")
    }
}
