use crate::{
    data_structures::IndexVec, errors::ErrorReporter, frontend::{
        ast_lowering::hir::{BodyOwner, DefId, DefKind, Generics, Hir, Item},
        typechecking::context::{
            self, EnumDef, FieldDef, FunctionDef, GenericParam, GenericParamKind, Impl, Node, StructDef, TypeContext, VariantDef
        },
    }, identifiers::ItemIndex, GlobalSymbols, SymbolInterner
};

pub struct ItemCollector<'a> {
    context: TypeContext<'a>,
    next_param_index: u32,
    items: &'a IndexVec<ItemIndex, Item>,
    hir: &'a Hir,
}

impl<'a> ItemCollector<'a> {
    pub fn new(
        symbol_interner: &'a SymbolInterner,
        _symbols: &'a GlobalSymbols,
        items: &'a IndexVec<ItemIndex, Item>,
        hir: &'a Hir,
        error_reporter: &'a ErrorReporter,
    ) -> Self {
        Self {
            context: TypeContext::new(symbol_interner, error_reporter),
            next_param_index: 0,
            items,
            hir,
        }
    }
    fn add_kind(&mut self, id: DefId, kind: DefKind) {
        self.context.kinds.insert(id, kind);
    }
    fn add_child_for(&mut self, parent: DefId, child: DefId) {
        self.context.child_to_owner_map.insert(child, parent);
    }
    fn collect_generic_params(&mut self, owner: DefId, generic_params: &'a Generics) {
        for param in generic_params.params.iter() {
            self.add_node(
                param.1,
                Node::Param(GenericParam {
                    id: param.1,
                    index: self.next_param_index,
                    name: param.0,
                    kind : param.2.as_ref().map(|ty|{
                        GenericParamKind::Const(ty)   
                    }).unwrap_or(GenericParamKind::Type)
                }),
            );
            self.add_kind(
                param.1,
                if param.2.is_some() {
                    DefKind::ConstParam
                } else {
                    DefKind::Param
                },
            );
            self.add_child_for(owner, param.1);
            self.next_param_index += 1;
        }
    }
    fn add_node(&mut self, id: DefId, node: Node<'a>) {
        self.context.nodes.insert(id, node);
    }
    fn collect_item(&mut self, item: &'a Item) {
        match item {
            Item::Struct(struct_def) => {
                let name = struct_def.name;
                let generics = &struct_def.generics;
                self.collect_generic_params(struct_def.id, &struct_def.generics);
                let fields = struct_def
                    .fields
                    .iter()
                    .map(|field| {
                        self.add_child_for(struct_def.id, field.id);
                        self.add_node(
                            field.id,
                            Node::Field(FieldDef {
                                name: field.name,
                                id: field.id,
                                ty: &field.ty,
                            }),
                        );
                        field.id
                    })
                    .collect();
                self.add_node(
                    struct_def.id,
                    Node::Item(context::Item::Struct(StructDef {
                        name,
                        generics,
                        fields,
                    })),
                );
                self.add_kind(struct_def.id, DefKind::Struct);
            }
            Item::Enum(enum_def) => {
                let name = enum_def.name;
                let generics = &enum_def.generics;
                self.collect_generic_params(enum_def.id, &enum_def.generics);
                let variants = enum_def
                    .variants
                    .iter()
                    .map(|variant_def| {
                        self.add_child_for(enum_def.id, variant_def.id);
                        let fields = variant_def
                            .fields
                            .iter()
                            .map(|field| {
                                self.add_child_for(variant_def.id, field.id);
                                self.add_node(field.id, Node::VariantField(field.id, &field.ty));
                                field.id
                            })
                            .collect();
                        self.add_node(
                            variant_def.id,
                            Node::Variant(VariantDef {
                                id: variant_def.id,
                                name: variant_def.name,
                                fields,
                            }),
                        );
                        self.add_kind(variant_def.id, DefKind::Variant);
                        variant_def.id
                    })
                    .collect();
                self.add_node(
                    enum_def.id,
                    Node::Item(context::Item::Enum(EnumDef {
                        name,
                        generics,
                        variants,
                    })),
                );
                self.add_kind(enum_def.id, DefKind::Enum);
            }
            Item::Impl(impl_) => {
                self.collect_generic_params(impl_.id, &impl_.generics);
                let methods = impl_
                    .methods
                    .iter()
                    .map(|&(has_self_param, ref method)| {
                        let name = method.name;
                        let generics = &method.generics;
                        let prev_param_index = self.next_param_index;
                        self.collect_generic_params(impl_.id, &method.generics);
                        let params = method.function.params.iter().map(|param| param).collect();
                        let return_ty = method.function.return_type.as_ref();
                        self.add_child_for(impl_.id, method.id);
                        self.add_node(
                            method.id,
                            Node::Method(
                                has_self_param,
                                FunctionDef {
                                    name,
                                    generics,
                                    params,
                                    return_ty,
                                },
                            ),
                        );
                        self.add_kind(method.id, DefKind::Method);
                        self.next_param_index = prev_param_index;

                        method.id
                    })
                    .collect();
                self.add_node(
                    impl_.id,
                    Node::Item(context::Item::Impl(Impl {
                        span: impl_.span,
                        ty: &impl_.ty,
                        generics: &impl_.generics,
                        methods,
                    })),
                );
            }
            Item::Function(function_def) => {
                let name = function_def.name;
                let generics = &function_def.generics;
                self.collect_generic_params(function_def.id, &function_def.generics);
                let params = function_def
                    .function
                    .params
                    .iter()
                    .map(|param| param)
                    .collect();
                let return_ty = function_def.function.return_type.as_ref();
                self.add_node(
                    function_def.id,
                    Node::Item(context::Item::Function(FunctionDef {
                        name,
                        generics,
                        params,
                        return_ty,
                    })),
                );
                self.add_kind(function_def.id, DefKind::Function);
            }
        }
    }
    pub fn collect(mut self) -> TypeContext<'a> {
        for item in self.items.iter() {
            self.collect_item(item);
            self.next_param_index = 0;
        }
        for owner in self.hir.body_owners.iter() {
            if let BodyOwner::AnonFunction(id) = owner {
                self.add_kind(*id, DefKind::AnonFunction);
            }
        }
        self.context
    }
}
