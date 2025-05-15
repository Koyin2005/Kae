use std::cell::{Cell, RefCell};
use fxhash::{FxBuildHasher, FxHashMap, FxHashSet};
use indexmap::{IndexMap, IndexSet};
use crate::{
    data_structures::IndexVec, 
    frontend::{
        ast_lowering::hir::{self, DefId, DefIdMap, HirId, Ident}, 
        tokenizing::SourceLocation, 
        typechecking::{context::{FuncSig, Generics, TypeContext, TypeMember}, error::TypeError, types::{format::TypeFormatter, generics::GenericArgs, lowering::TypeLower, subst::{SelfTypeSubst, Subst, TypeSubst}, AdtKind, Type}}
    }, 
    identifiers::{GlobalSymbols, ItemIndex, SymbolIndex, SymbolInterner}
};
use super::{env::{SelfType, TraitConstraint, TypeEnv}, Expectation};
struct FuncContext{
    return_type : Type
}

struct MethodLookup<'a>{
    generic_params : Option<&'a Generics>,
    base_generic_args : GenericArgs,
    sig : FuncSig,
    has_receiver : bool,
    id : Option<DefId>
}
pub struct TypeChecker<'a>{
    node_types : RefCell<FxHashMap<HirId,Type>>,
    env : TypeEnv,
    had_error : Cell<bool>,
    prev_functions : RefCell<Vec<FuncContext>>,
    context : &'a TypeContext,
    ident_interner : &'a SymbolInterner,
    items : &'a IndexVec<ItemIndex,hir::Item>,
    symbols:&'a GlobalSymbols,
    _item_map:&'a DefIdMap<ItemIndex>,
}
impl<'a> TypeChecker<'a>{
    pub fn new(context:&'a TypeContext,items:&'a IndexVec<ItemIndex,hir::Item>,symbols:&'a GlobalSymbols,_item_map:&'a DefIdMap<ItemIndex>,interner:&'a SymbolInterner) -> Self{
        Self { 
            node_types : RefCell::new(FxHashMap::default()),
            env : TypeEnv::new(),
            had_error : Cell::new(false),
            prev_functions : RefCell::new(Vec::new()),
            context,
            _item_map,
            items,
            ident_interner: interner,
            symbols,
        }
    }
    pub(super) fn lowerer(&self) -> TypeLower{
        TypeLower::new(&self.ident_interner,self.context,self.env.get_self_type().and_then(|self_ty| self_ty.as_ty()).cloned())
    }
    pub(super) fn lower_type(&self,ty: &hir::Type) -> Type{
        self.lowerer().lower_type(ty)
    }
    pub(super) fn format_type(&self,ty: &Type) -> String{
        TypeFormatter::new(&*self.ident_interner, &*self.context).format_type(ty)
    }
    fn store_type(&self,id: HirId,ty: Type){
        self.node_types.borrow_mut().insert(id, ty);
    }
    fn error(&self,msg:String,span : SourceLocation){
        self.had_error.set(true);
        TypeError.emit(msg, span);
    }

    pub(super) fn new_error(&self,msg:String,span : SourceLocation) -> Type{
        self.error(msg, span);
        Type::new_error()
    }
    fn check_impls(&self) {
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
    }
    pub fn check(mut self,stmts : &[hir::Stmt]) -> Result<(),TypeError>{
        self.check_impls();
        self.check_stmts(stmts);
        if !self.had_error.get(){
            Ok(())
        }
        else{
            Err(TypeError)
        }
    }
    fn check_stmts(&mut self,stmts : &[hir::Stmt]){
        for stmt in stmts{
            self.check_stmt(stmt);
        }
    }
    fn check_type(&mut self,ty:&hir::Type){
        match &ty.kind{
            hir::TypeKind::Array(ty) => self.check_type(ty),
            hir::TypeKind::Tuple(elements) => elements.iter().for_each(|element| self.check_type(element)),
            hir::TypeKind::Function(params,return_type) => {
                params.iter().for_each(|param| self.check_type(param));
                if let Some(return_type) = return_type.as_ref(){
                    self.check_type(return_type);
                }
            },
            hir::TypeKind::Path(path) => {
                self.check_path(path);
            }
        }
    }
    fn check_function<'b>(&mut self,sig:&FuncSig,param_patterns:impl Iterator<Item = (&'b hir::Pattern,&'b hir::Type)>,body:Option<&hir::Expr>){
        let FuncSig { params:param_types, return_type } = sig;
        for ((param_pattern,ty),param_ty) in param_patterns.zip(param_types){
            self.check_pattern(param_pattern, param_ty.clone());
            self.check_type(ty);
        }
        self.prev_functions.borrow_mut().push(FuncContext { return_type: return_type.clone() });
        if let Some(body) = body{
            self.check_expr(body, Expectation::CoercesTo(return_type.clone()));
        }
        self.prev_functions.borrow_mut().pop();

    }
    fn is_type_recursive(&self,ty:&Type,id:DefId)->bool{
        match ty{
            Type::Int | Type::Float | Type::Bool | Type::String | Type::Error | Type::Never | Type::Param(_,_) | Type::SelfAlias(_) => false,
            Type::Function(_,_) | Type::Array(_) => false,
            Type::Tuple(elements) => {
                elements.iter().any(|element| self.is_type_recursive(element, id))
            },
            &Type::Adt(ref generic_args,type_id, kind) => {
                match kind{
                    _ if type_id == id => true,
                    AdtKind::Struct => {
                        self.context.structs[type_id].fields.iter().any(|field|{
                            self.is_type_recursive(&TypeSubst::new(generic_args).instantiate_type(&field.ty), id)
                        })
                    },
                    AdtKind::Enum => {
                        self.context.enums[type_id].variants.iter().any(|variant|{
                            variant.fields.iter().any(|field|{
                                self.is_type_recursive(&TypeSubst::new(generic_args).instantiate_type(&field.ty), id)
                            })
                        })
                    }
                }
            }
        }
    }
    fn check_generic_constraints(&mut self,id: DefId){
        let constraints = self.context.expect_generic_constraints(id);
        for constraint in constraints{
            if let Some(constraint) = constraint{
                match self.context.as_trait_with_span(constraint){
                    (Some(trait_),_) => {
                        let generic_args = self.lowerer().get_generic_args(constraint);
                        self.env.add_generic_constraint(Some(TraitConstraint { id: trait_, generic_args: generic_args.unwrap_or(GenericArgs::new_empty()) }));
                    },
                    (None,span) => {
                        self.error(format!("Cannot use non trait '{}' as generic constraint.",constraint.format(self.ident_interner)), span);
                        self.env.add_generic_constraint(None);
                    }
                }
            }
            else{
                self.env.add_generic_constraint(None);
            }
        }
    }
    fn check_item(&mut self,item:ItemIndex){
        let count = self.env.generic_constraint_count();
        match &self.items[item]{
            hir::Item::Struct(struct_def) => {
                self.check_generic_constraints(struct_def.id);
                let mut repeated_fields = Vec::new();
                let mut seen_fields = FxHashSet::default();
                let mut is_recursive = false;
                for (i,field) in struct_def.fields.iter().enumerate(){
                    if !seen_fields.insert(field.name.index){
                        repeated_fields.push(field.name);
                    }
                    self.check_type(&field.ty);
                    if self.is_type_recursive(&self.context.structs[struct_def.id].fields[i].ty, struct_def.id){
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
                self.check_generic_constraints(function.id);
                let sig = (&self.context.functions[function.id].sig).clone();
                self.check_function(&sig,  function.function.params.iter().map(|param| (&param.pattern,&param.ty)),Some(&function.function.body));
            },
            hir::Item::Enum(enum_def) => {
                self.check_generic_constraints(enum_def.id);
                for (i,variant) in enum_def.variants.iter().enumerate(){
                    let mut repeated_fields = Vec::new();
                    let mut seen_fields = FxHashSet::default();
                    let mut is_recursive = false;
                    for (j,field) in variant.fields.iter().enumerate(){
                        if !seen_fields.insert(field.name.index){
                            repeated_fields.push(field.name);
                        }
                        self.check_type(&field.ty);
                        if self.is_type_recursive(&self.context.enums[enum_def.id].variants[i].fields[j].ty, enum_def.id){
                            is_recursive = true;
                        }
                    }
                    if is_recursive{
                        self.error(format!("Recursive type '{}'.",self.ident_interner.get(enum_def.name.index)),enum_def.name.span);
                    }
                    for field in repeated_fields{
                        self.error(format!("Repeated field '{}'.",self.ident_interner.get(field.index)),field.span);
                    }
                }
            },
            &hir::Item::Impl(id,ref ty,ref _generics,ref methods,ref trait_path) => {
                self.check_generic_constraints(id);
                self.check_type(ty);
                let impl_ = &self.context.impls[id];
                let self_ty = self.lower_type(ty);
                let old_self_type = self.env.set_self_type(Some(SelfType::Ty(self_ty)));
                if let Some(path) = trait_path{
                    self.check_path(path);
                    let (trait_,span) = self.context.as_trait_with_span(path);
                    if let Some(trait_) = trait_{
                        let trait_methods : IndexSet<SymbolIndex,FxBuildHasher> = self.context.traits[trait_].methods.iter().copied().filter_map(|method|{
                            (!method.has_default_impl).then_some(self.context.ident(method.id).index)
                        }).collect();
                        let mut method_spans : IndexMap<SymbolIndex,SourceLocation,FxBuildHasher> = IndexMap::default();
                        let methods : IndexSet<SymbolIndex,FxBuildHasher> = impl_.methods.iter().copied().map(|method| {
                            let name = self.context.ident(method);
                            method_spans.insert(name.index,name.span);
                            name.index
                        }).collect();
                        for &method_name in trait_methods.difference(&methods){
                            let span = method_spans.get(&method_name).copied().unwrap_or(impl_.span);
                            self.error(format!("Missing implementation of method '{}' for trait '{}'.",self.ident_interner.get(method_name),self.ident_interner.get(self.context.ident(trait_).index)), span);
                        }
                    }
                    else{
                        let self_ty = self.lower_type(ty);
                        self.error(format!("Cannot implement '{}' for '{}'.",path.format(self.ident_interner), self.format_type(&self_ty)),span);
                    }
                }
                for (method_def,method) in methods.iter().zip(impl_.methods.iter().map(|&id| &self.context.methods[id])){
                    let old_count = count;
                    self.check_generic_constraints(method_def.id);
                    self.check_function(&method.sig,  method_def.function.params.iter().map(|param| (&param.pattern,&param.ty)),Some(&method_def.function.body));
                    self.env.truncate_generic_constraints(old_count);
                }
                self.env.set_self_type(old_self_type);
            },
            hir::Item::Trait(trait_) => {

                let old_self_type = self.env.set_self_type(Some(SelfType::Trait(TraitConstraint{
                    id:trait_.id,
                    generic_args : GenericArgs::new(trait_.generics.params.iter().enumerate().map(|(i,param)|{
                        Type::Param(i as u32, param.0.index)
                    }).collect())
                })));
                for (method_def,method) in trait_.methods.iter().zip(self.context.traits[trait_.id].methods.iter().map(|&method| &self.context.methods[method.id])){
                    let old_count = count;
                    self.check_generic_constraints(method_def.id);
                    self.check_function(&method.sig,  method_def.params.iter().map(|param| (&param.pattern,&param.ty)),method_def.body.as_ref());
                    self.env.truncate_generic_constraints(old_count);
                }
                self.env.set_self_type(old_self_type);
                
            }
        }
        self.env.truncate_generic_constraints(count);
    }
    fn check_stmt(&mut self,stmt : &hir::Stmt) {
        match &stmt.kind{
            hir::StmtKind::Expr(expr) => {
                self.check_expr(expr, Expectation::CoercesTo(Type::new_unit()));

            },
            hir::StmtKind::Semi(expr) => {
                self.check_expr(expr, Expectation::None);
            },
            hir::StmtKind::Let(pattern,ty,expr) => {
                let ty = ty.as_ref().map(|ty| {
                    
                    self.check_type(ty);
                    self.lower_type(&ty)
                });
                let expr_ty = self.check_expr(expr, ty.as_ref().map_or(
                    Expectation::None,
                    |ty|{
                        Expectation::CoercesTo(ty.clone())
                    })
                );
                let ty = if let Some(ty) = (expr_ty.has_error() || expr_ty.is_never()).then_some(ty).flatten(){
                    ty
                }
                else{
                    expr_ty
                };
                self.check_pattern(pattern,ty);
                
            }
            &hir::StmtKind::Item(item) => {
                self.check_item(item);
            },
        }
    }
    fn check_pattern(&mut self,pattern : &hir::Pattern, expected_type : Type){
        let ty = match &pattern.kind{
            &hir::PatternKind::Binding(variable, _,ref binding_pattern) => {
                self.env.define_variable_type(variable, expected_type.clone());
                if let Some(pattern) = binding_pattern.as_ref(){
                    self.check_pattern(pattern, expected_type.clone());
                }
                expected_type
            },
            hir::PatternKind::Tuple(elements) => {
                let element_types = if let Type::Tuple(element_types) = &expected_type{
                    element_types.clone()
                }
                else{
                    let expected_tuple = self.format_type(&Type::new_tuple(vec![Type::new_error();elements.len()]));
                    let expected_ty = self.format_type(&expected_type);
                    self.error(format!("Expected a '{}' got '{}'.",expected_tuple,expected_ty),pattern.span);
                    Vec::new()
                };
                let mut element_iter = element_types.into_iter();
                for pattern in elements.iter(){
                    self.check_pattern(pattern, element_iter.next().unwrap_or_else(|| Type::new_error()));
                }
                expected_type
            },
            hir::PatternKind::Wildcard => expected_type,
            hir::PatternKind::Literal(literal) => {
                let literal_ty = match literal{
                    hir::LiteralKind::Bool(_) => Type::Bool,
                    hir::LiteralKind::Float(_) => Type::Float,
                    hir::LiteralKind::Int(_) => Type::Int,
                    hir::LiteralKind::String(_) => Type::String
                };
                self.check_type_is_expected(literal_ty, &expected_type, pattern.span)
            },
            hir::PatternKind::Struct(path, fields) => {
                if let hir::InferOrPath::Path(path) = path{
                    self.check_path(path);
                }
                let (generic_args,Some((constructor_kind,id))) = self.get_constructor_with_generic_args(path,Some(&expected_type)) else{
                    self.error(if let hir::InferOrPath::Path(path) = path { format!("Cannot use '{}' as constructor.",path.format(self.ident_interner))} else { format!("Cannot infer type of constructor.")},pattern.span);
                    return;
                };
                let type_id = match constructor_kind{
                    AdtKind::Enum => self.context.expect_owner_of(id),
                    AdtKind::Struct => id
                };
                let field_tys = match constructor_kind{
                    AdtKind::Struct => self.context.structs[id].fields.iter().map(|field|{
                        (field.name.index,field.ty.clone())
                    }).collect::<FxHashMap<SymbolIndex,Type>>(),
                    AdtKind::Enum => {
                        self.context.enums[self.context.expect_owner_of(id)].variants.iter().find(|variant| variant.id == id).expect("Should definitely be a variant with this id").fields.iter().map(|field|{
                            (field.name.index,field.ty.clone())
                        }).collect()
                    }
                };
                let mut seen_fields = FxHashSet::default();
                let mut last_field_span = pattern.span;
                for field_pattern in fields{
                    let field_ty= match field_tys.get(&field_pattern.name.index).map(|ty| TypeSubst::new(&generic_args).instantiate_type(ty)){
                        Some(ty) => ty,
                        None => {
                            self.new_error(format!("Unkown field '{}'.",self.ident_interner.get(field_pattern.name.index)), field_pattern.name.span)
                        }
                    };
                    if !seen_fields.insert(field_pattern.name.index){
                        self.error(format!("Repeated field '{}'.",self.ident_interner.get(field_pattern.name.index)), field_pattern.name.span);
                    }
                    self.check_pattern(&field_pattern.pattern, field_ty);
                    last_field_span = field_pattern.name.span;
                }
                let field_names = field_tys.into_keys().collect::<FxHashSet<_>>();
                let missing_fields = field_names.difference(&seen_fields);
                for &field in missing_fields.into_iter(){
                    self.error(format!("Missing field pattern for field '{}'.",self.ident_interner.get(field)), last_field_span);
                }
                match constructor_kind{
                    AdtKind::Enum => Type::new_enum(generic_args,type_id),
                    AdtKind::Struct => Type::new_struct(generic_args, type_id)
                }

            }
        };
        self.store_type(pattern.id, ty);
    }
    fn check_type_is_expected(&self, ty : Type, expected_type : &Type, span : SourceLocation) -> Type{
        self.check_type_equals_with(ty, expected_type.clone(), span, |this,span,ty,expected_type:&Type|{
            let expected_ty = this.format_type(&expected_type);
            let got_ty = this.format_type(&ty);
            this.error(format!("Expected type '{}' got '{}'.",expected_ty,got_ty), span)

        })
    }
    fn check_type_coerces_to_with_message(&self,from:Type,to:Type,span:SourceLocation,msg:String) -> Type{
        if from == to || from.is_never() || from.has_error(){
            to
        }
        else{
            if !(from.has_error()|| to.has_error()){
                self.error(msg, span)
            }
            Type::new_error()
        }
    }
    fn check_type_coerces_to(&self,from:Type,to:Type,span:SourceLocation) -> Type{
        let msg = format!("Expected '{}' got '{}'.",self.format_type(&to),self.format_type(&from));
        self.check_type_coerces_to_with_message(from, to, span,msg)
    }
    fn check_type_equals_with(&self,ty1:Type,ty2:Type,span:SourceLocation,mut err : impl FnMut(&Self,SourceLocation,&Type,&Type)) -> Type{
        if ty1 == ty2{
            ty1
        }
        else{
            if !(ty1.has_error() || ty2.has_error()){
                err(self,span,&ty1,&ty2);
            }
            Type::new_error()
        }
    }
    fn check_array_expr(&mut self,span:SourceLocation,elements:&[hir::Expr],expected:Expectation) -> Type{
        let mut element_type = match &expected{
            Expectation::HasType(Type::Array(element_type)) | Expectation::CoercesTo(Type::Array(element_type)) => 
                Some(*element_type.clone()),
            _ => None
        };
        let element_type = if !elements.is_empty(){
            for element in elements{
                let current_element = self.check_expr(element,element_type.as_ref().map_or(Expectation::None,|ty|Expectation::CoercesTo(ty.clone())));
                if element_type.as_ref().is_none(){
                    element_type = Some(current_element);
                }

            }
            element_type
        }
        else{
            element_type
        };
        let Some(element_type) = element_type else {
            return self.new_error("Cannot infer type of empty array.".to_string(), span);
        };
        Type::new_array(element_type)
    }
    fn check_literal_expr(&self,literal:&hir::LiteralKind) -> Type{
        let lit_ty = match literal{
            hir::LiteralKind::Bool(_) => Type::Bool,
            hir::LiteralKind::Float(_) => Type::Float,
            hir::LiteralKind::Int(_) => Type::Int,
            hir::LiteralKind::String(_) => Type::String
        };
        lit_ty
    }
    fn check_tuple_expr(&mut self,elements:&[hir::Expr],expected : Expectation) -> Type{
        let element_types = if let Expectation::HasType(Type::Tuple(element_types)) | Expectation::CoercesTo(Type::Tuple(element_types)) = expected{
            element_types
        } 
        else{
            Vec::new()
        };
        let element_types = elements.iter().enumerate().map(|(i,element)|{
            let expected_element = match element_types.get(i){
                Some(ty) => Expectation::CoercesTo(ty.clone()),
                None => Expectation::None
            };
            self.check_expr(element, expected_element)
        }).collect();
        Type::new_tuple(element_types)
    }
    fn check_match_expr(&mut self,matchee:&hir::Expr,arms:&[hir::MatchArm],expected:Expectation) -> Type{
        let matchee_ty = self.check_expr(matchee, Expectation::None);
        let mut result_ty = Type::Never;
        for arm in arms{
            self.check_pattern(&arm.pat, matchee_ty.clone());
            let body_ty = self.check_expr(&arm.body, expected.clone());
            if !body_ty.is_never() && result_ty.is_never(){
                result_ty = body_ty;
            }
            else{
                result_ty = self.check_type_coerces_to(body_ty, result_ty, arm.body.span);
            }
        }
        result_ty
    }
    fn check_if_expr(&mut self,condition:&hir::Expr,then_branch:&hir::Expr,else_branch:Option<&hir::Expr>,expected:Expectation) -> Type{
        self.check_expr(condition, Expectation::CoercesTo(Type::Bool));
        let then_ty = self.check_expr(then_branch, expected.clone());
        if let Some(else_branch) = else_branch.as_ref(){
            let else_ty = self.check_expr(else_branch, expected);
            if else_ty == Type::Never{
                return then_ty;
            }
            else if then_ty == Type::Never{
                return else_ty;
            }
            else{
                self.check_type_equals_with(then_ty, else_ty,else_branch.span,|this,span,then_ty,else_ty|{
                    let then = this.format_type(&then_ty);
                    let else_ = this.format_type(else_ty);
                    this.error(format!("'if' and 'else' branches have incompatible types '{}' and '{}'.",then,else_), span);
                })
            }
        }
        else{
            let then = self.format_type(&then_ty);
            self.check_type_coerces_to_with_message(then_ty, Type::new_unit(),then_branch.span,format!("'if' of type '{}' must have else.",then))
        }
    }
    fn check_block_expr(&mut self,stmts:&[hir::Stmt],result_expr:Option<&hir::Expr>,expected : Expectation) -> Type{
        self.check_stmts(stmts);
        let ty = if let Some(result_expr) = result_expr.as_ref(){
            self.check_expr(result_expr, expected)
        }
        else{
            Type::new_unit()
        };
        ty
    }
    fn check_callee(&mut self,callee:&hir::Expr,expected_ty:Option<&Type>) -> Type{
        match &callee.kind{
            hir::ExprKind::Path(path) => {
                match path{
                    hir::PathExpr::Path(path) => {
                        self.check_expr_path(path, true)
                    },
                    hir::PathExpr::Infer(name) => {
                        expected_ty.and_then(|ty| ty.as_adt().map(|info| (ty,info))).and_then(|(ty,(generic_args,id,kind))|{
                            match kind{
                                AdtKind::Enum => {
                                    self.context.get_variant_of(id, name.index).map(|variant|{
                                        let mut all_anon_fields = true;
                                        let params = TypeSubst::new(&generic_args).instantiate_types(variant.fields.iter().map(|field|{
                                            all_anon_fields &= self.ident_interner.get(field.name.index).parse::<usize>().is_ok();
                                            &field.ty
                                        }));
                                        if !all_anon_fields{
                                            self.error(format!("Cannot use variant '{}' as callable.",self.ident_interner.get(name.index)), name.span);
                                        }
                                        Type::new_function(params, ty.clone())
                                    })

                                },
                                AdtKind::Struct => None
                            }
                        }).unwrap_or_else(|| self.new_error(format!("Cannot infer type."),name.span))
                    }
                }
            },
            _ => self.check_expr(callee, Expectation::None)
        }
    }
    fn check_call_expr(&mut self,callee:&hir::Expr,args:&[hir::Expr],expected_ty:Option<&Type>) -> Type{
        let callee_ty = self.check_callee(callee,expected_ty);
        if let Type::Function(params,return_type) = callee_ty{
            if params.len() == args.len(){
                let return_ty = *return_type;
                params.iter().zip(args.iter()).for_each(|(param,arg)|{
                    self.check_expr(arg,Expectation::CoercesTo(param.clone()));
                });
                return_ty
            }
            else{
                self.new_error(format!("Expected '{}' arg{} got '{}'.",params.len(),if params.len() == 1 {""} else {"s"},args.len()), callee.span)
            }
        }
        else if callee_ty.has_error(){
            return Type::new_error();
        }
        else{
            let callee_string = self.format_type(&callee_ty);
            self.new_error(format!("Cannot call '{}'.",callee_string), callee.span)
        }
    }
    fn get_member(&self,ty:&Type,member:Ident) -> Option<TypeMember>{
        if let Some((generic_args,id,AdtKind::Enum)) = ty.as_adt(){
            if let Some(variant) = self.context.get_variant_of(id, member.index){
                return Some(TypeMember::Variant(id,generic_args.clone(), variant));
            }
        }
        self.get_method(ty, member,true).map(|MethodLookup { generic_params,base_generic_args, sig,id,has_receiver:_ }|{
            TypeMember::Method { receiver_generic_args:base_generic_args,receiver_generic_params: generic_params, sig,id}
        })
    }
    fn get_method(&self,ty:&Type,method_ident:Ident,keep_receiver:bool) -> Option<MethodLookup>{
        let method_index = method_ident.index;
        if let Type::Array(_) | Type::String = ty{
            if method_ident.index == self.symbols.len_symbol(){
                return Some(MethodLookup{
                    generic_params : None,
                    sig : FuncSig { params: vec![], return_type: Type::Int },
                    base_generic_args : GenericArgs::new_empty(),
                    id : None,
                    has_receiver : true
                });
            }
        }   
        self.context.get_methods(ty, method_index).pop().map(|(id,method,generic_args)|{
            let generics = self.context.expect_generics_for(id);
            let sig = {
                let mut sig = method.sig.clone();
                if method.has_receiver && !keep_receiver{
                    sig.params.remove(0);
                }
                sig
            };
            MethodLookup{generic_params:Some(generics),base_generic_args:generic_args,sig,id:Some(id),has_receiver:method.has_receiver}
        }).or_else(|| self.context.get_default_trait_methods(ty, method_index).pop().map(|(impl_id,id,method,generic_args)|{
            let trait_id = self.context.expect_owner_of(id);
            let generics = self.context.expect_generics_for(id);
            let trait_generics = self.lowerer().get_generic_args(self.context.impls[impl_id].trait_.as_ref().expect("It should have a trait path")).expect("There should be generics here");
            let sig = {
                let mut sig = method.sig.clone();
                if method.has_receiver && !keep_receiver{
                    sig.params.remove(0);
                }
                sig
            };
            /*The generic args inferred are based on the impl rather than the trait
              so substitute into the trait's generic arguments rather than the impls
             */
            let true_generics = GenericArgs::new(trait_generics.iter().map(|ty| TypeSubst::new(&generic_args).instantiate_type(ty)).collect());
            let sig = SelfTypeSubst{ty,id:trait_id}.instantiate_signature(&sig);
            MethodLookup{generic_params:Some(generics),base_generic_args:true_generics,sig,id:Some(id),has_receiver:method.has_receiver}
        })).or_else(||{
            let (trait_,method_id) = (||{
                let trait_= match ty {
                    &Type::Param(index,_) => {
                        self.env.get_generic_constraint_at(index).map(|trait_|{
                            trait_
                        })
                    },
                    &Type::SelfAlias(id) => self.env.get_self_type().and_then(|ty| ty.as_trait()).filter(|trait_|{
                        trait_.id == id
                    }),
                    _ => return None
                }?;
                
                let method_id = self.context.traits[trait_.id].methods.iter().find(|trait_method|{
                    self.context.ident(trait_method.id).index == method_index
                }).map(|method|{
                    method.id
                })?;
                Some((trait_,method_id))
            })()?;
            let method = &self.context.methods[method_id];
            let method_generics = self.context.expect_generics_for(method_id);
            let subst = SelfTypeSubst{ty,id:trait_.id}.chain(TypeSubst::new(&trait_.generic_args));
            let sig = {
                let mut sig = method.sig.clone();
                if method.has_receiver && !keep_receiver{
                    sig.params.remove(0);
                }
                sig
            };
            let sig = subst.instantiate_signature(&sig);
            Some(MethodLookup{generic_params:Some(method_generics),base_generic_args:trait_.generic_args.clone(),sig,id:Some(method_id),has_receiver:method.has_receiver})
        })
    }
    ///Checks a method call
    /// or a call of a field
    fn check_method_call(&mut self,receiver:&hir::Expr,segment: &hir::PathSegment,args:&[hir::Expr]) -> Type{
        let receiver_ty = self.check_expr(receiver, Expectation::None);
        let generic_args = self.lowerer().lower_generic_args(&segment.args);
        let name = segment.ident;
        let (generic_params,base_generic_args,method_sig,has_receiver,method_id) = match self.get_method(&receiver_ty, name,false) {
            Some(MethodLookup { generic_params, sig,base_generic_args ,id,has_receiver}) => (generic_params,base_generic_args,sig,has_receiver,id),
            None => {
                let field_ty = if let &Type::Adt(ref generic_args,id,AdtKind::Struct) = &receiver_ty{
                    self.context.structs[id].fields.iter().find(|field_def|{
                        field_def.name.index == name.index
                    }).map(|field_def| TypeSubst::new(generic_args).instantiate_type(&field_def.ty))
                }
                else if let Type::Tuple(elements) = &receiver_ty{
                    self.ident_interner.get(name.index).parse::<usize>().ok().and_then(|index|{
                        elements.get(index)
                    }).cloned()
                }
                else{
                    None
                };
                let Some(Type::Function(params,return_type)) = field_ty else {
                    if receiver_ty.has_error(){
                        return Type::new_error();
                    }
                    return self.new_error(format!("{} has no method '{}'.",self.format_type(&receiver_ty),self.ident_interner.get(name.index)), name.span)
                };
                let sig = FuncSig{params,return_type:*return_type};
                //We're treating a field access as a method call so just allow it
                (None,GenericArgs::new_empty(),sig,true,None)
            }
        };

        if !has_receiver{
            self.error(format!("Cannot call '{}' using method call syntax.",self.ident_interner.get(name.index)), name.span);
        }
        let generic_param_len = generic_params.map_or(0, |generics| generics.param_names.len());

        if !self.check_path_segment(segment, 
            &if let Some(method_id) = method_id { self.context.expect_generic_constraints(method_id)} else { std::iter::repeat_n(None, generic_param_len).collect::<Vec<_>>()}
        ){
            return Type::new_error()
        }
        let method_sig =  TypeSubst::new(&generic_args.rebase(&base_generic_args)).instantiate_signature(&method_sig);
        if method_sig.params.len() != args.len(){
            self.error(format!("Expected {} arg{} got {}.",method_sig.params.len(),if method_sig.params.len() == 1 { ""} else {"s"},args.len()), name.span);
            return method_sig.return_type;
        }
        for (param,arg) in method_sig.params.into_iter().zip(args){
            self.check_expr(arg, Expectation::CoercesTo(param));
        }
        method_sig.return_type
    }
    fn get_constructor_with_generic_args(&mut self, path: &hir::InferOrPath, expected_type: Option<&Type>) -> (GenericArgs,Option<(AdtKind,DefId)>){
        match path{
            &hir::InferOrPath::Infer(_,name) => {
                let generic_args_and_adt = expected_type.and_then(|ty|{
                    ty.as_adt().and_then(|(generic_args,id,kind)|{
                        match (kind,name){
                            (AdtKind::Enum,Some(name)) => {
                                self.context.get_variant_of(id,name.index).map(|variant| (generic_args.clone(),(AdtKind::Enum,variant.id)))
                            },
                            (AdtKind::Struct,None) => {
                                Some((generic_args.clone(),(AdtKind::Struct,id)))
                            },
                            _ => None
                        }
                        
                    })
                });
                let Some((generic_args,kind_and_id)) = generic_args_and_adt else{
                    return (GenericArgs::new_empty(),None)
                };

                (generic_args,Some(kind_and_id))
            },
            hir::InferOrPath::Path(path) => {
                let generic_args = self.lowerer().get_generic_args(path).expect("There should be generic args");
                match path{
                    hir::QualifiedPath::TypeRelative(ty,segment) => {
                        let ty = self.lower_type(ty);
                        self.get_member(&ty,segment.ident).and_then(|member|{
                            let TypeMember::Variant(_,generic_args,variant) = member else {
                                return None;
                            };
                            Some((generic_args,Some((AdtKind::Enum,variant.id))))
                        }).unwrap_or_else(|| (generic_args,None))
                    },  
                    hir::QualifiedPath::Resolved(path) => {
                        match path.final_res{
                            hir::Resolution::Definition(hir::DefKind::Struct,id) => (generic_args,Some((AdtKind::Struct,id))),
                            hir::Resolution::Definition(hir::DefKind::Variant,id) => (generic_args,Some((AdtKind::Enum,id))),
                            hir::Resolution::SelfType => {
                                self.env.get_self_type().and_then(|ty|{
                                    ty.as_ty()?.as_adt()
                                }).map(|(generic_args,id,kind)|{
                                    match kind{
                                        AdtKind::Struct => (generic_args.clone(),Some((kind,id))),
                                        AdtKind::Enum => (generic_args.clone(),None)
                                    }
                                }).unwrap_or_else(|| (generic_args,None))
                            },
                            _ =>{
                                (generic_args,None)
                            } 
                        }

                    }
                }
            }
        }
    }
    fn check_struct_literal(&mut self,expr:&hir::Expr,path:&hir::InferOrPath,fields:&[hir::FieldExpr],expected_type:Option<&Type>) -> Type{
        if let hir::InferOrPath::Path(path) = path{
            self.check_path(path);
        }
        let (generic_args,Some((constructor_kind,id))) = self.get_constructor_with_generic_args(path,expected_type) else {
            let err = self.new_error(if let hir::InferOrPath::Path(path) = path { format!("Cannot use '{}' as constructor.",path.format(self.ident_interner))} else { format!("Cannot infer type of constructor.")},expr.span);
            for field in fields{
                self.check_expr(&field.expr, Expectation::None);
            }
            return err;
        };
        let type_id = match constructor_kind{
            AdtKind::Enum => self.context.expect_owner_of(id),
            AdtKind::Struct => id
        };
        let field_tys = match constructor_kind{
            AdtKind::Struct => self.context.structs[id].fields.iter().map(|field|{
                (field.name.index,field.ty.clone())
            }).collect::<FxHashMap<SymbolIndex,Type>>(),
            AdtKind::Enum => {
                self.context.get_variant(id).expect("Should definitely be a variant with this id").fields.iter().map(|field|{
                    (field.name.index,field.ty.clone())
                }).collect()
            }
        };
        let mut seen_fields = FxHashSet::default();
        let mut last_field_span = expr.span;
        for field_expr in fields{
            let field_ty= match field_tys.get(&field_expr.field.index).map(|ty| TypeSubst::new(&generic_args).instantiate_type(ty)){
                Some(ty) => ty,
                None => {
                    self.new_error(format!("Unkown field '{}'.",self.ident_interner.get(field_expr.field.index)), field_expr.field.span)
                }
            };
            if !seen_fields.insert(field_expr.field.index){
                self.error(format!("Repeated field '{}'.",self.ident_interner.get(field_expr.field.index)), field_expr.field.span);
            }
            self.check_expr(&field_expr.expr, Expectation::CoercesTo(field_ty));
            last_field_span = field_expr.span;
        }
        let field_names = field_tys.into_keys().collect::<FxHashSet<_>>();
        let missing_fields = field_names.difference(&seen_fields);
        for &field in missing_fields.into_iter(){
            self.error(format!("Missing field initializer for field '{}'.",self.ident_interner.get(field)), last_field_span);
        }
        match constructor_kind{
            AdtKind::Enum => Type::new_enum(generic_args, type_id),
            AdtKind::Struct => Type::new_struct(generic_args, type_id)
        }
    }
    pub(super) fn check_expr(&mut self,expr:&hir::Expr,expected:Expectation) -> Type{
        let ty = match &expr.kind{
            hir::ExprKind::Literal(literal) => {
                self.check_literal_expr(literal)
            },
            hir::ExprKind::Array(elements) => {
                self.check_array_expr(expr.span,elements,expected.clone())
            },
            hir::ExprKind::Tuple(elements) => {
                self.check_tuple_expr(elements, expected.clone())
            },
            hir::ExprKind::If(condition, then_branch, else_branch) => {
                self.check_if_expr(condition, then_branch, else_branch.as_ref().map(|else_branch| else_branch.as_ref()),expected.clone())
            },
            hir::ExprKind::Block(stmts, result_expr) => {
                self.check_block_expr(stmts, result_expr.as_ref().map(|expr| expr.as_ref()), expected.clone())
            },
            hir::ExprKind::Path(path) => {
                match path{
                    hir::PathExpr::Path(path) => {
                        self.check_expr_path(path, matches!(expected,Expectation::CoercesTo(Type::Function(_,_))|Expectation::HasType(Type::Function(_,_))))
                    },
                    &hir::PathExpr::Infer(name) => {
                         expected.as_type().and_then(|ty|{
                            match ty.as_adt() {
                                Some((_,id,AdtKind::Enum)) => {
                                    self.context.get_variant_of(id, name.index).map(|_| ty.clone())
                                },
                                _ => None
                            }
                         }).unwrap_or_else(|| self.new_error(format!("Cannot infer type of variant."),name.span))
                    }
                }
            },
            hir::ExprKind::Index(base, index) => {
                let base_ty = self.check_expr(base, Expectation::None);
                self.check_expr(index, Expectation::HasType(Type::Int));
                if let Type::Array(element_type) = base_ty{
                    *element_type
                }
                else{
                    let base_ty_string = TypeFormatter::new(&*self.ident_interner, &self.context).format_type(&base_ty);
                    self.new_error(format!("Cannot get element of '{}'.",base_ty_string), base.span)
                }

            },
            hir::ExprKind::Assign(lhs, rhs) => {
                let lhs_ty = self.check_expr(lhs, Expectation::None);
                self.check_expr(rhs, Expectation::CoercesTo(lhs_ty));
                Type::new_unit()
            },
            &hir::ExprKind::Typename(id,ref ty) => {
                let ty = self.lower_type(ty);
                self.store_type(id, ty);
                Type::String
            },
            hir::ExprKind::While(condition, body) => {
                self.check_expr(condition, Expectation::CoercesTo(Type::Bool));
                self.check_expr(body, Expectation::CoercesTo(Type::new_unit()))
            },
            hir::ExprKind::Print(args) => {
                for arg in args{
                    self.check_expr(arg, Expectation::None);
                }
                Type::new_unit()
            },
            hir::ExprKind::Call(callee, args) => {
                self.check_call_expr(callee,args,expected.as_type())
            },
            hir::ExprKind::Binary(op,left,right) => {
                self.check_binary_expr(*op, left, right, expr.span)
            },
            hir::ExprKind::Logical(op,left,right) => {
                self.check_logical_expr(*op,left,right,expr.span)
            },
            hir::ExprKind::Unary(op, operand) => {
                self.check_unary_expr(*op,operand,expr.span)
            },
            hir::ExprKind::Match(matchee, arms) => {
                self.check_match_expr(matchee,arms,expected.clone())
            },
            hir::ExprKind::Return(return_expr) => {
                let return_type = if let Some(FuncContext { return_type,.. }) = self.prev_functions.borrow().last(){
                    Some(return_type.clone())
                }
                else{
                    self.error(format!("'return' outside of function."), expr.span);
                    None
                };
                if let Some(return_expr) = return_expr.as_ref(){
                    self.check_expr(return_expr, return_type.as_ref().map_or(Expectation::None,|ty| Expectation::CoercesTo(ty.clone())));
                }
                else if let Some(return_type) = return_type{
                    if !return_type.is_unit() {
                        let return_ty = self.format_type(&return_type);
                        self.error(format!("Empty return cannot be used for '{}' returning function.",return_ty), expr.span);
                    }
                }
                Type::Never
            },
            hir::ExprKind::Function(function) => {
                let param_patterns = function.params.iter().map(|param| (&param.pattern,&param.ty));
                let param_types = function.params.iter().map(|param| self.lower_type(&param.ty)).collect();
                let return_type = function.return_type.as_ref().map_or_else(|| Type::new_unit(), |ty| self.lower_type(ty));
                let sig = FuncSig{params:param_types,return_type};
                self.check_function(&sig, param_patterns, Some(&function.body));
                sig.as_type()
            },
            hir::ExprKind::Field(base, field) => {
                let base_ty = self.check_expr(base, Expectation::None);
                let field_ty = if let &Type::Adt(ref generic_args,id,AdtKind::Struct) = &base_ty{
                    self.context.structs[id].fields.iter().find(|field_def|{
                        field_def.name.index == field.index
                    }).map(|field_def| TypeSubst::new(generic_args).instantiate_type(&field_def.ty))
                    
                }
                else if let Type::Tuple(elements) = &base_ty{
                    self.ident_interner.get(field.index).parse::<usize>().ok().and_then(|index|{
                        elements.get(index)
                    }).cloned()
                }
                else if base_ty.has_error(){
                    Some(Type::new_error())
                }
                else{
                    let base_string = self.format_type(&base_ty);
                    Some(self.new_error(format!("'{}' doesn't have fields.",base_string), field.span))
                };
                match field_ty{
                    Some(ty) => ty,
                    None => {
                        let base_string = self.format_type(&base_ty);
                        self.new_error(format!("'{}' has no field '{}'.",base_string,self.ident_interner.get(field.index)), field.span)
                        
                    }
                }
            },
            hir::ExprKind::StructLiteral(path,fields) => {
                self.check_struct_literal(expr,path,fields,expected.as_type())
            },
            hir::ExprKind::MethodCall(ref receiver,segment,ref args) => {
                self.check_method_call(receiver,segment,args)
            }
        };
        
        let ty = match expected{
            Expectation::HasType(expected_type) => {
                self.check_type_is_expected(ty, &expected_type, expr.span)
            },
            Expectation::CoercesTo(expected_type) => {
                self.check_type_coerces_to(ty, expected_type, expr.span)
            }
            Expectation::None => {
                ty
            }
        };
        self.store_type(expr.id, ty.clone());
        ty
    }
    fn check_generic_count(&self,expected:usize,got:usize,span:SourceLocation) -> bool{
        if got == expected{
            true
        }
        else{
            self.error(format!("Expected '{}' generic arg{} got '{}'.",expected,if expected == 1 { "" } else {"s"},got), span);
            false
        }
    }
    fn check_path_segment(&mut self, segment: &hir::PathSegment, generic_param_constraints:&[Option<&hir::QualifiedPath>]) -> bool{
        let mut ok = true;
        if self.check_generic_count(generic_param_constraints.len(), segment.args.len(), segment.ident.span){
            for (arg,constraint) in segment.args.iter().zip(generic_param_constraints){
                if let Some(constraint) = constraint{
                    let (Some(trait_id),span) = self.context.as_trait_with_span(&constraint)else {
                        ok = false;
                        self.error(format!("Cannot use '{}' as generic cosntraint.",constraint.format(self.ident_interner)), constraint.span());
                        continue;
                    };
                    let ty = self.lower_type(&arg.ty);
                    let satisfied = match ty{
                        Type::Param(index,_) => {
                            self.env.get_generic_constraint_at(index).is_some_and(|constraint| constraint.id == trait_id)
                        },
                        _ => {
                            
                            self.context.ty_impls_trait(&ty,trait_id)
                        }
                    };
                    if !satisfied{
                        self.error(format!("Type '{}' does not satisfy generic constraint '{}'.",self.format_type(&ty),constraint.format(self.ident_interner)), span);
                        ok = false;
                        
                    }
                }
            }
        }
        else{
            ok = false;
        }
        ok
    }
    fn check_path(&mut self, path: &hir::QualifiedPath) -> bool{
        match path{
            hir::QualifiedPath::TypeRelative(ty,segment) => {
                self.check_type(ty);
                let ty = self.lower_type(ty);
                let Some(member) = self.get_member(&ty, segment.ident) else {
                    self.error(format!("{} has no member '{}'.",self.format_type(&ty),self.ident_interner.get(segment.ident.index)), segment.ident.span);
                    return false;
                };
                let generic_constraints = match member {
                    TypeMember::Method { receiver_generic_args:_,receiver_generic_params:_, sig:_ ,id} => {
                        id.map(|method|{
                            self.context.expect_generic_constraints(method)
                        }).unwrap_or(Vec::new())
                    },
                    TypeMember::Variant(_,_,_) => {
                        Vec::new()
                    }
                };
                self.check_path_segment(segment,&generic_constraints)
            },
            hir::QualifiedPath::Resolved(path) => {
                let mut ok = true;
                for segment in path.segments.iter(){
                    
                    let generic_constraints = self.context.get_generic_constraints(&segment.res);
                    ok &= self.check_path_segment(segment,generic_constraints.as_slice());
                }
                ok
            }
        }
    }
    fn check_expr_path(&mut self, path: &hir::QualifiedPath, as_callable: bool) -> Type{
        let ok = self.check_path(path);
        let ty = match path{
            hir::QualifiedPath::Resolved(resolved_path) => {
                match resolved_path.final_res{
                    hir::Resolution::Variable(variable) => {
                        self.env.get_variable_type(variable)
                    },
                    hir::Resolution::Definition(hir::DefKind::Function,function) => {
                        let def = &self.context.functions[function];
                        TypeSubst::new(&self.lowerer().get_generic_args(path).expect("There should be some generic args here")).instantiate_signature(&def.sig).as_type()
                    },
                    hir::Resolution::Definition(hir::DefKind::Variant,id) => {
                        let enum_id = self.context.expect_owner_of(id);
                        let variant = self.context.get_variant(id).expect("There should be a variant here");
                        let generic_args = self.lowerer().get_generic_args(path).expect("There should be some generic args here");
                        if as_callable{
                            let mut all_anon_fields = true;
                            let params = TypeSubst::new(&generic_args).instantiate_types(variant.fields.iter().map(|field|{
                                all_anon_fields &= self.ident_interner.get(field.name.index).parse::<usize>().is_ok();
                                &field.ty
                            }));
                            if !all_anon_fields{
                                self.error(format!("Cannot use variant '{}' as callable.",resolved_path.format(self.ident_interner)), resolved_path.span);
                            }
                            Type::new_function(params,Type::new_enum(generic_args, enum_id))
                        }
                        else{
                            if !variant.fields.is_empty(){
                                self.error(format!("Cannot initialize variant '{}' without fields.",resolved_path.format(self.ident_interner)), resolved_path.span);
                            }
                            Type::new_enum(generic_args, enum_id)
                        }
                    },
                    hir::Resolution::Definition(hir::DefKind::Struct,id) => {
                        let struct_def = &self.context.structs[id];
                        let generic_args = self.lowerer().get_generic_args(path).expect("There should be some generic args here");
                        if as_callable{
                            let mut all_anon_fields = true;
                            let params = TypeSubst::new(&generic_args).instantiate_types(struct_def.fields.iter().map(|field|{
                                all_anon_fields &= self.ident_interner.get(field.name.index).parse::<usize>().is_ok();
                                &field.ty
                            }));
                            if !all_anon_fields{
                                self.error(format!("Cannot use struct '{}' as callable.",resolved_path.format(self.ident_interner)), resolved_path.span);
                            }
                            Type::new_function(params,Type::new_struct(generic_args, id))
                        }
                        else{
                            if !struct_def.fields.is_empty(){
                                self.error(format!("Cannot initialize struct '{}' without fields.",resolved_path.format(self.ident_interner)), resolved_path.span);
                            }
                            Type::new_struct(generic_args, id)
                        }

                    },
                    hir::Resolution::Builtin(hir::BuiltinKind::Panic) => {
                        Type::new_function(vec![Type::String], Type::Never)
                    },
                    hir::Resolution::SelfType => {
                        if let Some((generic_args,id,AdtKind::Struct))  = self.env.get_self_type().and_then(|ty| ty.as_ty()?.as_adt()){
                            let struct_def = &self.context.structs[id];
                            if as_callable{
                                let mut all_anon_fields = true;
                                let params = TypeSubst::new(&generic_args).instantiate_types(struct_def.fields.iter().map(|field|{
                                    all_anon_fields &= self.ident_interner.get(field.name.index).parse::<usize>().is_ok();
                                    &field.ty
                                }));
                                if !all_anon_fields{
                                    self.error(format!("Cannot use struct '{}' as callable.",resolved_path.format(self.ident_interner)), resolved_path.span);
                                }
                                Type::new_function(params,Type::new_struct(generic_args.clone(), id))
                            }
                            else{
                                if !struct_def.fields.is_empty(){
                                    self.error(format!("Cannot initialize struct '{}' without fields.",resolved_path.format(self.ident_interner)), resolved_path.span);
                                }
                                Type::new_struct(generic_args.clone(), id)
                            }
                        }
                        else{
                            self.new_error(format!("Cannot use type '{}' as expr.",resolved_path.format(self.ident_interner)), resolved_path.span)
                        }
                    },
                    hir::Resolution::Primitive(_) | 
                    hir::Resolution::Definition(hir::DefKind::Param|hir::DefKind::Enum|hir::DefKind::Trait,_) | hir::Resolution::SelfAlias(_)|
                    hir::Resolution::None => 
                        self.new_error(format!("Cannot use type '{}' as expr.",resolved_path.format(self.ident_interner)), resolved_path.span),
                }
        
            },
            hir::QualifiedPath::TypeRelative(ty,segment) => {
                let ty = self.lower_type(&ty);
                let member = self.get_member(&ty, segment.ident);
                let Some(member) = member else {
                    return Type::new_error();
                };
                match member{
                    TypeMember::Variant(enum_id,ty_generic_args,variant) => {
                        if as_callable{
                            let mut all_anon_fields = true;
                            let params = TypeSubst::new(&ty_generic_args).instantiate_types(variant.fields.iter().map(|field|{
                                all_anon_fields &= self.ident_interner.get(field.name.index).parse::<usize>().is_ok();
                                &field.ty
                            }));
                            if !all_anon_fields{
                                self.error(format!("Cannot use variant '{}' as callable.",path.format(self.ident_interner)), segment.ident.span);
                            }
                            Type::new_function(params,Type::new_enum(ty_generic_args.clone(), enum_id))
                        }
                        else{
                            if !variant.fields.is_empty(){
                                self.error(format!("Cannot initialize variant '{}' without fields.",path.format(self.ident_interner)), segment.ident.span);
                            }
                            Type::new_enum(ty_generic_args.clone(), enum_id)
                        }

                    },
                    TypeMember::Method { receiver_generic_args,receiver_generic_params:_, sig:method_sig,id:_ } => {
                        let generic_args = self.lowerer().lower_generic_args(&segment.args);
                        TypeSubst::new(&generic_args.rebase(&receiver_generic_args)).instantiate_signature(&method_sig).as_type()
                    }
                }
            }
        };
        if ok{
            ty
        }
        else{
            Type::new_error()
        }
    }
}