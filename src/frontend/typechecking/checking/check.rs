use std::cell::RefCell;
use fxhash::{FxHashMap, FxHashSet};
use crate::{
     data_structures::{IndexVec, IntoIndex}, errors::ErrorReporter, frontend::{
        ast_lowering::hir::{self, DefId, HirId, Resolution}, 
        tokenizing::SourceLocation, 
        typechecking::{context::{FuncSig, TypeContext, TypeMember}, error::TypeError, items::item_check::ItemCheck, types::{format::TypeFormatter, generics::GenericArgs, lowering::TypeLower, subst::{Subst, TypeSubst}, AdtKind, Type}}
    }, identifiers::{BodyIndex, FieldIndex, GlobalSymbols, SymbolIndex, SymbolInterner, VariableIndex}
};
use super::{env::{SelfType, TypeEnv}, Expectation, TypeCheckResults};
struct FuncContext{
    return_type : Type
}
pub struct TypeChecker<'a>{
    env : TypeEnv,
    error_reporter: ErrorReporter,
    prev_functions : RefCell<Vec<FuncContext>>,
    variable_types : RefCell<FxHashMap<VariableIndex,Type>>,
    context : &'a TypeContext,
    ident_interner : &'a SymbolInterner,
    symbols:&'a GlobalSymbols,
    bodies:&'a IndexVec<BodyIndex,hir::Body>,
    results : RefCell<TypeCheckResults>
}
impl<'a> TypeChecker<'a>{
    pub fn new(context:&'a TypeContext,symbols:&'a GlobalSymbols,bodies:&'a IndexVec<BodyIndex,hir::Body>,interner:&'a SymbolInterner) -> Self{
        Self { 
            env : TypeEnv::new(),
            error_reporter: ErrorReporter::new(false),
            prev_functions : RefCell::new(Vec::new()),
            context,
            bodies,
            ident_interner: interner,
            symbols,
            results: RefCell::new(TypeCheckResults::new()),
            variable_types : RefCell::new(FxHashMap::default())
        }
    }
    pub(super) fn lowerer(&self) -> TypeLower{
        TypeLower::new(&self.ident_interner,self.context,self.env.get_self_type().map(|self_ty| &self_ty.0).cloned(),&self.error_reporter)
    }
    pub(super) fn lower_type(&self,ty: &hir::Type) -> Type{
        self.lowerer().lower_type(ty)
    }
    pub(super) fn format_type(&self,ty: &Type) -> String{
        TypeFormatter::new(&*self.ident_interner, &*self.context).format_type(ty)
    }
    fn store_type(&self, id: HirId, ty: Type){
        self.results.borrow_mut().node_types.insert(id, ty);
    }
    fn store_generic_args(&self, id: HirId, args: GenericArgs){
        self.results.borrow_mut().generic_args.insert(id,args);
    }
    fn store_resolution(&self, id: HirId, res: Resolution){
        self.results.borrow_mut().resolutions.insert(id, res);
    }
    fn error(&self,msg:String,span : SourceLocation){
        self.error_reporter.emit(msg, span);
    }

    pub(super) fn new_error(&self,msg:String,span : SourceLocation) -> Type{
        self.error(msg, span);
        Type::new_error()
    }
    pub fn check<'b>(mut self,items:impl Iterator<Item = &'b hir::Item>) -> Result<TypeCheckResults,TypeError>{
        for item in items{
            match item{
                hir::Item::Function(function_def) => {
                    self.check_function(&self.context.signatures[function_def.id], &function_def.function);
                },
                hir::Item::Enum(_) => {},
                hir::Item::Struct(_) => {},
                hir::Item::Impl(impl_) => {
                    self.env.set_self_type(Some(SelfType(self.context.impls[impl_.id].ty.clone())));
                    for method in &impl_.methods{
                        self.check_function(&self.context.signatures[method.id],&method.function);
                    }
                    self.env.set_self_type(None);
                }
            }
        }
        if !self.error_reporter.error_occurred(){
            Ok(self.results.into_inner())
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
    fn check_function<'b>(&mut self,sig:&FuncSig, function : &hir::Function){
        let FuncSig { params:param_types, return_type } = sig;
        for (param_pattern,param_ty) in self.bodies[function.body].params.iter().map(|param| &param.pattern).zip(param_types){
            self.check_pattern(param_pattern, param_ty.clone());
        }
        self.prev_functions.borrow_mut().push(FuncContext { return_type: return_type.clone() });
        self.check_expr(&self.bodies[function.body].value, Expectation::CoercesTo(return_type.clone()));
        self.prev_functions.borrow_mut().pop();

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
            &hir::StmtKind::Item(_) => {
            },
        }
    }
    fn check_pattern(&self,pattern : &hir::Pattern, expected_type : Type){
        let ty = match &pattern.kind{
            &hir::PatternKind::Binding(variable, _,ref binding_pattern) => {
                self.variable_types.borrow_mut().insert(variable, expected_type.clone());
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
                self.check_type_is_expected(&literal_ty, &expected_type, pattern.span);
                literal_ty
            },
            hir::PatternKind::Variant(path, fields) => {
                let (generic_args,kind_and_id) = self.get_constructor_with_generic_args(path,Some(&expected_type));
                let Ok(kind_and_id) = kind_and_id else {
                    return;
                };
                let Some((constructor_kind,id)) = kind_and_id else{
                    self.error(if let hir::InferOrPath::Path(path) = path { format!("Cannot use '{}' as constructor.",path.format(self.ident_interner))} else { format!("Cannot infer type of constructor.")},pattern.span);
                    return;
                };
                let type_id = match constructor_kind{
                    AdtKind::Enum => self.context.expect_owner_of(id),
                    AdtKind::Struct => id
                };
                let field_types = match constructor_kind{
                   AdtKind::Enum =>  Some(TypeSubst::new(&generic_args).instantiate_types(self.context.expect_variant(id).fields.iter())),
                   AdtKind::Struct => {
                        for field in fields{
                            self.check_pattern(field, Type::new_error());
                        }
                        None
                   }
                };
                if let Some(field_types) = field_types{
                    let field_len = field_types.len();
                    if field_len != fields.len(){
                        self.error(format!("Expected '{}' field{} got '{}'.",field_len,if field_len == 1{""} else{"s"},fields.len()), pattern.span);
                    }
                    self.store_generic_args(pattern.id, generic_args.clone());
                    self.store_resolution(pattern.id, Resolution::Definition(match constructor_kind { AdtKind::Enum => hir::DefKind::Variant, AdtKind::Struct => hir::DefKind::Struct}, id));
                    if let AdtKind::Struct = constructor_kind{
                        self.error(format!("Cannot match struct '{}' with ( ).",self.ident_interner.get(self.context.ident(id).index)), pattern.span);
                    };
                    for (field,field_ty) in fields.iter().zip(field_types){
                        self.check_pattern(&field, field_ty);
                    }
                }
                match constructor_kind{
                    AdtKind::Enum => Type::new_enum(generic_args,type_id),
                    AdtKind::Struct => Type::new_struct(generic_args, type_id)
                }
            },
            hir::PatternKind::Struct(path, fields) => {
                let (generic_args,kind_and_id) = self.get_constructor_with_generic_args(path,Some(&expected_type));
                let Ok(kind_and_id) = kind_and_id else {
                    return;
                };
                let Some((constructor_kind,id)) = kind_and_id else{
                    self.error(if let hir::InferOrPath::Path(path) = path { format!("Cannot use '{}' as constructor.",path.format(self.ident_interner))} else { format!("Cannot infer type of constructor.")},pattern.span);
                    return;
                };
                let type_id = match constructor_kind{
                    AdtKind::Enum => self.context.expect_owner_of(id),
                    AdtKind::Struct => id
                };
                self.store_generic_args(pattern.id, generic_args.clone());
                self.store_resolution(pattern.id, Resolution::Definition(match constructor_kind { AdtKind::Enum => hir::DefKind::Variant, AdtKind::Struct => hir::DefKind::Struct}, id));
                match constructor_kind{
                    AdtKind::Struct => {
                        let field_tys = self.context.structs[id].fields.iter().enumerate().map(|(field_index,field)|{
                            (field.name.index,(FieldIndex::new(field_index as u32),field.ty.clone()))
                        }).collect::<FxHashMap<SymbolIndex,(FieldIndex,Type)>>();
                        let mut seen_fields = FxHashSet::default();
                        let mut last_field_span = pattern.span;
                        for field_pattern in fields{
                            let (field_ty,field_index)= match field_tys.get(&field_pattern.name.index).map(|&(field_index,ref ty)| (TypeSubst::new(&generic_args).instantiate_type(ty),field_index)){
                                Some((ty,field_index)) => (ty,Some(field_index)),
                                None => {
                                    (self.new_error(format!("Unkown field '{}'.",self.ident_interner.get(field_pattern.name.index)), field_pattern.name.span),None)
                                }
                            };
                            if !seen_fields.insert(field_pattern.name.index){
                                self.error(format!("Repeated field '{}'.",self.ident_interner.get(field_pattern.name.index)), field_pattern.name.span);
                            }
                            self.check_pattern(&field_pattern.pattern, field_ty);
                            if let Some(field_index) = field_index{
                                self.results.borrow_mut().fields.insert(field_pattern.id, field_index);
                            }
                            last_field_span = field_pattern.name.span;
                        }
                        let field_names = field_tys.into_keys().collect::<FxHashSet<_>>();
                        let missing_fields = field_names.difference(&seen_fields);
                        for &field in missing_fields.into_iter(){
                            self.error(format!("Missing field pattern for field '{}'.",self.ident_interner.get(field)), last_field_span);
                        }
                    }
                    AdtKind::Enum => {
                        self.error(format!("Cannot match variant '{}' with {{ }}.",self.ident_interner.get(self.context.ident(id).index)), pattern.span);
                        for field in fields{
                            self.check_pattern(&field.pattern, Type::new_error());
                        }
                    }
                };
                match constructor_kind{
                    AdtKind::Enum => Type::new_enum(generic_args,type_id),
                    AdtKind::Struct => Type::new_struct(generic_args, type_id)
                }

            }
        };
        self.store_type(pattern.id, ty);
    }
    fn check_type_is_expected(&self, ty : &Type, expected_type : &Type, span : SourceLocation) -> bool{
        if ty != expected_type {
            self.error(format!("Expected type '{}' got '{}'.",self.format_type(expected_type),self.format_type(ty)), span);
            false
        }
        else{
            true
        }
    }
    fn coerces(&self, from: &Type, _: &Type) -> bool{
        from.is_never() || from.is_error()
    }
    fn check_type_coerces_to(&self,from: &Type,to: &Type,span:SourceLocation) -> bool{
        if self.coerces(from,to){
            true
        }
        else{
            self.error(format!("Expected '{}' got '{}'.",self.format_type(to),self.format_type(from)), span);
            false
        }
    }
    fn check_array_expr(&mut self,span:SourceLocation,elements:&[hir::Expr],expected:Expectation) -> Type{
        let element_type =expected.as_type().and_then(|ty| match ty{
            Type::Array(element_type) => Some(element_type.as_ref().clone()),
            _ => None
        });
        if let Some(element_type) = element_type{
            for element in elements{
                self.check_expr(element,Expectation::CoercesTo(element_type.clone()));
            }
            Type::new_array(element_type)
        }
        else{
            let mut all_element_type = None;
            let element_types = elements.iter().map(|element|{
                let element_type = self.check_expr(element, Expectation::None);
                if all_element_type.is_none() || all_element_type.as_ref().is_some_and(|ty: &Type| ty.is_never() && !element_type.is_never()){
                    all_element_type = Some(element_type.clone());
                }
                (element_type,element.id,element.span)
            }).collect::<Vec<_>>();
            if let Some(element_type) = all_element_type{
                for (ty,id,span) in element_types{
                    if ty != element_type{
                        if !self.coerces(&ty, &element_type){
                            self.error(format!("Expected '{}' for match arm got '{}'.",self.format_type(&element_type),self.format_type(&ty)), span);
                        }
                        else{
                            self.results.borrow_mut().coercions.insert(id, element_type.clone());
                        }
                    }

                }
                Type::new_array(element_type)
            }
            else{
                self.new_error("Cannot infer type of empty array.".to_string(), span)
            }
        }
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
        let element_types = if let Some(Type::Tuple(element_types)) = expected.as_type(){
            element_types.clone()
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
        let body_types = arms.iter().map(|arm|{
            self.check_pattern(&arm.pat, matchee_ty.clone());
            let body_ty = self.check_expr(&arm.body, expected.clone());
            if result_ty.is_never() && !body_ty.is_never(){
                result_ty = body_ty.clone();
            }
            (body_ty,arm.body.span,arm.body.id)
        });
        for (ty,span,id) in body_types.collect::<Vec<_>>(){
            if result_ty != ty {
                if !self.coerces(&ty, &result_ty){
                    self.error(format!("Expected '{}' for match arm got '{}'.",self.format_type(&result_ty),self.format_type(&ty)), span);
                }
                else{
                    self.results.borrow_mut().coercions.insert(id, result_ty.clone());
                }
            }
        }

        result_ty
    }
    fn check_if_expr(&mut self,condition:&hir::Expr,then_branch:&hir::Expr,else_branch:Option<&hir::Expr>,expected:Expectation) -> Type{
        self.check_expr(condition, Expectation::CoercesTo(Type::Bool));
        let then_ty = self.check_expr(then_branch, expected.clone());

        if let Some(else_branch) = else_branch.as_ref(){
            let else_ty = self.check_expr(else_branch, expected);
            if then_ty == else_ty{
                then_ty
            }
            else if self.coerces(&else_ty, &then_ty){
                self.results.borrow_mut().coercions.insert(else_branch.id, then_ty.clone());
                then_ty
            }
            else if self.coerces(&then_ty, &else_ty){
                self.results.borrow_mut().coercions.insert(then_branch.id, else_ty.clone());
                else_ty
            }
            else if then_ty.has_error() || else_ty.has_error(){
                Type::Error
            }
            else{
                self.new_error(format!("'if' and 'else' branches have incompatible types '{}' and '{}'.",self.format_type(&then_ty),self.format_type(&else_ty)), else_branch.span)
            }
        }
        else if then_ty.is_unit(){
            then_ty
        }
        else if self.coerces(&then_ty, &Type::new_unit()){
            self.results.borrow_mut().coercions.insert(then_branch.id, Type::new_unit());
            Type::new_unit()
        }
        else if then_ty.has_error() {
            Type::Error
        }
        else{
            self.new_error(format!("'if' of type '{}' requires an 'else' branch.",self.format_type(&then_ty)),then_branch.span)
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
        let ty = match &callee.kind{
            hir::ExprKind::Path(path) => {
                match path{
                    hir::PathExpr::Path(path) => {
                        self.check_expr_path(callee.id,path, true)
                    },
                    hir::PathExpr::Infer(name) => {
                         expected_ty.and_then(|ty| ty.as_adt().map(|info| (ty,info))).and_then(|(ty,(generic_args,id,kind))|{
                            match kind{
                                AdtKind::Enum => {
                                    self.context.get_variant_of(id, name.index).map(|variant|{
                                        let params = TypeSubst::new(&generic_args).instantiate_types(variant.fields.iter().map(|field|{
                                            field
                                        }));
                                        self.store_generic_args(callee.id, generic_args.clone());
                                        self.store_resolution(callee.id, Resolution::Definition(hir::DefKind::Variant,variant.id));
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
        };
        self.store_type(callee.id, ty.clone());
        ty
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
    ///Checks a method call
    /// or a call of a field
    fn check_method_call(&mut self, expr_id: HirId, receiver: &hir::Expr, segment: &hir::PathSegment, args: &[hir::Expr]) -> Type{
        let receiver_ty = self.check_expr(receiver, Expectation::None);
        let generic_args = self.lowerer().lower_generic_args(&segment.args);
        let name = segment.ident;

        let (generic_params,base_generic_args,mut sig,has_receiver) = 
            match self.context.get_member(self.symbols, &receiver_ty, name){
                Some(member) => {
                    match member{
                        TypeMember::Method { receiver_generic_args, sig, id } => {
                            self.store_resolution(expr_id, Resolution::Definition(hir::DefKind::Method, id));
                            (Some(self.context.expect_generics_for(id)),receiver_generic_args,sig,self.context.has_receiver[id])
                        },
                        TypeMember::Variant(id,_,_) => {
                            return self.new_error(format!("Cannot use variant '{}' of '{}' as method.",self.ident_interner.get(self.context.ident(id).index),self.format_type(&receiver_ty)),name.span);
                        } 
                    }
                },
                None => {
                    let field_ty_and_index = if let &Type::Adt(ref generic_args,id,AdtKind::Struct) = &receiver_ty{
                        self.context.structs[id].fields.iter().enumerate().find_map(|(i,field_def)|{
                            (field_def.name.index == name.index).then_some((field_def,FieldIndex::new(i as u32)))
                        }).map(|(field_def,index)| (TypeSubst::new(generic_args).instantiate_type(&field_def.ty),index))
                    }
                    else if let Type::Tuple(elements) = &receiver_ty{
                        self.ident_interner.get(name.index).parse::<usize>().ok().and_then(|index|{
                            elements.get(index).map(|ty| (ty.clone(),FieldIndex::new(index as u32)))
                        })
                    }
                    else{
                        None
                    };
                    let Some((Type::Function(params,return_type),field_index)) = field_ty_and_index else {
                        if receiver_ty.has_error(){
                            return Type::new_error();
                        }
                        return self.new_error(format!("{} has no method '{}'.",self.format_type(&receiver_ty),self.ident_interner.get(name.index)), name.span)
                    };
                    let sig = FuncSig{params,return_type:*return_type};
                    self.results.borrow_mut().fields.insert(expr_id,field_index);
                    //We're treating a field access as a method call,
                    //so just pretend it has a recevier
                    (None,GenericArgs::new_empty(),sig,true)

                }
            };
        if !has_receiver{
            self.error(format!("Cannot call '{}' using method call syntax.",self.ident_interner.get(name.index)), name.span);
        }
        else{

            sig.params.remove(0);
        }
        let generic_param_len = generic_params.map_or(0, |generics| generics.param_names.len());
        if !self.check_generic_count(generic_param_len,segment.args.len(), segment.ident.span){
            return Type::new_error();
        }
        
        let method_sig =  TypeSubst::new(&generic_args.rebase(&base_generic_args)).instantiate_signature(&sig);
        if method_sig.params.len() != args.len(){
            self.error(format!("Expected {} arg{} got {}.",method_sig.params.len(),if method_sig.params.len() == 1 { ""} else {"s"},args.len()), name.span);
            return method_sig.return_type;
        }
        self.store_generic_args(expr_id, generic_args);
        self.results.borrow_mut().signatures.insert(expr_id, method_sig.clone());
        for (param,arg) in method_sig.params.into_iter().zip(args){
            self.check_expr(arg, Expectation::CoercesTo(param));
        }
        method_sig.return_type
    }
    fn get_constructor_with_generic_args(&self, path: &hir::InferOrPath, expected_type: Option<&Type>) -> (GenericArgs,Result<Option<(AdtKind,DefId)>,TypeError>){
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
                    return (GenericArgs::new_empty(),Ok(None))
                };

                (generic_args,Ok(Some(kind_and_id)))
            },
            hir::InferOrPath::Path(path) => {
                let Ok((generic_args,res)) = self.resolve_path(path) else {
                    return (GenericArgs::new_empty(),Err(TypeError));
                };
                match res{
                    hir::Resolution::Definition(hir::DefKind::Struct,id) => (generic_args,Ok(Some((AdtKind::Struct,id)))),
                    hir::Resolution::Definition(hir::DefKind::Variant,id) => (generic_args,Ok(Some((AdtKind::Enum,id)))),
                    _ =>{
                        (generic_args,Ok(None))
                    } 
                }
            }
        }
    }
    fn check_struct_literal(&mut self,expr:&hir::Expr,path:&hir::InferOrPath,fields:&[hir::FieldExpr],expected_type:Option<&Type>) -> Type{
        let (generic_args,kind_and_id) = self.get_constructor_with_generic_args(path,expected_type);
        let Ok(kind_and_id) = kind_and_id else {
            return Type::new_error();
        };
        let Some((constructor_kind,id)) = kind_and_id else {
            let err = self.new_error(if let hir::InferOrPath::Path(path) = path { format!("Cannot use '{}' as constructor.",path.format(self.ident_interner))} else { format!("Cannot infer type of constructor.")},expr.span);
            for field in fields{
                self.check_expr(&field.expr, Expectation::None);
            }
            return err;
        };
        self.store_generic_args(expr.id, generic_args.clone());
        self.store_resolution(expr.id, Resolution::Definition(match constructor_kind { AdtKind::Enum => hir::DefKind::Variant, AdtKind::Struct => hir::DefKind::Struct},id));
        let type_id = match constructor_kind{
            AdtKind::Enum => self.context.expect_owner_of(id),
            AdtKind::Struct => id
        };
        match constructor_kind{
            AdtKind::Struct => {
                let field_tys = 
                self.context.structs[id].fields.iter().enumerate().map(|(field_index,field_def)|{
                    (field_def.name.index,(field_def.ty.clone(),FieldIndex::new(field_index as u32)))
                }).collect::<FxHashMap<SymbolIndex,(Type,FieldIndex)>>();
                
                let mut seen_fields = FxHashSet::default();
                let mut last_field_span = expr.span;
                for field_expr in fields{
                    let (field_ty,field_index)= match field_tys.get(&field_expr.field.index).map(|&(ref ty,index)| (TypeSubst::new(&generic_args).instantiate_type(ty),index)){
                        Some((ty,field_index)) => (ty,Some(field_index)),
                        None => {
                            (self.new_error(format!("Unkown field '{}'.",self.ident_interner.get(field_expr.field.index)), field_expr.field.span),None)
                        }
                    };
                    if !seen_fields.insert(field_expr.field.index){
                        self.error(format!("Repeated field '{}'.",self.ident_interner.get(field_expr.field.index)), field_expr.field.span);
                    }
                    self.check_expr(&field_expr.expr, Expectation::CoercesTo(field_ty));
                    if let Some(field_index) = field_index{
                        self.results.borrow_mut().fields.insert(field_expr.id,field_index);
                    }
                    last_field_span = field_expr.span;
                }
                let field_names = field_tys.into_keys().collect::<FxHashSet<_>>();
                let missing_fields = field_names.difference(&seen_fields);
                for &field in missing_fields.into_iter(){
                    self.error(format!("Missing field initializer for field '{}'.",self.ident_interner.get(field)), last_field_span);
                }
            },
            AdtKind::Enum => {
                self.error(format!("Cannot initialize variant '{}' with {{ }}.",self.ident_interner.get(self.context.ident(id).index)), expr.span);
                for field in fields{
                    self.check_expr(&field.expr, Expectation::None);
                }
            }
        };
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
                        self.check_expr_path(expr.id,path, expected.as_type().is_some_and(|ty| matches!(ty,Type::Function(_, _))))
                    },
                    &hir::PathExpr::Infer(name) => {
                         expected.as_type().and_then(|ty|{
                            match ty.as_adt() {
                                Some((generic_args,id,AdtKind::Enum)) => {
                                    self.context.get_variant_of(id, name.index).map(|variant| {
                                        
                                        self.store_generic_args(expr.id, generic_args.clone());
                                        self.store_resolution(expr.id, Resolution::Definition(hir::DefKind::Variant,variant.id));
                                        ty.clone()
                                    })
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
                let &hir::AnonFunction{id:_,ref function} = function.as_ref();
                let sig = self.lowerer().lower_sig(function.params.iter(), function.return_type.as_ref());
                /*Checks the items signature */
                let item_check = ItemCheck::new(self.context, self.ident_interner, &self.error_reporter);
                item_check.check_function(function);
                self.check_function(&sig, function);
                sig.as_type()
            },
            hir::ExprKind::Field(base, field) => {
                let base_ty = self.check_expr(base, Expectation::None);
                let (field_ty,index) = if let &Type::Adt(ref generic_args,id,AdtKind::Struct) = &base_ty{
                    self.context.structs[id].fields.iter().enumerate().find_map(|(i,field_def)|{
                        (field_def.name.index == field.index).then_some((field_def,FieldIndex::new(i as u32)))
                    }).map(|(field_def,index)| (TypeSubst::new(generic_args).instantiate_type(&field_def.ty),index)).unzip()
                    
                }
                else if let Type::Tuple(elements) = &base_ty{
                    self.ident_interner.get(field.index).parse::<usize>().ok().and_then(|index|{
                        Some((elements.get(index)?.clone(),FieldIndex::new(index as u32)))
                    }).unzip()
                }
                else if base_ty.has_error(){
                    (Some(Type::new_error()),None)
                }
                else{
                    let base_string = self.format_type(&base_ty);
                    (Some(self.new_error(format!("'{}' doesn't have fields.",base_string), field.span)),None)
                };
                if let Some(field_index) = index{
                    self.results.borrow_mut().fields.insert(expr.id, field_index);
                }
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
                self.check_method_call(expr.id,receiver,segment,args)
            }
        };
        let (expr_ty,result_ty) = match expected{
            Expectation::HasType(expected_type) => {
                if self.check_type_is_expected(&ty, &expected_type, expr.span){
                    (ty,expected_type)
                }
                else{
                    (ty.clone(),Type::Error)
                }
            },
            Expectation::CoercesTo(expected_type) => {
                if ty == expected_type{
                    (ty,expected_type)
                }
                else{
                    if self.check_type_coerces_to(&ty, &expected_type, expr.span){
                        self.results.borrow_mut().coercions.insert(expr.id, expected_type.clone());
                        (ty,expected_type)
                    }
                    else{
                        (ty,Type::Error)
                    }
                }
            }
            Expectation::None => {
                (ty.clone(),ty)
            }
        };
        self.store_type(expr.id, expr_ty);
        result_ty
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
    fn check_path_segment(&self, segment: &hir::PathSegment, generic_param_count: usize) -> bool{
        if self.check_generic_count(generic_param_count, segment.args.len(), segment.ident.span){
            true
        }
        else{
            false
        }
    }
    fn resolve_path(&self, path: &hir::QualifiedPath) -> Result<(GenericArgs,Resolution),TypeError>{
        match path{
            hir::QualifiedPath::TypeRelative(ty,segment) => {
                ItemCheck::new(self.context, self.ident_interner, &self.error_reporter).check_type(&ty);
                if self.error_reporter.error_occurred(){
                    return Err(TypeError);
                }
                let ty = self.lower_type(&ty);
                if let Some(member) = self.context.get_member(self.symbols, &ty, segment.ident){
                    let (generic_count,base_generic_args,resolution) = match member{
                        TypeMember::Method { receiver_generic_args, sig:_, id } => {
                            (self.context.expect_generics_for(id).param_names.len(),receiver_generic_args,Resolution::Definition(hir::DefKind::Method, id))
                        },
                        TypeMember::Variant(id,receiver_generic_args,_) => {
                            (0,receiver_generic_args,Resolution::Definition(hir::DefKind::Variant, id))
                        }
                    };
                    self.check_path_segment(segment, generic_count);
                    Ok((self.lowerer().lower_generic_args(&segment.args).rebase(&base_generic_args),resolution))
                }
                else{
                    self.error(format!("{} has no member {}.",self.format_type(&ty),self.ident_interner.get(segment.ident.index)), segment.ident.span);
                    return Err(TypeError);
                }

            },
            hir::QualifiedPath::FullyResolved(path) => {
                for segment in path.segments.iter(){
                    self.check_path_segment(segment,self.context.get_generic_count(&segment.res));
                }
                let (generic_args,res) = match path.final_res{
                    hir::Resolution::SelfType(id) => match &self.context.impls[id].ty{
                         &Type::Adt(ref generic_args,id,AdtKind::Struct)  => {
                            (generic_args.clone(),Resolution::Definition(hir::DefKind::Struct, id))
                         },
                         ty => {
                            self.error(format!("Cannot use '{}' as value.",self.format_type(ty)), path.span);
                            return Err(TypeError);
                         }
                    },
                    res =>  (self.lowerer().lower_generic_args_of_path(path),res)
                };
                Ok((generic_args,res))
            }
        }
    }
    fn check_expr_path(&mut self, expr_id: HirId, path: &hir::QualifiedPath, as_callable: bool) -> Type{
        let Ok((generic_args,res)) =  self.resolve_path(path) else {
            return Type::new_error();
        };
        self.store_generic_args(expr_id, generic_args.clone());
        self.store_resolution(expr_id, res);
        let span = path.span();
        let ty = match res{
            hir::Resolution::Variable(variable) => {
                self.variable_types.borrow()[&variable].clone()
            },
            hir::Resolution::Definition(hir::DefKind::Function|hir::DefKind::Method,id) => {
                let sig = &self.context.signatures[id];
                TypeSubst::new(&generic_args).instantiate_signature(sig).as_type()
            },
            hir::Resolution::Definition(hir::DefKind::Variant,id) => {
                let enum_id = self.context.expect_owner_of(id);
                let variant = self.context.get_variant(id).expect("There should be a variant here");
                if as_callable{
                    let params = TypeSubst::new(&generic_args).instantiate_types(variant.fields.iter().map(|field|{
                        field
                    }));
                    Type::new_function(params,Type::new_enum(generic_args, enum_id))
                }
                else{
                    if !variant.fields.is_empty(){
                        self.error(format!("Cannot initialize variant '{}' without fields.",path.format(self.ident_interner)), span);
                    }
                    Type::new_enum(generic_args, enum_id)
                }
            },
            hir::Resolution::Definition(hir::DefKind::Struct,id) => {
                let struct_def = &self.context.structs[id];
                if as_callable{
                    let mut all_anon_fields = true;
                    let params = TypeSubst::new(&generic_args).instantiate_types(struct_def.fields.iter().map(|field|{
                        all_anon_fields &= self.ident_interner.get(field.name.index).parse::<usize>().is_ok();
                        &field.ty
                    }));
                    if !all_anon_fields{
                        self.error(format!("Cannot use struct '{}' as callable.",path.format(self.ident_interner)), span);
                    }
                    Type::new_function(params,Type::new_struct(generic_args, id))
                }
                else{
                    if !struct_def.fields.is_empty(){
                        self.error(format!("Cannot initialize struct '{}' without fields.",path.format(self.ident_interner)), span);
                    }
                    Type::new_struct(generic_args, id)
                }

            },
            hir::Resolution::Builtin(hir::BuiltinKind::Panic) => {
                self.store_resolution(expr_id, Resolution::Builtin(hir::BuiltinKind::Panic));
                Type::new_function(vec![Type::String], Type::Never)
            },
            hir::Resolution::SelfType(id) => {
                unreachable!("Self type {:?} should already be resolved.",id)
            },
            hir::Resolution::Definition(hir::DefKind::AnonFunction, _) => unreachable!("Can't use anonymous functions in this context"),
            hir::Resolution::Primitive(_) | 
            hir::Resolution::Definition(hir::DefKind::Param|hir::DefKind::Enum,_) | 
            hir::Resolution::None => 
                return self.new_error(format!("Cannot use type '{}' as expr.",path.format(self.ident_interner)),span),
        };
        ty
    }
}