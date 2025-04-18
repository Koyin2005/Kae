use std::cell::Cell;

use fxhash::{FxHashMap, FxHashSet};

use crate::{data_structures::IndexVec, frontend::{ast_lowering::{hir::{self, HirId}, SymbolInterner}, tokenizing::SourceLocation, typechecking::{context::{FuncSig, TypeContext}, error::TypeError, types::{format::TypeFormatter, lowering::{LoweredItem, TypeLower}, Type}}}, identifiers::ItemIndex};


use super::{env::TypeEnv, Expectation};

struct FuncContext{
    return_type : Type
}
pub struct TypeChecker<'a>{
    node_types : FxHashMap<HirId,Type>,
    env : TypeEnv,
    had_error : Cell<bool>,
    lowered_items : IndexVec<ItemIndex,Option<LoweredItem>>,
    prev_functions : Vec<FuncContext>,
    context : &'a mut TypeContext,
    ident_interner : &'a mut SymbolInterner
}

impl<'a> TypeChecker<'a>{
    pub fn new(context:&'a mut TypeContext,items: IndexVec<ItemIndex,LoweredItem>,interner:&'a mut SymbolInterner) -> Self{
        Self { 
            node_types : FxHashMap::default(),
            env : TypeEnv::new(),
            had_error : Cell::new(false),
            lowered_items : items.into_iter().map(Some).collect(),
            prev_functions : Vec::new(),
            context,
            ident_interner: interner
        }
    }
    pub(super) fn lower_type(&self,ty: &hir::Type) -> Type{
        TypeLower::new().lower(ty)
    }
    pub(super) fn format_type(&mut self,ty: &Type) -> String{
        TypeFormatter::new(&mut *self.ident_interner, &mut *self.context).format_type(ty)
    }
    fn store_type(&mut self,id: HirId,ty: Type){
        self.node_types.insert(id, ty);
    }
    fn error(&self,msg:String,span : SourceLocation){
        self.had_error.set(true);
        TypeError.emit(msg, span);
    }

    pub(super) fn new_error(&self,msg:String,span : SourceLocation) -> Type{
        self.error(msg, span);
        Type::new_error()
    }
    pub fn check(mut self,stmts : &[hir::Stmt]) -> Result<(),TypeError>{
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
    fn check_function<'b>(&mut self,sig:&FuncSig,param_patterns:impl Iterator<Item = &'b hir::Pattern>,body:&hir::Expr){
        let FuncSig { params:param_types, return_type } = sig;
        for (param_pattern,param_ty) in param_patterns.zip(param_types){
            self.check_pattern(param_pattern, param_ty.clone());
        }
        self.prev_functions.push(FuncContext { return_type: return_type.clone() });
        self.check_expr(body, Expectation::CoercesTo(&return_type));
        self.prev_functions.pop();

    }
    fn check_stmt(&mut self,stmt : &hir::Stmt) {
        match &stmt.kind{
            hir::StmtKind::Expr(expr) => {
                self.check_expr(expr, Expectation::CoercesTo(&Type::new_unit()));

            },
            hir::StmtKind::Semi(expr) => {
                self.check_expr(expr, Expectation::None);
            },
            hir::StmtKind::Let(pattern,ty,expr) => {
                let ty = ty.as_ref().map(|ty| self.lower_type(&ty));
                let expr_ty = self.check_expr(expr, ty.as_ref().map_or(
                    Expectation::None,
                    |ty|{
                        Expectation::CoercesTo(ty)
                    })
                );
                let ty = if let Some(ty) = (expr_ty.is_error() || expr_ty.is_never()).then_some(ty).flatten(){
                    ty
                }
                else{
                    expr_ty
                };
                self.check_pattern(pattern,ty);
                
            }
            hir::StmtKind::Item(item) => {
                let item =  self.lowered_items[*item].take().expect("All items should only be checked once and should be some initially");
                match item{
                    LoweredItem::Struct(struct_index) => {
                        let mut repeated_fields = Vec::new();
                        let mut seen_fields = FxHashSet::default();
                        for field in self.context.expect_struct(struct_index).fields.iter(){
                            if !seen_fields.insert(field.name.index){
                                repeated_fields.push(field.name);
                            }
                        }
                        for field in repeated_fields{
                            self.error(format!("Repeated field '{}'.",self.ident_interner.get(field.index)),field.span);
                        }
                    },
                    LoweredItem::Function(index,ref param_patterns,ref body) => {
                        let sig = self.context.expect_function(index).sig.clone();
                        self.check_function(&sig, param_patterns.iter(), body);
                    }
                }
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
            _ => todo!("REST")
        };
        self.store_type(pattern.id, ty);
    }
    fn check_type_is_expected(&mut self, ty : Type, expected_type : &Type, span : SourceLocation) -> Type{
        self.check_type_equals_with(ty, expected_type.clone(), span, |this,span,ty,expected_type:&Type|{
            let expected_ty = this.format_type(&expected_type);
            let got_ty = this.format_type(&ty);
            this.error(format!("Expected type '{}' got '{}'.",expected_ty,got_ty), span)

        })
    }
    fn check_type_coerces_to(&mut self,from:Type,to:Type,span:SourceLocation) -> Type{
        if from == to || from.is_never() || from.is_error(){
            from
        }
        else{
            if !(from.is_error()|| to.is_error()){
                let expected_ty = self.format_type(&to);
                let got_ty = self.format_type(&from);
                self.error(format!("Expected type '{}' got '{}'.",expected_ty,got_ty), span)
            }
            Type::new_error()
        }
    }
    fn check_type_equals_with(&mut self,ty1:Type,ty2:Type,span:SourceLocation,mut err : impl FnMut(&mut Self,SourceLocation,&Type,&Type)) -> Type{
        if ty1 == ty2{
            ty1
        }
        else{
            if !(ty1.is_error() || ty2.is_error()){
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
                let current_element = self.check_expr(element,element_type.as_ref().map_or(Expectation::None,|ty|Expectation::CoercesTo(ty)));
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
            element_types.as_slice()
        } 
        else{
            &[]
        };
        let element_types = elements.iter().enumerate().map(|(i,element)|{
            let expected_element = match element_types.get(i){
                Some(ty) => Expectation::CoercesTo(&ty),
                None => Expectation::None
            };
            self.check_expr(element, expected_element)
        }).collect();
        Type::new_tuple(element_types)
    }
    fn check_match_expr(&mut self,matchee:&hir::Expr,arms:&[hir::MatchArm]) -> Type{
        let matchee_ty = self.check_expr(matchee, Expectation::None);
        let mut result_ty = Type::Never;
        for arm in arms{
            self.check_pattern(&arm.pat, matchee_ty.clone());
            let body_ty = self.check_expr(&arm.body, Expectation::None);
            if !body_ty.is_never() && result_ty.is_never(){
                result_ty = body_ty;
            }
            else{
                result_ty = self.check_type_equals_with(body_ty, result_ty,arm.pat.span,|this,span,body_ty,result_ty|{
                    let prev = this.format_type(body_ty);
                    let got = this.format_type(result_ty);
                    this.error(format!("'match' arms have incompatible types '{}' and '{}'.",prev,got), span);
                });
            }
        }
        result_ty
    }
    fn check_if_expr(&mut self,condition:&hir::Expr,then_branch:&hir::Expr,else_branch:Option<&hir::Expr>) -> Type{
        self.check_expr(condition, Expectation::CoercesTo(&Type::Bool));
        let then_ty = self.check_expr(then_branch, Expectation::None);
        if let Some(else_branch) = else_branch.as_ref(){
            let else_ty = self.check_expr(else_branch, Expectation::None);
            self.check_type_equals_with(then_ty, else_ty,else_branch.span,|this,span,then_ty,else_ty|{
                let then = this.format_type(&then_ty);
                let else_ = this.format_type(else_ty);
                this.error(format!("'if' and 'else' branches have incompatible types '{}' and '{}'.",then,else_), span);
            })
        }
        else{
            self.check_type_equals_with(then_ty, Type::new_unit(),then_branch.span,|this,span,then_ty,_|{
                let then = this.format_type(&then_ty);
                this.error(format!("'if' of type '{}' must have else.",then), span);
            })
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
    fn check_call_expr(&mut self,callee:&hir::Expr,args:&[hir::Expr]) -> Type{
        let (callee_ty,mut generic_args) = self.check_expr_with_holes(callee, Expectation::None);
        if let Type::Function(params, return_type) = callee_ty{
            if params.len() == args.len(){
                
                if !generic_args.is_empty(){
                        
                }
                params.iter().zip(args.iter()).for_each(|(param,arg)|{
                    self.check_expr(arg, Expectation::CoercesTo(param));
                });
                *return_type
            }
            else{
                self.new_error(format!("Expected '{}' args got '{}'.",params.len(),args.len()), callee.span)
            }
        }
        else{
            let callee_string = self.format_type(&callee_ty);
            self.new_error(format!("Cannot call '{}'.",callee_string), callee.span)
        }
    }
    fn check_expr_with_holes(&mut self,expr:&hir::Expr,expected : Expectation) -> (Type,Vec<Option<Type>>){
        if let hir::ExprKind::Path(path) =  &expr.kind{
            match path.def{
                hir::PathDef::Function(function) => {
                    let func=  self.context.expect_function(function);
                    if !func.generics.is_empty(){
                        let last_segment = path.segments.last().expect("There has to be at least 1 path segment");
                        if last_segment.args.is_empty(){
                            return (func.sig.as_type(),func.generics.iter().map(|_| None).collect());
                        }
                    }
                },
                _ => {}
            }
        }
        (self.check_expr(expr, expected),vec![])
    }
    pub(super) fn check_expr(&mut self,expr:&hir::Expr,expected:Expectation) -> Type{
        let ty = match &expr.kind{
            hir::ExprKind::Literal(literal) => {
                self.check_literal_expr(literal)
            },
            hir::ExprKind::Array(elements) => {
                self.check_array_expr(expr.span,elements,expected)
            },
            hir::ExprKind::Tuple(elements) => {
                self.check_tuple_expr(elements, expected)
            },
            hir::ExprKind::If(condition, then_branch, else_branch) => {
                self.check_if_expr(condition, then_branch, else_branch.as_ref().map(|else_branch| else_branch.as_ref()))
            },
            hir::ExprKind::Block(stmts, result_expr) => {
                self.check_block_expr(stmts, result_expr.as_ref().map(|expr| expr.as_ref()), expected)
            },
            hir::ExprKind::Path(path) => {
                self.check_expr_path(path, expected)
            },
            hir::ExprKind::Index(base, index) => {
                let base_ty = self.check_expr(base, Expectation::None);
                self.check_expr(index, Expectation::HasType(&Type::Int));
                if let Type::Array(element_type) = base_ty{
                    *element_type
                }
                else{
                    let base_ty_string = TypeFormatter::new(&mut *self.ident_interner, &mut self.context).format_type(&base_ty);
                    self.new_error(format!("Cannot get element of '{}'.",base_ty_string), base.span)
                }

            },
            hir::ExprKind::Assign(lhs, rhs) => {
                let lhs_ty = self.check_expr(lhs, Expectation::None);
                self.check_expr(rhs, Expectation::CoercesTo(&lhs_ty));
                Type::new_unit()
            },
            &hir::ExprKind::Typename(id,ref ty) => {
                let ty = self.lower_type(ty);
                self.store_type(id, ty);
                Type::String
            },
            hir::ExprKind::While(condition, body) => {
                self.check_expr(condition, Expectation::CoercesTo(&Type::Bool));
                self.check_expr(body, Expectation::CoercesTo(&Type::new_unit()))
            },
            hir::ExprKind::Print(args) => {
                for arg in args{
                    self.check_expr(arg, Expectation::None);
                }
                Type::new_unit()
            },
            hir::ExprKind::Call(callee, args) => {
                self.check_call_expr(callee,args)
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
                self.check_match_expr(matchee,arms)
            },
            hir::ExprKind::Return(return_expr) => {
                let return_type = if let Some(FuncContext { return_type,.. }) = self.prev_functions.last(){
                    Some(return_type.clone())
                }
                else{
                    self.error(format!("'return' outside of function."), expr.span);
                    None
                };
                if let Some(return_expr) = return_expr.as_ref(){
                    self.check_expr(return_expr, return_type.as_ref().map_or(Expectation::None,|ty| Expectation::CoercesTo(ty)));
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
                let param_patterns = function.params.iter().map(|param| &param.pattern);
                let param_types = function.params.iter().map(|param| self.lower_type(&param.ty)).collect();
                let return_type = function.return_type.as_ref().map_or_else(|| Type::new_unit(), |ty| self.lower_type(ty));
                let sig = FuncSig{params:param_types,return_type};
                self.check_function(&sig, param_patterns, &function.body);
                sig.as_type()
            },
            hir::ExprKind::Field(base, field) => {
                let base_ty = self.check_expr(base, Expectation::None);
                let field_ty = if let &Type::Struct(ref _generic_args,index) = &base_ty{
                    self.context.expect_struct(index).fields.iter().find(|field_def|{
                        field_def.name.index == field.index
                    }).map(|field_def| field_def.ty.clone())
                    
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
            hir::ExprKind::StructLiteral(_path, _fields) => {
                todo!("STRUCT LITERALS")
            }
        };
        
        let ty = match expected{
            Expectation::HasType(expected_type) => {
                self.check_type_is_expected(ty, expected_type, expr.span)
            },
            Expectation::CoercesTo(expected_type) => {
                self.check_type_coerces_to(ty, expected_type.clone(), expr.span)
            }
            Expectation::None => {
                ty
            }
        };
        self.store_type(expr.id, ty.clone());
        ty
    }

    fn check_expr_path(&mut self,path:&hir::Path,_expected:Expectation) -> Type{
        match path.def{
            hir::PathDef::Variable(variable) => {
                self.env.get_variable_type(variable)
            },
            hir::PathDef::Function(function) => {
                let def = self.context.expect_function(function);
                def.sig.as_type()
            }
            _ => todo!("The rest of the path exprs")
            
        }
    }
}