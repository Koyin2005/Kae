use std::{collections::HashSet, rc::Rc};

use indexmap::{IndexMap, IndexSet};

use crate::frontend::{parsing::ast::{ExprNode, ExprNodeKind, LiteralKind, ParsedAssignmentTarget, ParsedAssignmentTargetKind, ParsedBinaryOp, ParsedFunction, ParsedGenericArgs, ParsedGenericParam, ParsedGenericParams, ParsedLogicalOp, ParsedType, ParsedUnaryOp, PatternMatchArmNode, StmtNode, Symbol}, tokenizing::SourceLocation, typechecking::typed_ast::TypedPatternMatchArm};

use super::{generics:: substitute, names::{Environment, Structs, ValueKind}, patterns::PatternChecker, typed_ast::{BinaryOp, LogicalOp, NumberKind, PatternNode, TypedAssignmentTarget, TypedAssignmentTargetKind, TypedExprNode, TypedExprNodeKind, TypedFunction, TypedFunctionSignature, TypedStmtNode, UnaryOp}, types::{FunctionId, GenericArgs, Type}};
#[derive(Clone)]
struct EnclosingFunction{
    return_type : Type
}
#[derive(Clone,Copy,PartialEq,Debug,Eq,Hash)]
pub struct GenericTypeId(usize);
pub struct TypeCheckFailed;
#[derive(Default)]
pub struct TypeChecker{
    environment : Environment,
    enclosing_functions : Vec<EnclosingFunction>,
    generic_param_names : Vec<(String,usize)>,

    structs : Structs,
    next_generic_type : usize,
    next_function_id : FunctionId
}
impl TypeChecker{
    fn begin_scope(&mut self)->Environment{
        let mut new_env = self.environment.clone();
        new_env.begin_scope();
        std::mem::replace(&mut self.environment, new_env)
    }
    fn end_scope(&mut self,old_env:Environment){
        self.environment = old_env;
    }
    fn error(&self,message:String,line:u32){
        eprintln!("Error on line {}: {}",line,message);
    }
    fn type_mismatch_error(&self,line:u32,expected:&Type,got:&Type){
        self.error(format!("Expected \"{}\" got \"{}\".",expected,got),line);
    }
    fn add_variables_in_pattern(&mut self,pattern:&PatternNode,ty:&Type){
        let mut variables = Vec::new();
        PatternChecker::collect_variables_in_pattern(pattern,ty, &mut variables);
        self.environment.add_variables(variables.into_iter().map(|(name_symbol,ty)| (name_symbol.content,ty)));
        
    }
    fn value_scope_error(&mut self,name:&str,line:u32){
        self.error(format!("Cannot find value '{}' in scope.",name), line);
    }
    fn check_type_match(&mut self,ty:&Type,expected_type:&Type,line:u32)->Result<(),TypeCheckFailed>{
        if ty != expected_type &&  ty != &Type::Never{
            self.type_mismatch_error(line, expected_type, ty);
            return Err(TypeCheckFailed);
        }
        Ok(())
    }
    fn check_signature(&mut self,function:&ParsedFunction)->Result<TypedFunctionSignature,TypeCheckFailed>{
        let params = match function.params.iter().map(|param|{
            let pattern = PatternChecker::get_pattern(&param.pattern)?;
            if let Err(refutable_pattern) = PatternChecker::check_irrefutable(&pattern){
                self.error("Can't use non-irrefutable pattern in function parameter.".to_string(), refutable_pattern.location.start_line);
                return Err(TypeCheckFailed);
            }
            let ty = self.check_type(&param.ty)?;
            if let Err(pattern_type) = PatternChecker::check_pattern_type(&pattern, &ty){
                    self.type_mismatch_error(pattern.location.start_line,&ty, &pattern_type);
                    return Err(TypeCheckFailed);
            };
            Ok((pattern,ty))
        }).collect::<Result<Vec<_>,TypeCheckFailed>>(){
            Ok(params) => params,
            Err(_) => {
                return Err(TypeCheckFailed);
            }
        };
        let return_type = match function.return_type.as_ref().map_or(Ok(Type::Unit), |return_type| self.check_type(return_type)){
            Ok(ty) => ty,
            Err(_) => {
                return Err(TypeCheckFailed);
            }
        };
        Ok(TypedFunctionSignature { params, return_type })

    }
    fn check_function(&mut self,function:&ParsedFunction,signature : TypedFunctionSignature)->Result<TypedFunction, TypeCheckFailed>{
        fn finish_function(this:&mut TypeChecker,old_env: Environment){
            this.end_scope(old_env);
            this.enclosing_functions.pop();
        }
        let old_env = self.begin_scope();
        self.enclosing_functions.push(EnclosingFunction { return_type:  signature.return_type.clone()});

        let mut variable_names =  IndexSet::new();
        for (pattern,ty) in &signature.params{
            let mut variables = Vec::new();
            PatternChecker::collect_variables_in_pattern(pattern, ty,&mut variables);
            for name in variables.iter().map(|(name,_)| name){
                if !variable_names.insert(name.content.clone()){
                    self.error(format!("Repeated parameter with name '{}'.",name.content),name.location.start_line);
                    finish_function(self, old_env);
                    return Err(TypeCheckFailed);
                }
            }
            self.environment.add_variables(variables.into_iter().map(|(name,ty)| (name.content,ty)));
        }
        let body = match self.check_expr_type(&function.body, &signature.return_type){
            Ok(body) => body,
            Err(_) => {
                finish_function(self, old_env);
                return Err(TypeCheckFailed);
            }
        };
        finish_function(self, old_env);
        Ok(TypedFunction{
            signature,
            body:Box::new(body)
        })

    }

    fn get_type_of_value(&self,name:&str) -> Option<(Type,ValueKind)>{
        Some(if let Some(ty) = self.environment.get_variable(name){
            (ty.clone(),ValueKind::Variable)
        }
        else if let Some(ty) = self.environment.get_function_type(name){
            (ty,ValueKind::Function)
        }
        else{
            return None
        })
    }
    fn infer_index_expr_type(&mut self,location : SourceLocation,lhs:&ExprNode,rhs:&ExprNode)->Result<(Type,TypedExprNode,TypedExprNode),TypeCheckFailed>{
        
        let lhs = self.infer_expr_type(lhs)?;
        let rhs = self.infer_expr_type(rhs)?;
        let (Type::Array(element),Type::Int) = (&lhs.ty,&rhs.ty) else {
            self.error(format!("Cannot index into \"{}\" with \"{}\".",&lhs.ty,&rhs.ty),location.start_line);
            return Err(TypeCheckFailed);
        };
        Ok((*element.clone(),lhs,rhs))
    }

    fn check_value_in_scope(&mut self,name:&str,location : SourceLocation)->Result<Type,TypeCheckFailed>{
        if let Some((ty,kind)) = self.get_type_of_value(name){
            match kind{
                ValueKind::Variable => Ok(ty.clone()),
                ValueKind::Function => {
                    self.error(format!("Cannot assign to function '{}'.",name), location.start_line);
                    Err(TypeCheckFailed)
                }
            }
        } else {
            self.error(format!("Cannot find value '{}' in scope.",name), location.start_line);
            Err(TypeCheckFailed)
        }

    }
    fn infer_assignment_target(&mut self,assignment_target : &ParsedAssignmentTarget)->Result<TypedAssignmentTarget,TypeCheckFailed>{
        let (ty,kind) = match &assignment_target.kind{
            ParsedAssignmentTargetKind::Name(name) => {
                (self.check_value_in_scope(name,assignment_target.location)?,TypedAssignmentTargetKind::Name(name.clone()))
            },
            ParsedAssignmentTargetKind::Index { lhs, rhs } => {
                let (ty,lhs,rhs) = self.infer_index_expr_type(assignment_target.location,lhs,rhs)?;
                (ty,TypedAssignmentTargetKind::Index { lhs: Box::new(lhs), rhs: Box::new(rhs) })
                
            },
            ParsedAssignmentTargetKind::Field { lhs, field } => {
                let lhs = self.infer_expr_type(lhs)?;
                let field_type = if matches!((&lhs.ty,&field.content as &str),(Type::Array(_),"length")) { 
                    self.error(format!("Cannot assign to field \'length\' of \"{}\".",lhs.ty),field.location.start_line);
                    return Err(TypeCheckFailed);
                 } else {
                    lhs.ty.get_field(&field.content, &self.structs) 
                };
                let Some(field_type) = field_type else{
                    self.error(format!("\"{}\" has no field '{}'.",lhs.ty,field.content), field.location.start_line);
                    return Err(TypeCheckFailed);
                };
                (field_type,TypedAssignmentTargetKind::Field{lhs:Box::new(lhs),name:field.clone()})
            }
        };
        Ok(TypedAssignmentTarget { location: assignment_target.location, ty, kind })
    }
    fn check_or_infer_expr_type(&mut self,expr:&ExprNode,expected_type : Option<&Type>) -> Result<TypedExprNode,TypeCheckFailed>{
        if let Some(expected_type) = expected_type{
            self.check_expr_type(expr, expected_type)
        }
        else{
            self.infer_expr_type(expr)
        }
    }
    fn check_expr_type(&mut self,expr:&ExprNode,expected:&Type)->Result<TypedExprNode,TypeCheckFailed>{
        let expr = match (&expr.kind,expected){
            (ExprNodeKind::Array(elements),Type::Array(element_type)) if elements.is_empty() => {
                TypedExprNode{
                    location:expr.location,
                    kind:TypedExprNodeKind::Array(Vec::new()),
                    ty:Type::Array(element_type.clone())
                }
            },
            (ExprNodeKind::Grouping(expr),ty) => self.check_expr_type(expr, ty)?,
            (ExprNodeKind::Block { stmts, expr:result_expr },ty) => {
                let (ty,kind) = self.infer_or_check_block_expr_type(stmts, result_expr.as_ref().map(|expr| expr.as_ref()), Some(ty))?;
                TypedExprNode{ location:expr.location, ty, kind}
            }
            (ExprNodeKind::Tuple(elements),Type::Tuple(element_types)) if element_types.len() == elements.len() => {
                let elements = elements.iter().zip(element_types.iter()).map(|(element,ty)| self.check_expr_type(element, ty)).collect::<Result<Vec<_>,_>>()?;
                TypedExprNode{ location: expr.location,ty : Type::Tuple(element_types.clone()),kind : TypedExprNodeKind::Tuple(elements) }
            },
            (ExprNodeKind::Match { matchee, arms },ty) => self.infer_match_expr_type(expr.location, Some(ty.clone()), matchee, arms)?,
            (ExprNodeKind::If { condition, then_branch, else_branch },ty) => {
                let (ty,kind) = self.infer_or_check_if_expr_type(expr.location, condition, then_branch, else_branch.as_ref().map(|expr| expr.as_ref()), Some(ty))?;
                TypedExprNode{location:expr.location,ty,kind}
            },
            _ => self.infer_expr_type(expr)?
        };
        if self.check_type_match(&expr.ty, expected,expr.location.start_line).is_ok(){
            Ok(expr)
        }
        else{
            Err(TypeCheckFailed)
        }
    }

    fn infer_or_check_block_expr_type(&mut self,stmts:&[StmtNode],expr:Option<&ExprNode>,expected_type : Option<&Type>)->Result<(Type, TypedExprNodeKind), TypeCheckFailed>{
        let old_env = self.begin_scope();
        let stmts = match self.check_stmts(stmts){
            Ok(stmts) => stmts,
            Err(_) => {
                self.end_scope(old_env);
                return Err(TypeCheckFailed);
            }
        };
        let expr = if let Some(expr) = expr.as_ref() { 
            Some(match if let Some(ty) = expected_type { self.check_expr_type(expr, ty)} else {self.infer_expr_type(expr)}{
                Ok(expr) => expr,
                Err(_) => {
                    self.end_scope(old_env);
                    return Err(TypeCheckFailed);
                }
            })
        } else { None};
        self.end_scope(old_env);

        let ty = expr.as_ref().map(|expr| expr.ty.clone()).unwrap_or_else(||{
            let is_never = stmts.iter().any(|stmt| {
                matches!(stmt,TypedStmtNode::Let {  expr,.. } | TypedStmtNode::Expr(expr) | TypedStmtNode::ExprWithSemi(expr) if expr.ty == Type::Never)
            });
            if is_never { Type::Never } else {Type::Unit}
        });
        Ok((ty,TypedExprNodeKind::Block { stmts, expr:expr.map(Box::new) }))

    }
    fn infer_or_check_if_expr_type(&mut self,location : SourceLocation,
        condition:&ExprNode,then_branch:&ExprNode,else_branch:Option<&ExprNode>,
        expected_type : Option<&Type>)->Result<(Type,TypedExprNodeKind),TypeCheckFailed>{
        
        let condition = self.check_expr_type(condition, &Type::Bool)?;
        let then_branch = self.check_or_infer_expr_type(then_branch,expected_type)?;
        let else_branch = else_branch.as_ref().map_or(Ok(None),|else_branch|
             self.check_or_infer_expr_type(else_branch,expected_type).map(Some))?;
             
        let ty = if let Some(else_branch) = else_branch.as_ref() { match (&then_branch.ty,&else_branch.ty){
            (Type::Never,ty) | (ty,Type::Never) => ty.clone(),
            (then_branch,else_branch)  if then_branch == else_branch => then_branch.clone(),
            (then_branch,else_branch_type) => {
                self.error(format!("Expected \'else\' to have type \"{}\" got \"{}\".",then_branch,else_branch_type),else_branch.location.start_line);
                return Err(TypeCheckFailed);
            } 
        } } else if matches!(&then_branch.ty,Type::Unit|Type::Never) {
           then_branch.ty.clone()
        } else {
            self.error(format!("'if' of type '{}' must have else.",then_branch.ty), location.start_line);
            return Err(TypeCheckFailed);
        };
        Ok((ty,TypedExprNodeKind::If { condition:Box::new(condition), then_branch: Box::new(then_branch), else_branch: else_branch.map(Box::new) }))
    }
    fn infer_match_expr_type(&mut self,location : SourceLocation,mut expected_type : Option<Type>,matchee:&ExprNode,arms:&[PatternMatchArmNode])->Result<TypedExprNode, TypeCheckFailed> {
            let matchee = self.infer_expr_type(matchee)?;
            let arms = arms.iter().map(|arm|{
                let pattern = PatternChecker::get_pattern(&arm.pattern)?;
                let pattern_type = match PatternChecker::check_pattern_type(&pattern,&matchee.ty){
                    Ok(ty) => ty,
                    Err(pattern_type) => {
                        self.type_mismatch_error(pattern.location.start_line, &matchee.ty, &pattern_type);
                        return Err(TypeCheckFailed);
                    }
                };
                
                let old_env = self.begin_scope();
                let mut variables = Vec::new();
                PatternChecker::collect_variables_in_pattern(&pattern,&pattern_type, &mut variables);
                self.environment.add_variables(variables.into_iter().map(|(name_symbol,ty)| (name_symbol.content,ty)));
                let arm_expr = match self.infer_expr_type(&arm.expr){
                    Ok(arm_expr) => arm_expr,
                    Err(_) => {
                        self.end_scope(old_env);
                        return Err(TypeCheckFailed);
                    }
                };
                if let None | Some(Type::Never) = expected_type{
                    expected_type = Some(arm_expr.ty.clone());
                }
                self.end_scope(old_env);
                Ok(TypedPatternMatchArm{ pattern,ty:pattern_type,expr:arm_expr,location:arm.location})
            }).collect::<Result<Vec<_>,_>>()?;
            if !PatternChecker.is_exhaustive(&matchee.ty, &arms.iter().map(|TypedPatternMatchArm{pattern,..}| pattern).collect::<Box<_>>()){
                self.error("Non exhaustive pattern match.".to_string(),location.start_line);
                return Err(TypeCheckFailed);
            }
            Ok(TypedExprNode{
                location,
                ty : expected_type.unwrap_or(Type::Unit),
                kind : TypedExprNodeKind::Match { matchee:Box::new(matchee), arms }
            })
    }
    fn infer_expr_type(&mut self,expr:&ExprNode)->Result<TypedExprNode,TypeCheckFailed>{
        let (ty,kind) = match &expr.kind{
            ExprNodeKind::Array(elements) => {
                if elements.is_empty(){
                    self.error("Cannot infer type of empty array.".to_string(),expr.location.start_line);
                    return Err(TypeCheckFailed);
                }
                else{
                    let first_element = self.infer_expr_type(elements.first().unwrap())?;
                    let ty = first_element.ty.clone();
                    let elements = std::iter::once(Ok(first_element)).chain(
                        elements.iter().skip(1).map(|element| {
                            self.check_expr_type(element,&ty)
                        })).collect::<Result<Vec<_>,_>>()?;
                    
                    (Type::Array(Box::new(ty)),TypedExprNodeKind::Array(elements))
                }
            },
            ExprNodeKind::Literal(literal) => {
                match literal{
                    &LiteralKind::Int(value) => (Type::Int,TypedExprNodeKind::Number(NumberKind::Int(value))),
                    &LiteralKind::Float(value) => (Type::Float,TypedExprNodeKind::Number(NumberKind::Float(value))),
                    LiteralKind::String(value) => (Type::String,TypedExprNodeKind::String(Rc::from(value as &str))),
                    &LiteralKind::Bool(value) => (Type::Bool,TypedExprNodeKind::Bool(value)),

                }
            },
            ExprNodeKind::Grouping(expr) => {
                let TypedExprNode { ty, kind,.. } = self.infer_expr_type(expr)?;
                (ty,kind)
            },
            ExprNodeKind::If { condition, then_branch, else_branch } => {
                self.infer_or_check_if_expr_type(expr.location,condition,then_branch,else_branch.as_ref().map(|expr| expr.as_ref()),None)?
            },
            ExprNodeKind::While { condition, body } =>{
                let condition = self.check_expr_type(condition, &Type::Bool)?;
                let body = self.check_expr_type(body, &Type::Unit)?;
                (Type::Unit,TypedExprNodeKind::While { condition: Box::new(condition), body: Box::new(body) })
            },
            ExprNodeKind::Return(return_expr) => {
               let Some(EnclosingFunction {return_type,.. }) = self.enclosing_functions.last().cloned() else{
                    self.error("'return' outside of function.".to_string(),expr.location.start_line);
                    return Err(TypeCheckFailed)
                };
                let return_expr = if let Some(expr) = return_expr.as_ref() {
                    Some(self.check_expr_type(expr, &return_type)?)
                }
                else if return_type != Type::Unit{
                    self.error("'return' with no expression inside function that does not return \"()\".".to_string(),expr.location.start_line);
                    return Err(TypeCheckFailed);
                }
                else{
                    None
                };
                (Type::Never,TypedExprNodeKind::Return { expr: return_expr.map(Box::new) })
            },
            ExprNodeKind::Index { lhs, rhs } => {
                let (element_type,lhs,rhs) = self.infer_index_expr_type(lhs.location, lhs, rhs)?;
                (element_type,TypedExprNodeKind::Index { lhs:Box::new(lhs), rhs:Box::new(rhs) })
            },
            ExprNodeKind::Unary { op, operand } => {
                let op = match op{
                    ParsedUnaryOp::Negate => UnaryOp::Negate,
                };
                let operand = self.infer_expr_type(operand)?;
                let result_type = match (op,&operand.ty){
                    (UnaryOp::Negate,ty @ (Type::Int|Type::Float)) => Some(ty),
                    _ => None
                };
                let Some(result_type) = result_type.cloned() else {
                    self.error(format!("'{}' does not support \"{}\" operand.",op,operand.ty), operand.location.start_line);
                    return Err(TypeCheckFailed);
                };
                (result_type,TypedExprNodeKind::Unary { op, operand: Box::new(operand) })
            }
            ExprNodeKind::Print(exprs) => {
                let exprs = exprs.iter().map(|expr| {
                    self.infer_expr_type(expr)
                }).collect::<Result<Vec<_>,_>>()?;
                (Type::Unit,TypedExprNodeKind::Print(exprs))
            },
            ExprNodeKind::Tuple(elements) => {
                if elements.is_empty(){
                    (Type::Unit,TypedExprNodeKind::Unit)
                }
                else{
                    let elements = elements.iter().map(|element| self.infer_expr_type(element)).collect::<Result<Vec<_>,_>>()?;
                    (Type::Tuple(elements.iter().map(|element| element.ty.clone()).collect()),TypedExprNodeKind::Tuple(elements))
                }
            },
            ExprNodeKind::Block { stmts, expr } => {
                self.infer_or_check_block_expr_type(stmts, expr.as_ref().map(|expr| expr.as_ref()), None)?
            },
            ExprNodeKind::Get(name) => {
                match self.get_type_of_value(name){
                    Some((ty,kind)) => {
                        if let (Some(args),ValueKind::Function) = (ty.get_generic_args(),kind){
                            if args.is_empty(){
                                (ty,TypedExprNodeKind::Get(name.clone()))
                            }
                            else{
                                self.error(format!("Cannot use generic function '{}' without generic arguments.",name), expr.location.start_line);
                                return Err(TypeCheckFailed);
                            }
                        }
                        else if !ty.is_unknown(){
                            (ty.clone(),TypedExprNodeKind::Get(name.clone()))
                        }
                        else{
                            return Err(TypeCheckFailed);
                        }
                    },
                    _ =>  {
                        self.value_scope_error(name, expr.location.start_line);
                        return Err(TypeCheckFailed);
                    }
                }
            },
            ExprNodeKind::Match { matchee, arms } => {
                let TypedExprNode { ty, kind,.. } =  self.infer_match_expr_type(expr.location, None, matchee, arms)?;
                (ty,kind)
            },
            ExprNodeKind::Function(function) => {
                let signature = self.check_signature(function)?;
                let function = self.check_function(function,signature)?;
                (Type::Function { generic_args:GenericArgs::default(), params: function.signature.params.iter().map(|(_,ty)| ty.clone()).collect(), return_type:Box::new(function.signature.return_type.clone()) },TypedExprNodeKind::Function(function))
            },
            ExprNodeKind::GetGeneric(name, args) => {
                let ParsedGenericArgs{
                    location,
                    types
                } = &args;

                let ty = if let Some(ty) = self.environment.get_function_type(name){
                    if !ty.is_unknown(){
                        ty.clone()
                    }
                    else{
                        return Err(TypeCheckFailed);
                    }
                }
                else {
                    self.value_scope_error(name, expr.location.start_line);
                    return Err(TypeCheckFailed);
                };
                let args = types.iter().map(|ty| self.check_type(ty)).collect::<Result<Vec<Type>,_>>()?;
                let Some(mut params) = ty.get_generic_args() else{
                    self.error(format!("Cannot apply generic args to non-generic type \"{}\".",ty),location.start_line);
                    return Err(TypeCheckFailed);
                };
                if args.len() != params.len(){
                    self.error(format!("Expected '{}' generic args got '{}'.",params.len(),args.len()), location.start_line);
                    return Err(TypeCheckFailed);
                }
                for (value,ty) in params.values_mut().zip(args.iter().cloned()){
                    *value = ty;
                }

                (substitute(ty,&params),TypedExprNodeKind::GetGeneric{name:name.clone(), args })
            },
            ExprNodeKind::Logical { op, left, right } => {
                let op = match op {
                    ParsedLogicalOp::And => LogicalOp::And,
                    ParsedLogicalOp::Or => LogicalOp::Or
                };
                let left = self.infer_expr_type(left)?;
                let right = self.infer_expr_type(right)?;
                let output_type = match(&left.ty,&right.ty,op){
                    (Type::Bool,Type::Bool,_) => Some(Type::Bool),
                    _ => None
                };
                let Some(output_type) = output_type else{
                    self.error(format!("'{}' does not support \"{}\" and \"{}\"",op,left.ty,right.ty),expr.location.start_line);
                    return Err(TypeCheckFailed);
                }; 
                (output_type,TypedExprNodeKind::Logical{op,left:Box::new(left),right:Box::new(right)})

            },
            ExprNodeKind::BinaryOp { op, left, right } => {
                let op = match op {
                    ParsedBinaryOp::Add => BinaryOp::Add,
                    ParsedBinaryOp::Subtract => BinaryOp::Subtract,
                    ParsedBinaryOp::Multiply => BinaryOp::Multiply,
                    ParsedBinaryOp::Divide => BinaryOp::Divide,
                    ParsedBinaryOp::Lesser => BinaryOp::Lesser,
                    ParsedBinaryOp::Greater => BinaryOp::Lesser,
                    ParsedBinaryOp::LesserEquals => BinaryOp::LesserEquals,
                    ParsedBinaryOp::GreaterEquals => BinaryOp::GreaterEquals,
                    ParsedBinaryOp::Equals => BinaryOp::Equals,
                    ParsedBinaryOp::NotEquals => BinaryOp::NotEquals,
                };
                let left = self.infer_expr_type(left)?;
                let right = self.infer_expr_type(right)?;
                let output_type = match (&left.ty,&right.ty,op){
                    (left,right,BinaryOp::Equals|BinaryOp::NotEquals)  if left == right=> Some(Type::Bool),
                    ( left @(Type::Int|Type::Float),right @ (Type::Int|Type::Float),
                        BinaryOp::Lesser|BinaryOp::LesserEquals|BinaryOp::Greater|BinaryOp::GreaterEquals) if left == right => Some(Type::Bool),
                    (Type::Int,Type::Int,_) => Some(Type::Int),
                    (Type::Float,Type::Float,_) => Some(Type::Float),
                    (Type::String,Type::String,BinaryOp::Add) => Some(Type::String),
                    _ => None
                };
                let Some(output_type) = output_type else{
                    self.error(format!("'{}' does not support \"{}\" and \"{}\"",op,left.ty,right.ty),expr.location.start_line);
                    return Err(TypeCheckFailed);
                };
                (output_type,TypedExprNodeKind::Binary { op, left: Box::new(left), right: Box::new(right) })
            },
            ExprNodeKind::Assign { lhs, rhs } => {
                let lhs = self.infer_assignment_target(lhs)?;
                let rhs = self.infer_expr_type(rhs)?;
                if lhs.ty != rhs.ty {
                    self.error(format!("Cannot assign a value of type \"{}\" to \"{}\".",rhs.ty,lhs.ty),rhs.location.end_line);
                    return Err(TypeCheckFailed);
                }
                (lhs.ty.clone(),TypedExprNodeKind::Assign { lhs, rhs: Box::new(rhs) })
            },
            ExprNodeKind::Call { callee, args } =>{
                let callee = self.infer_expr_type(callee)?;
                let (arg_types,return_type) = match &callee.ty{
                    Type::Function { params:arg_types, return_type ,..}=> {
                        (arg_types,return_type)
                    },
                    _ => {
                        self.error(format!("Cannot call \"{}\".",callee.ty),callee.location.start_line);
                        return Err(TypeCheckFailed);
                    }
                };

                if arg_types.len() != args.len(){
                    self.error(format!("Expected \'{}\' args got \'{}\'.",arg_types.len(),args.len()),expr.location.start_line);
                    return Err(TypeCheckFailed);
                }
                let args = arg_types.iter().zip(args.iter()).map(|(ty,arg)| {
                    self.check_expr_type(arg, ty)
                }).collect::<Result<Vec<_>,_>>()?;
                (*return_type.clone(),TypedExprNodeKind::Call { callee:Box::new(callee), args })
                
            },
            ExprNodeKind::TypenameOf(ty) => {
                let ty = self.check_type(ty)?;
                (Type::String,TypedExprNodeKind::TypenameOf(ty))
            },
            ExprNodeKind::Property(lhs, property) => {
                let lhs = self.infer_expr_type(lhs)?;
                let Some(property_type) = lhs.ty.get_field(&property.content,&self.structs) else{
                    self.error(format!("\"{}\" has no field or method.",property.content),property.location.start_line);
                    return Err(TypeCheckFailed);
                };
                (property_type,TypedExprNodeKind::Field(Box::new(lhs), property.clone()))
            },
            ExprNodeKind::StructInit { name, generic_args, fields } => {
                let struct_type = self.check_type(&if let Some(generic_args)=  generic_args.as_ref().cloned(){
                    ParsedType::NameWithArgs(name.clone(), generic_args) 
                } else {
                    ParsedType::Name(name.clone())
                })?;

                let Type::Struct { generic_args, id, name } = struct_type.clone() else {
                    self.error(format!("Expected a 'struct' type got, \"{}\".",struct_type), name.location.start_line);
                    return Err(TypeCheckFailed);
                };

                let struct_info = self.structs.get_struct_info(&id).expect("Can only use valid struct ids");
                let field_names_and_types = struct_info.fields.iter().cloned().map(|(name,ty)| (name,substitute(ty, &generic_args))).collect::<IndexMap<_,_>>();
                let mut seen_fields = HashSet::new();
                let fields = fields.iter().map(|(field_name,field_expr)|{

                    let Some(ty) = field_names_and_types.get(&field_name.content) else {
                        self.error(format!("'struct' {}, has no field '{}'.",name,field_name.content), field_name.location.start_line);
                        return Err(TypeCheckFailed);
                    };
                    if !seen_fields.insert(&field_name.content){
                        self.error(format!("Re-initialized field '{}'.",field_name.content), field_name.location.start_line);
                        return Err(TypeCheckFailed);
                    }
                    let field_expr = self.check_expr_type(field_expr, ty)?;
                    Ok((field_name.content.clone(),field_expr))
                }).collect::<Result<Vec<_>,_>>()?;
                if field_names_and_types.len() != seen_fields.len(){
                    let missing_fields : Vec<&String> = field_names_and_types.keys().filter(|name|{
                        !seen_fields.contains(name)
                    }).collect();
                    let missing_field_count = missing_fields.len();
                    let mut error_string = if  missing_field_count == 1 {
                        format!("Did not initialize field ")
                     } else {
                        format!("Did not initialize fields ")
                    };
                    for (i,field) in missing_fields.into_iter().enumerate(){
                        if i>0{
                            if i<=missing_field_count-1{
                                error_string.push_str(" and ");
                            }
                            else{
                                error_string.push(',');
                            }
                        }
                        error_string.push_str(&format!("'{}'",field));
                    }
                    error_string.push_str(&format!(" of struct \"{}\".",struct_type));
                    self.error(error_string, expr.location.start_line);
                    return Err(TypeCheckFailed);
                }
                (struct_type,TypedExprNodeKind::StructInit { fields })
            }

        };
        Ok(TypedExprNode { location: expr.location, ty, kind })
    }

    fn check_type(&mut self,ty:&ParsedType)->Result<Type,TypeCheckFailed>{
        fn get_named_type(this:&mut TypeChecker,name:&Symbol)->Result<Type,TypeCheckFailed>{

            Ok(match &name.content as &str{
                "int" => Type::Int,
                "float" => Type::Float,
                "string" => Type::String,
                "bool" => Type::Bool,
                "never" => Type::Never,
                type_name => {
                    if let Some((_,index)) = this.generic_param_names.iter().rev().find(|(name,_)| name == type_name){
                        Type::Param { name: type_name.to_string(), index : GenericTypeId(*index) }
                    }
                    else if let Some(ty) = this.environment.get_type(type_name){
                        ty.clone()
                    }
                    else{
                        this.error(format!("Used undefined type \"{}\".",name.content), name.location.start_line);
                        return Err(TypeCheckFailed);
                    }
                }
            })
        }
        let ty = match ty{
            ParsedType::Name(name) => {
                get_named_type(self, name)?
            },
            ParsedType::NameWithArgs(name, args) => {
                let ty = get_named_type(self, name)?;
                let generic_args = args.types.iter().map(|ty| self.check_type(ty)).collect::<Result<Vec<_>,_>>()?;
                let expected_args = match &ty { 
                    Type::Struct { generic_args, .. } if generic_args.values().all(|ty| !ty.is_closed()) => {
                        generic_args
                    },
                    ty => {
                        self.error(format!("Cannot apply generic args to non-generic type \"{}\".",ty), args.location.start_line);
                        return Err(TypeCheckFailed);
                    }
                };
                if generic_args.len() != expected_args.len(){
                    self.error(format!("Expected '{}' generic args, but got '{}'.",expected_args.len(),generic_args.len()),args.location.start_line);
                    return Err(TypeCheckFailed);
                }
                let subbed_generic_args = expected_args.keys().zip(generic_args).map(|(name,ty)|{
                    (*name,ty)
                }).collect();
                substitute(ty, &subbed_generic_args)
            },
            ParsedType::Array(element_type) => {
                Type::Array(Box::new(self.check_type(element_type)?))
            },
            ParsedType::Tuple(elements) => {
                if elements.is_empty(){
                    Type::Unit
                }
                else{
                    Type::Tuple(elements.iter().map(|ty| self.check_type(ty)).collect::<Result<_,_>>()?)
                }
            },
            ParsedType::Fun(params, return_type) => {
                Type::Function { 
                    params: params.iter().map(|param| self.check_type(param)).collect::<Result<_,_>>()?, 
                    return_type: return_type.as_ref().map_or(Ok(Type::Unit),|ty| self.check_type(ty)).map(Box::new)?,
                    generic_args:GenericArgs::default() 
                }
            }
        };
        if ty.is_unknown(){
            Err(TypeCheckFailed)
        }
        else{
            Ok(ty)
        }
    }
    fn check_generic_params(&mut self,generic_params : Option<&ParsedGenericParams>)->Result<Option<Vec<(String,usize)>>,TypeCheckFailed>{
        let mut had_error = false;
        let generic_param_count = self.generic_param_names.len();
        let generic_params = if let Some(ParsedGenericParams(generic_params)) = generic_params.as_ref(){
            let mut generic_param_names = Vec::new();
            
            for ParsedGenericParam(name) in generic_params{
                if generic_param_names.contains(&name.content){
                    self.error(format!("Repeated generic parameter name \"{}\".",name.content),name.location.start_line);
                    had_error = true;
                }
                else{
                    generic_param_names.push(name.content.clone());
                }
            }
            self.generic_param_names.extend(generic_param_names.iter().enumerate().map(|(i,name)|{
                (name.clone(),self.next_generic_type + i)
            }));
            let generic_params : Vec<(String,usize)> = generic_param_names.into_iter().enumerate().map(|(i,name)|{
                (name,self.next_generic_type + i)
            }).collect();
            self.next_generic_type += generic_params.len();
            Some(generic_params)
        }
        else{
            None
        };
        if had_error { 
            self.generic_param_names.truncate(generic_param_count);
            return Err(TypeCheckFailed);
        }
        Ok(generic_params)
    }
    fn check_stmt(&mut self,stmt:&StmtNode)->Result<TypedStmtNode,TypeCheckFailed>{
        match stmt{
            &StmtNode::Expr { ref expr, has_semi } => {
                if !has_semi{
                    Ok(TypedStmtNode::Expr( self.check_expr_type(expr, &Type::Unit)?))
                }
                else{
                    Ok(TypedStmtNode::ExprWithSemi(self.infer_expr_type(expr)?))
                }
            },
            StmtNode::Let { pattern, expr ,ty} => {

                let pattern = PatternChecker::get_pattern(pattern)?;

                let ty = if let Some(ty) = ty.as_ref(){ self.check_type(ty).map(Some)} else {Ok(None)};
                let expr = self.check_or_infer_expr_type(expr, ty.as_ref().ok().and_then(|ty| ty.as_ref()));

                let (ty,expr) = match (ty,expr){
                    (Ok(ty),Ok(expr)) => (ty,expr),
                    (Ok(Some(ty)),Err(_)) => {
                        self.add_variables_in_pattern(&pattern, &ty);
                        return Err(TypeCheckFailed);
                    },
                    (Err(_),Ok(expr)) => {
                        let ty = match PatternChecker::check_pattern_type(&pattern,&expr.ty){
                            Ok(ty) => ty,
                            Err(ty) => {
                                self.type_mismatch_error(pattern.location.start_line, &expr.ty, &ty);
                                ty
                            }
                        };
                        self.add_variables_in_pattern(&pattern, &ty);
                        return Err(TypeCheckFailed);
                    },
                    (Err(_)|Ok(None),Err(_)) => {
                        let (Ok(ty)|Err(ty)) = PatternChecker::check_pattern_type(&pattern,&Type::Unknown);
                        self.add_variables_in_pattern(&pattern, &ty);
                        return Err(TypeCheckFailed);
                    }
                };

                let ty = ty.unwrap_or_else(|| expr.ty.clone());
                if let Err(refutable_pattern) = PatternChecker::check_irrefutable(&pattern){
                    self.error("Can't use non-irrefutable pattern in 'let' statement.".to_string(), refutable_pattern.location.start_line);
                    self.add_variables_in_pattern(&pattern, &ty);
                    return Err(TypeCheckFailed);
                }
                if let Err(pattern_type) =  PatternChecker::check_pattern_type(&pattern,&expr.ty){
                    self.type_mismatch_error(pattern.location.start_line, &expr.ty, &pattern_type);
                    self.add_variables_in_pattern(&pattern, &pattern_type);
                    return Err(TypeCheckFailed);
                }
                self.add_variables_in_pattern(&pattern, &ty);
                Ok(TypedStmtNode::Let{
                    pattern,
                    expr
                })
            },
            StmtNode::Fun { name,generic_params, function } => {
                let function_name = name.content.clone();
                if self.environment.get_function_id(&function_name).is_some(){
                    self.error(format!("Repeated function name '{}'.",function_name), name.location.start_line);
                    return Err(TypeCheckFailed);
                }

                let id = self.next_function_id;
                self.next_function_id = self.next_function_id.next();

                let generic_param_count = self.generic_param_names.len();
                let Ok(generic_params) =  self.check_generic_params(generic_params.as_ref()) else{
                    self.environment.add_function(name.content.clone(), Vec::new(),Type::Unknown,id);
                    self.generic_param_names.truncate(generic_param_count);
                    return Err(TypeCheckFailed);
                };
                let signature = self.check_signature(function);
                let Ok(signature) = signature else{
                    self.environment.add_function(name.content.clone(), Vec::new(),Type::Unknown,id);
                    self.generic_param_names.truncate(generic_param_count);
                    return Err(TypeCheckFailed);
                };
                let params = signature.params.iter().map(|(_,ty)| ty).cloned().collect();
                let return_type = signature.return_type.clone();
                if let Some(names) = generic_params.clone(){
                    self.environment.add_generic_function(function_name, params, return_type, id, names.into_iter().map(|(name,index)|{
                        (GenericTypeId(index),Type::Param { name, index:GenericTypeId(index) })
                    }));
                }
                else{
                    self.environment.add_function(function_name,params, return_type, id);
                }
                
                let function =  self.check_function(function, signature);
                self.generic_param_names.truncate(generic_param_count);
                let function = function?;
                Ok(if let Some(generic_params) = generic_params {
                        TypedStmtNode::GenericFunction { name:name.clone(), function,generic_params:generic_params.into_iter().map(|(_,index)| GenericTypeId(index)).collect() } 
                    } 
                    else{
                        TypedStmtNode::Fun { name: name.clone(), function }
                    })
            },
            StmtNode::Struct { name, generic_params, fields } => {
                let generic_param_count = self.generic_param_names.len();
                let struct_name = name.content.clone();
                let Ok(generic_params) = self.check_generic_params(generic_params.as_ref()) else {
                    self.generic_param_names.truncate(generic_param_count);
                    self.environment.add_type(struct_name,Type::Unknown);
                    return Err(TypeCheckFailed);
                };
                let id = self.structs.define_struct (vec![].into_iter() );
                let generic_params = if let Some(generic_params) = generic_params.clone(){
                    let generic_params : IndexMap<_,_> = generic_params.into_iter().map(|(name,index)|{
                        (GenericTypeId(index),Type::Param { name, index : GenericTypeId(index) })
                    }).collect();
                    Some(generic_params)
                }
                else{   
                    None
                };
                self.environment.add_type(
                    struct_name.clone(), 
                Type::Struct { 
                    generic_args: generic_params.clone().unwrap_or_default(), 
                    id, 
                    name: struct_name.clone()
                });
                let mut field_names = HashSet::new();
                let Ok(fields) = fields.iter().map(|(field,ty)|{

                    let field_type = self.check_type(ty)?;
                    if !field_names.insert(&field.content){
                        self.error(format!("Repeated field '{}'.",field.content), field.location.start_line);
                        return Err(TypeCheckFailed);
                    }
                    Ok((field.clone(),field_type))
                }).collect::<Result<Vec<_>,_>>() else {
                    self.generic_param_names.truncate(generic_param_count);
                    return Err(TypeCheckFailed);
                };
                self.generic_param_names.truncate(generic_param_count);
                self.structs.update_struct_info(&id, |struct_info|{
                    struct_info.add_fields(fields.clone().into_iter().map(|(name,ty)|{
                        (name.content,ty)
                    }));
                });

                Ok(TypedStmtNode::Struct { name:name.clone(), 
                    generic_params: generic_params.map_or_else(Vec::new,|params| params.into_iter().map(|(name,_)| name).collect()),
                    fields: fields.into_iter().map(|(name,ty)| (name.content,ty)).collect() })
            }
        }
    }
    fn check_stmts(&mut self,stmts:&[StmtNode])->Result<Vec<TypedStmtNode>,TypeCheckFailed>{
        let mut typed_stmts = Vec::new();
        let mut had_error  = false;   
        for stmt in stmts{
            if let Ok(stmt) = self.check_stmt(stmt){
                typed_stmts.push(stmt);
            }
            else{
                had_error = true;
            }
        }

        if !had_error { Ok(typed_stmts)} else {Err(TypeCheckFailed)}

    }
    pub fn check(mut self,stmts:Vec<StmtNode>)->Result<(Structs,Vec<TypedStmtNode>),TypeCheckFailed>{
        self.check_stmts(&stmts).map (|stmts| (self.structs,stmts))
    }
}