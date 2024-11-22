use std::{collections::HashSet, rc::Rc};

use indexmap::{IndexMap, IndexSet};

use crate::frontend::{parsing::ast::{ExprNode, ExprNodeKind, LiteralKind, ParsedAssignmentTarget, ParsedAssignmentTargetKind, ParsedBinaryOp, ParsedFunction, ParsedGenericArgs, ParsedGenericParam, ParsedGenericParams, ParsedLogicalOp, ParsedPath, ParsedPatternNode, ParsedPatternNodeKind, ParsedType, ParsedUnaryOp, PatternMatchArmNode, StmtNode, Symbol}, tokenizing::SourceLocation, typechecking::typed_ast::{TypedEnumVariant, TypedPatternMatchArm}};

use super::{generics:: substitute, names::{ Environment, ValueKind}, patterns::PatternChecker, typed_ast::{BinaryOp, InitKind, LogicalOp, NumberKind, PatternNode, PatternNodeKind, TypedAssignmentTarget, TypedAssignmentTargetKind, TypedExprNode, TypedExprNodeKind, TypedFunction, TypedFunctionSignature, TypedMethod, TypedStmtNode, UnaryOp}, types::{EnumVariant, FunctionId, GenericArgs, Type, TypeContext}};
#[derive(Clone)]
struct EnclosingFunction{
    return_type : Type
}
pub struct TypeCheckFailed;
#[derive(Default)]
pub struct TypeChecker{
    environment : Environment,
    enclosing_functions : Vec<EnclosingFunction>,
    generic_param_names : Vec<String>,
    self_type : Option<Type>,
    type_context : TypeContext,
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
    fn declare_new_function(&mut self)->FunctionId{
        let id = self.next_function_id;
        self.next_function_id = self.next_function_id.next();
        id
    }
    fn error(&self,message:String,line:u32){
        eprintln!("Error on line {}: {}",line,message);
    }
    fn type_mismatch_error(&self,line:u32,expected:&Type,got:&Type){
        self.error(format!("Expected \"{}\" got \"{}\".",expected,got),line);
    }
    fn add_variables_in_pattern(&mut self,pattern:&PatternNode,ty:&Type){
        let mut variables = Vec::new();
        PatternChecker::collect_variables_in_pattern(pattern,ty, &mut variables,&self.type_context);
        self.environment.add_variables(variables.into_iter().map(|(name_symbol,ty)| (name_symbol.content,ty)));
        
    }
    pub fn get_pattern(&mut self,pattern:&ParsedPatternNode) -> Result<PatternNode,TypeCheckFailed>{
        let kind = match &pattern.kind{
            ParsedPatternNodeKind::Name(name) => {
                PatternNodeKind::Name(name.clone())
            },
            ParsedPatternNodeKind::Is(name, right_pattern) => {
                let right_pattern = self.get_pattern(right_pattern)?;
                PatternNodeKind::Is(name.clone(),Box::new(right_pattern))
            },
            ParsedPatternNodeKind::Wildcard => {
                PatternNodeKind::Wildcard
            },
            ParsedPatternNodeKind::Tuple(patterns) => {
                let patterns = patterns.iter().map(|pattern| self.get_pattern(pattern)).collect::<Result<_,_>>()?;
                PatternNodeKind::Tuple(patterns)
            },
            ParsedPatternNodeKind::Literal(literal) => {
                match literal{
                    LiteralKind::Int(int) => {
                        PatternNodeKind::Int(*int)
                    },
                    LiteralKind::Float(float) => {
                        PatternNodeKind::Float(*float)
                    },
                    LiteralKind::Bool(bool) => {
                        PatternNodeKind::Bool(*bool)
                    },
                    LiteralKind::String(string) => {
                        PatternNodeKind::String(string.clone())
                    }
                }
            },
            ParsedPatternNodeKind::Struct { path, fields } => {
                let ty = self.check_type(&ParsedType::Path(path.clone()))?;

                
                let field_names_and_types = match &ty{
                    Type::Struct {  id, .. } => {
                        self.type_context.structs.get_struct_info(id).unwrap().fields.clone()
                    },
                    Type::EnumVariant { id, variant_index,.. } => {
                        self.type_context.enums.get_enum(*id).variants[*variant_index].fields.clone()
                    }
                    _ => {
                        self.error(format!("Can't use struct pattern with \"{}\" type.",ty), pattern.location.start_line);
                        return Err(TypeCheckFailed);
                    }
                };
                let mut seen_fields = HashSet::new();
                let fields = fields.iter().map(|(name,pattern)|{
                    let Some(expected_type) = ty.get_field(&name.content, &self.type_context) else {
                        self.error(format!("\"{}\" has no field '{}'.",ty,name.content), name.location.start_line);
                        return Err(TypeCheckFailed);
                    };
                    if !seen_fields.insert(&name.content){
                        self.error(format!("Repeated field '{}' for pattern of type \"{}\".",name.content,ty), name.location.start_line);
                        return Err(TypeCheckFailed);
                    }
                    let pattern = self.get_pattern(pattern)?;
                    if PatternChecker::check_pattern_type(&pattern, &expected_type,&self.type_context).is_err(){
                        return Err(TypeCheckFailed)
                    }

                    Ok((name.content.clone(),pattern))
                }).collect::<Result<Vec<_>,_>>()?;
                if seen_fields.len() != field_names_and_types.len(){
                    let field_names = field_names_and_types.iter().map(|(name,_)| name.clone()).collect::<Vec<_>>();
                    self.missing_fields_error( |missing_field_count|
                        if  missing_field_count == 1 {
                            "Missing field pattern ".to_string()
                            } else {
                            "Missing field patterns ".to_string()
                        }, 
                        pattern.location, 
                        field_names.iter(), 
                        seen_fields, 
                        &ty
                    );
                    return Err(TypeCheckFailed);
                }
                PatternNodeKind::Struct { ty, fields  }
            },
            ParsedPatternNodeKind::Array(before, ignore, after) => {
                let before = before.iter().map(|pattern| self.get_pattern(pattern)).collect::<Result<Vec<_>,_>>()?;
                let ignore = ignore.as_ref().map(|ignore|self.get_pattern(ignore)).map_or(Ok(None), |result| result.map(|value| Some(Box::new(value))))?;
                let after = after.iter().map(|pattern| self.get_pattern(pattern)).collect::<Result<Vec<_>,_>>()?;
                PatternNodeKind::Array(before, ignore, after)
            }
        };
        Ok(PatternNode { location:pattern.location,kind })
    }
    fn value_scope_error(&mut self,name:&str,line:u32){
        self.error(format!("Cannot find value '{}' in scope.",name), line);
    }
    fn check_type_match(&mut self,ty:&Type,expected_type:&Type,line:u32)->Result<(),TypeCheckFailed>{
        if ty != expected_type &&  ty != &Type::Never && !ty.is_variant_of(expected_type) {
            self.type_mismatch_error(line, expected_type, ty);
            return Err(TypeCheckFailed);
        }
        Ok(())
    }
    fn check_signature(&mut self,function:&ParsedFunction)->Result<TypedFunctionSignature,TypeCheckFailed>{
        let params = match function.params.iter().map(|param|{
            let pattern = self.get_pattern(&param.pattern)?;
            let ty = self.check_type(&param.ty)?;
            if let Err(refutable_pattern) = PatternChecker::check_irrefutable(&pattern){
                self.error("Can't use non-irrefutable pattern in function parameter.".to_string(), refutable_pattern.location.start_line);
                return Err(TypeCheckFailed);
            }
            if let Err(pattern_type) = PatternChecker::check_pattern_type(&pattern, &ty,&self.type_context){
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
            PatternChecker::collect_variables_in_pattern(pattern, ty,&mut variables,&self.type_context);
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

    fn missing_fields_error<'a>(&mut self,
        start:impl Fn(usize)->String,
        location : SourceLocation,
        expected_fields : impl Iterator<Item = &'a String>,
        seen_fields : HashSet<&String>,
        struct_type : &Type
    ){

            let missing_fields : Vec<&String> = expected_fields.filter(|name|{
                !seen_fields.contains(name as &String)
            }).collect();
            let missing_field_count = missing_fields.len();
            let mut error_string = start(missing_field_count);
            for (i,field) in missing_fields.into_iter().enumerate(){
                if i>0{
                    if i==missing_field_count-1{
                        error_string.push_str(" and ");
                    }
                    else{
                        error_string.push_str(", ");
                    }
                }
                error_string.push_str(&format!("'{}'",field));
            }
            error_string.push_str(&format!(" of struct \"{}\".",struct_type));
            self.error(error_string, location.start_line);
        
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
                    lhs.ty.get_field(&field.content, &self.type_context) 
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
                let pattern = self.get_pattern(&arm.pattern)?;
                let pattern_type = match PatternChecker::check_pattern_type(&pattern,&matchee.ty,&self.type_context){
                    Ok(ty) => ty,
                    Err(pattern_type) => {
                        self.type_mismatch_error(pattern.location.start_line, &matchee.ty, &pattern_type);
                        return Err(TypeCheckFailed);
                    }
                };
                
                let old_env = self.begin_scope();
                let mut variables = Vec::new();
                PatternChecker::collect_variables_in_pattern(&pattern,&pattern_type, &mut variables,&self.type_context);
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
            
            let patterns = &arms.iter().map(|TypedPatternMatchArm{pattern,..}| pattern).collect::<Box<_>>();
            if !PatternChecker.is_exhaustive(patterns,&matchee.ty,&self.type_context){
                self.error("Non exhaustive pattern match.".to_string(),location.start_line);
                return Err(TypeCheckFailed);
            }
            Ok(TypedExprNode{
                location,
                ty : expected_type.unwrap_or(Type::Unit),
                kind : TypedExprNodeKind::Match { matchee:Box::new(matchee), arms }
            })
    }

    fn infer_variable_expr_type(&mut self,location : SourceLocation,name:&String)->Result<(Type,TypedExprNodeKind),TypeCheckFailed>{
        
        match self.get_type_of_value(name){
            Some((ty,kind)) => {
                if let (Some(args),ValueKind::Function) = (ty.get_generic_args(),kind){
                    if args.is_empty(){
                        Ok((ty,TypedExprNodeKind::Get(name.clone())))
                    }
                    else{
                        self.error(format!("Cannot use generic function '{}' without generic arguments.",name), location.start_line);
                        Err(TypeCheckFailed)
                    }
                }
                else if !ty.is_unknown(){
                    Ok((ty.clone(),TypedExprNodeKind::Get(name.clone())))
                }
                else{
                    Err(TypeCheckFailed)
                }
            },
            None =>  {
                self.value_scope_error(name, location.start_line);
                Err(TypeCheckFailed)
            }
        }
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
                self.infer_variable_expr_type(expr.location, name)?
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
            ExprNodeKind::GetPath(path) => {
                let head = &path.head;
                let head_name = path.head.name.content.clone();
                match path.generic_args.as_ref() {
                    Some(args) => {
                        let ParsedGenericArgs{
                            location,
                            types
                        } = args;
                        let ty = if let Some(ty) = self.environment.get_type(&head.name.content){
                            if !ty.is_unknown(){
                                ty.clone()
                            }
                            else{
                                return Err(TypeCheckFailed);
                            }
                        }
                        else if let Some((function,ValueKind::Function)) = self.get_type_of_value(&head_name){
                            function
                        }
                        else {
                            self.error(format!("Cannot find type '{}' in scope.",head_name), expr.location.start_line);
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
                        for (value,ty) in params.iter_mut().zip(args.iter().cloned()){
                            *value = ty;
                        }
                        let ty = substitute(ty, &params);
                        if path.segments.is_empty(){
                            (substitute(ty,&params),TypedExprNodeKind::GetGeneric{name:head.name.content.clone(), args })
                        }
                        else{
                            self.get_expr_path(path, ty)?
                        }
                    },
                    None => {
                        if let Some(ty) = self.environment.get_type(&head.name.content){
                            let ty = if !ty.is_unknown(){
                                ty.clone()
                            }
                            else{
                                return Err(TypeCheckFailed);
                            };
                            if !ty.is_closed(){
                                self.error(format!("Cannot use generic type \"{}\".",ty), path.location.start_line);
                                return Err(TypeCheckFailed);
                            }
                            self.get_expr_path(path,ty)?
                        }
                        else{
                            let (mut ty,mut expr) = self.infer_variable_expr_type(head.location, &head_name)?;
                            for segment in &path.segments{
                                let property = segment.name.clone();
                                let Some(property_type) = ty.get_field(&property.content,&self.type_context) else{
                                    self.error(format!("\"{}\" has no field or method '{}'.",ty,property.content),property.location.start_line);
                                    return Err(TypeCheckFailed);
                                };
                                let location = property.location;
                                (ty,expr) = (property_type,TypedExprNodeKind::Field(Box::new(TypedExprNode { location, ty, kind:expr }), property.clone()));
                            }
                            (ty,expr)
                        }
                    }
                }
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
                    ParsedBinaryOp::Greater => BinaryOp::Greater,
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
            ExprNodeKind::MethodCall { receiver, method, args } => {
                let receiver = self.infer_expr_type(receiver)?;
                
                let (arg_types,return_type,field_ty) = 
                if let Some(method_info) = self.environment.get_method(&receiver.ty, &method.content){
                    let mut params = method_info.param_types.clone();
                    if method_info.has_self_param{
                        params.remove(0);
                    }
                    else{
                        self.error(format!("Cannot call method '{}' with no self parameter on type \"{}\".",method_info.name,receiver.ty), method.location.start_line);
                        return Err(TypeCheckFailed);
                    }
                    (params,method_info.return_type.clone(),None)
                }
                else if let Some(field) = receiver.ty.get_field(&method.content, &self.type_context){

                    let (arg_types,return_type) = match &field{
                        Type::Function { params:arg_types, return_type ,..}=> {
                            (arg_types,return_type)
                        },
                        _ => {
                            self.error(format!("Cannot call \"{}\".",field),expr.location.start_line);
                            return Err(TypeCheckFailed);
                        }
                    };
                    (arg_types.clone(),*return_type.clone(),Some(field))
                }
                else {
                    self.error(format!("\"{}\" has no method or field '{}'.",receiver.ty,method.content), method.location.start_line);
                    return Err(TypeCheckFailed);
                };

                if arg_types.len() != args.len(){
                    self.error(format!("Expected \'{}\' args got \'{}\'.",arg_types.len(),args.len()),expr.location.start_line);
                    return Err(TypeCheckFailed);
                }
                let args = arg_types.iter().zip(args.iter()).map(|(ty,arg)| {
                    self.check_expr_type(arg, ty)
                }).collect::<Result<Vec<_>,_>>()?;

                let kind = 
                    if let Some(field_ty) = field_ty {
                     TypedExprNodeKind::Call { 
                        callee:Box::new(TypedExprNode{
                            location:method.location,kind:TypedExprNodeKind::Field(Box::new(receiver), 
                            method.clone()),ty:field_ty
                        }), args } 
                    } 
                    else {
                         TypedExprNodeKind::MethodCall { lhs:Box::new(receiver),method:method.clone(), args }
                    };
                (return_type,kind)
                
            }
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
                let Some(property_type) = lhs.ty.get_field(&property.content,&self.type_context) else{
                    self.error(format!("\"{}\" has no field or method '{}'.",lhs.ty,property.content),property.location.start_line);
                    return Err(TypeCheckFailed);
                };
                (property_type,TypedExprNodeKind::Field(Box::new(lhs), property.clone()))
            },
            ExprNodeKind::StructInit { path , fields } => {
                let mut ty = self.check_type(&ParsedType::Path(path.clone()))?;
                

                let (kind,name,field_names_and_types,error_type) = match ty.clone(){
                    Type::Struct { generic_args, id, name } => {
                        
                        let struct_info = self.type_context.structs.get_struct_info(&id).expect("Can only use valid struct ids");
                        let field_names_and_types = struct_info.fields.iter().cloned().map(|(name,ty)| (name,substitute(ty, &generic_args))).collect::<IndexMap<_,_>>();
                        
                        (InitKind::Struct(id),name,field_names_and_types,ty.clone())
                    },
                    Type::EnumVariant { id, name, variant_index ,generic_args} => {
                        let variant = &self.type_context.enums.get_enum(id).variants[variant_index];
                        let fields = variant.fields.clone();
                        let display_type = ty.clone();
                        ty = Type::Enum { id, name: self.type_context.enums.get_enum(id).name.clone() ,generic_args:generic_args.clone()};
                        (InitKind::Variant(id, variant_index),name,fields.into_iter().map(|(name,ty)|(name,substitute(ty, &generic_args))).collect(),display_type)
                    }
                    _ => {
                        self.error(format!("Expected struct or variant got \"{}\".",ty), path.location.start_line);
                        return Err(TypeCheckFailed);
                    }
                };
                
                let mut seen_fields = HashSet::new();
                let fields = fields.iter().map(|(field_name,field_expr)|{

                    let Some(ty) = field_names_and_types.get(&field_name.content) else {
                        self.error(format!("\"{}\", has no field '{}'.",name,field_name.content), field_name.location.start_line);
                        return Err(TypeCheckFailed);
                    };
                    if !seen_fields.insert(&field_name.content){
                        self.error(format!("Re-initialized field '{}'.",field_name.content), field_name.location.start_line);
                        return Err(TypeCheckFailed);
                    }
                    let field_expr = self.check_expr_type(field_expr, ty )?;
                    Ok((field_name.content.clone(),field_expr))
                }).collect::<Result<Vec<_>,_>>()?;
                if field_names_and_types.len() != seen_fields.len(){
                    self.missing_fields_error( |missing_field_count|
                        if  missing_field_count == 1 {
                       "Did not initialize field ".to_string()
                     } else {
                        "Did not initialize fields ".to_string()
                    }, expr.location, field_names_and_types.keys(), seen_fields, &error_type);
                    return Err(TypeCheckFailed);
                }
                (ty,TypedExprNodeKind::StructInit { kind,fields })
            }

        };
        Ok(TypedExprNode { location: expr.location, ty, kind })
    }
    fn get_expr_path(&mut self,path:&ParsedPath,ty:Type)->Result<(Type, TypedExprNodeKind), TypeCheckFailed>{ 

        enum Item{
            Type(Type),
            Method(Type,TypedExprNodeKind),
            Variant(Type,TypedExprNodeKind),
        }
        let mut current = Item::Type(ty.clone());
        let mut last_type = ty;
        for segment in &path.segments{
            let segment_name = segment.name.content.clone();
            let next = match current{
                Item::Type(ty) => {
                    let variant = if let Type::Enum {  id,generic_args,.. } = ty.clone(){
                        self.type_context.enums.get_enum(id).variants.iter().find(|variant| variant.name == segment_name ).map(|variant|{
                            last_type = Type::EnumVariant { generic_args, id, name: variant.name.clone(), variant_index: variant.discrim };
                            Item::Variant(ty.clone(),TypedExprNodeKind::StructInit { kind: InitKind::Variant(id, variant.discrim), fields:Vec::new() })
                        })
                    }
                    else{
                        None
                    };
                    let method = if variant.is_none(){
                        self.environment.get_method(&ty, &segment_name).map(|method|{
                            let method_type = Type::Function { generic_args: method.generic_types.clone(), params: method.param_types.clone(), return_type:Box::new(method.return_type.clone()) };
                            Item::Method(method_type,TypedExprNodeKind::GetMethod { ty:ty.clone(), method:segment.name.clone() })
                        })
                    }
                    else{
                        None
                    };
                    variant.or(method)
                },
                _ => None
            };
            let Some(next) = next else {
                self.error(format!("\"{}\" has no variant or method '{}'.",last_type,segment_name), segment.location.start_line);
                return Err(TypeCheckFailed);
            };
            current = next;

        }

        match current{
            Item::Method(ty, expr) | Item::Variant(ty, expr) => {
                Ok((ty,expr))
            },
            Item::Type(ty) => {
                self.error(format!("Expected an expression got type \"{}\".",ty),path.location.start_line);
                Err(TypeCheckFailed)
            }
        }
    }
    fn check_type(&mut self,ty:&ParsedType)->Result<Type,TypeCheckFailed>{
        fn get_substituted(this:&mut TypeChecker,ty:Type,args:&ParsedGenericArgs)->Result<Type,TypeCheckFailed>{

            let generic_args = args.types.iter().map(|ty| this.check_type(ty)).collect::<Result<Vec<_>,_>>()?;
            let expected_args = match &ty { 
                Type::Struct { generic_args, .. }|Type::Enum { generic_args, .. } if generic_args.iter().all(|ty| !ty.is_closed()) => {
                    generic_args
                },
                ty => {
                    this.error(format!("Cannot apply generic args to non-generic type \"{}\".",ty), args.location.start_line);
                    return Err(TypeCheckFailed);
                }
            };
            if generic_args.len() != expected_args.len(){
                this.error(format!("Expected '{}' generic args, but got '{}'.",expected_args.len(),generic_args.len()),args.location.start_line);
                return Err(TypeCheckFailed);
            }
            let subbed_generic_args = generic_args;
            Ok(substitute(ty, &subbed_generic_args))
        }
        fn get_type_at_path(this:&mut TypeChecker,path:&ParsedPath)->Result<Type,TypeCheckFailed>{
            
            let ty = get_named_type(this, &path.head.name)?;
            if path.head.name.content == "Self" && path.generic_args.is_some(){
                this.error("Cannot use \"Self\" type with generic args.".to_string(), path.head.location.start_line);
                return Err(TypeCheckFailed);
            }
            let ty = match path.generic_args.as_ref(){
                Some(args) if path.segments.is_empty() => {
                    get_substituted(this, ty, args)?
                },
                None if path.segments.is_empty() => {
                    if !matches!(&ty,Type::Param { ..}) && !ty.is_closed(){
                        this.error(format!("Cannot use generic type \"{}\" without type args.",ty), path.head.location.start_line);
                        return Err(TypeCheckFailed);
                    }
                    ty
                },
                Some(generic_args) => {
                    let mut ty = get_substituted(this, ty, generic_args)?;
                    for segment in &path.segments{
                        let segment_name = segment.name.content.clone();
                        let mut result_ty = None;
                        if let Type::Enum { id, generic_args,.. } = &ty{
                            if let Some(variant) = this.type_context.enums.get_enum(*id).variants.iter().find(|variant| variant.name == segment_name){
                                result_ty = Some(Type::EnumVariant { id:*id, name: variant.name.clone(), variant_index: variant.discrim ,generic_args:generic_args.clone()})
                            }
                        }
                        ty = if let Some(result_ty) = result_ty{
                            result_ty
                        }
                        else{
                            this.error(format!("\"{}\" does not have variant '{}'.",ty,segment.name.content), segment.location.start_line);
                            return Err(TypeCheckFailed);
                        }

                    }
                    ty
                },
                None => {
                    let mut ty = ty;
                    for segment in &path.segments{
                        let segment_name = segment.name.content.clone();
                        let mut result_ty = None;
                        if let Type::Enum { id, generic_args,.. } = &ty{
                            if let Some(variant) = this.type_context.enums.get_enum(*id).variants.iter().find(|variant| variant.name == segment_name){
                                result_ty = Some(Type::EnumVariant { id:*id, name: variant.name.clone(), variant_index: variant.discrim ,generic_args:generic_args.clone()})
                            }
                        }
                        ty = if let Some(result_ty) = result_ty{
                            result_ty
                        }
                        else{
                            this.error(format!("\"{}\" does not have variant '{}'.",ty,segment.name.content), segment.location.start_line);
                            return Err(TypeCheckFailed);
                        }

                    }
                    ty
                }
            };
            Ok(ty)
        }
        fn get_named_type(this:&mut TypeChecker,name:&Symbol)->Result<Type,TypeCheckFailed>{

            Ok(match &name.content as &str{
                "int" => Type::Int,
                "float" => Type::Float,
                "string" => Type::String,
                "bool" => Type::Bool,
                "never" => Type::Never,
                "Self" => if let Some(ty) = this.self_type.clone() {
                    ty
                }
                else{
                    this.error("Cannot use \"Self\" in this context.".to_string(),name.location.start_line);
                    return Err(TypeCheckFailed);
                },
                type_name => {
                    if let Some(index) = this.generic_param_names.iter().rev().position(|name| name == type_name){
                        Type::new_param_type(type_name.to_string(), index)
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
            ParsedType::Path(path) => {
                get_type_at_path(self,path)?
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
            self.generic_param_names.extend(generic_param_names.iter().cloned());
            let generic_params = generic_param_names.into_iter().enumerate().map(|(i,name)|{
                (name,generic_param_count+i)
            }).collect::<Vec<(String,_)>>();
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

    fn check_type_not_in_local_scope(&mut self,name:&str,location : SourceLocation)->Result<(),TypeCheckFailed>{
        
        if self.environment.is_type_in_local_scope(name){
            self.error(format!("A type with name '{}' is already defined.",name),location.start_line);
            return Err(TypeCheckFailed);
        }

        Ok(())
    }
    fn check_generic_params_def(&mut self,generic_params : Option<&ParsedGenericParams>)->Result<Option<Vec<(String,usize)>>,TypeCheckFailed>{
        let Ok(checked_generic_params) = self.check_generic_params(generic_params) else {
            self.generic_param_names.truncate(self.generic_param_names.len() - generic_params.as_slice().len());
            return Err(TypeCheckFailed);
        };
        Ok(checked_generic_params)

    }
    fn convert_to_generic_params(&self,generic_params : &Option<Vec<(String,usize)>>)->Option<GenericArgs>{
        if let Some(generic_params) = generic_params.clone(){
            let generic_params : Vec<Type> = generic_params.into_iter().map(|(name,index)|{
               Type::Param { name, index }
            }).collect();
            Some(generic_params)
        }
        else{   
            None
        }
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

                let pattern = self.get_pattern(pattern)?;

                let ty = if let Some(ty) = ty.as_ref(){ self.check_type(ty).map(Some)} else {Ok(None)};
                let expr = self.check_or_infer_expr_type(expr, ty.as_ref().ok().and_then(|ty| ty.as_ref()));

                let (ty,expr) = match (ty,expr){
                    (Ok(ty),Ok(expr)) => (ty,expr),
                    (Ok(Some(ty)),Err(_)) => {
                        self.add_variables_in_pattern(&pattern, &ty);
                        return Err(TypeCheckFailed);
                    },
                    (Err(_),Ok(expr)) => {
                        let ty = match PatternChecker::check_pattern_type(&pattern,&expr.ty,&self.type_context){
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
                        let (Ok(ty)|Err(ty)) = PatternChecker::check_pattern_type(&pattern,&Type::Unknown,&self.type_context);
                        self.add_variables_in_pattern(&pattern, &ty);
                        return Err(TypeCheckFailed);
                    }
                };

                let ty = ty.unwrap_or_else(|| expr.ty.clone());
                if !PatternChecker.is_exhaustive(&[&pattern],&ty,&self.type_context){
                    self.error("Can't use non-irrefutable pattern in 'let' statement.".to_string(), pattern.location.start_line);
                    self.add_variables_in_pattern(&pattern, &ty);
                    return Err(TypeCheckFailed);
                }
                if let Err(pattern_type) =  PatternChecker::check_pattern_type(&pattern,&expr.ty,&self.type_context){
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

                let id = self.declare_new_function();
                let generic_param_count = self.generic_param_names.len();
                let Ok(generic_params) = self.check_generic_params_def(generic_params.as_ref()) else{
                    self.environment.add_function(name.content.clone(), Vec::new(),Type::Unknown,id);
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
                if let Some(generic_params) = self.convert_to_generic_params(&generic_params){
                    self.environment.add_generic_function(function_name, params, return_type, id, generic_params.into_iter());
                }
                else{
                    self.environment.add_function(function_name,params, return_type, id);
                }
                
                let function =  self.check_function(function, signature);
                self.generic_param_names.truncate(generic_param_count);
                let function = function?;
                Ok(if let Some(generic_params) = generic_params {
                        TypedStmtNode::GenericFunction { name:name.clone(), function,generic_params:generic_params.into_iter().map(|(_,index)| index).collect() } 
                    } 
                    else{
                        TypedStmtNode::Fun { name: name.clone(), function }
                    })
            },
            StmtNode::Struct { name, generic_params, fields } => {
                let generic_param_count = self.generic_param_names.len();
                self.check_type_not_in_local_scope(&name.content,name.location)?;
                let struct_name = name.content.clone();
                let Ok(generic_params) = self.check_generic_params_def(generic_params.as_ref()) else {
                    self.environment.add_type(struct_name,Type::Unknown);
                    return Err(TypeCheckFailed);
                };
                let id = self.type_context.structs.define_struct (vec![].into_iter() );
                let generic_params = self.convert_to_generic_params(&generic_params);
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
                self.type_context.structs.update_struct_info(&id, |struct_info|{
                    struct_info.add_fields(fields.clone().into_iter().map(|(name,ty)|{
                        (name.content,ty)
                    }));
                });

                Ok(TypedStmtNode::Struct { name:name.clone(), 
                    generic_params: generic_params.map_or_else(Vec::new,|params| params.into_iter().map(|param|{
                        let Type::Param {  index ,..} = param else {unreachable!()};
                        index
                    }).collect()),
                    fields: fields.into_iter().map(|(name,ty)| (name.content,ty)).collect() })
            },
            StmtNode::Enum {name,generic_params,variants} => {
                let generic_param_count = self.generic_param_names.len();
                self.check_type_not_in_local_scope(&name.content, name.location)?;
                let enum_name = name.content.clone();
                let Ok(generic_names) = self.check_generic_params_def(generic_params.as_ref()) else {
                    self.environment.add_type(enum_name.clone(), Type::Unknown);
                    return Err(TypeCheckFailed);
                };
                let generic_params = self.convert_to_generic_params(&generic_names);
                let id = self.type_context.enums.define_enum(enum_name.clone(),Vec::new());
                self.environment.add_type(enum_name.clone(), Type::Enum { id, name: enum_name.clone(),generic_args:generic_params.unwrap_or_default()});                
                let variants = {
                    let mut seen_variant_names = HashSet::new();
                    let Ok(variants) = variants.iter().map(|variant|{
                        if !seen_variant_names.insert(&variant.name.content){
                            self.error(format!("Redefined variant '{}'.",variant.name.content),variant.name.location.start_line);
                            return Err(TypeCheckFailed);
                        }
                        let mut seen_fields = HashSet::new();
                        let fields = variant.fields.iter().map(|(field_name,field_type)|{
                            let ty = self.check_type(field_type)?;
                            if !seen_fields.insert(&field_name.content){
                                self.error(format!("Redefined field '{}'.",field_name.content),field_name.location.start_line);
                                return Err(TypeCheckFailed);
                            }
                            Ok((field_name.clone(),ty))
                        }).collect::<Result<Vec<_>,_>>()?;
                        Ok(TypedEnumVariant{
                            name : variant.name.clone(),
                            fields
                        })
                    }).collect::<Result<Vec<_>,_>>() else {
                        self.generic_param_names.truncate(generic_param_count);
                        self.environment.add_type(enum_name.clone(), Type::Unknown);
                        return Err(TypeCheckFailed);
                    };
                    variants
                };
                self.type_context.enums.update_enum(id, |enum_|{
                    enum_.variants = variants.iter().enumerate().map(|(i,variant)|{
                        EnumVariant{
                            discrim:i,
                            name : variant.name.content.clone(),
                            fields:variant.fields.iter().map(|(field_name,ty)|{(field_name.content.clone(),ty.clone())}).collect()
                        }
                    }).collect();
                });
                self.generic_param_names.truncate(generic_param_count);
                Ok(TypedStmtNode::Enum { name:name.clone(), variants })
            },
            StmtNode::Impl { ty, methods } => {
                let self_type = self.check_type(ty)?;
                let old_type = self.self_type.take();
                self.self_type = Some(self_type.clone());
                let Ok(methods) = methods.iter().map(|method|{
                    let signature = self.check_signature(&method.function)?;
                    if !self.environment.add_method(self_type.clone(),method.name.content.clone(),method.has_receiver ,signature.params.clone().into_iter().map(|(_,ty)| ty).collect(), signature.return_type.clone()){
                        self.error(format!("There is already a method with name '{}' for type \"{}\".",method.name.content,self_type), method.name.location.start_line);
                        return Err(TypeCheckFailed);
                    }
                    let method_function = self.check_function(&method.function, signature.clone())?;
                    Ok(TypedMethod{name:method.name.clone(),function:method_function})
                }).collect::<Result<Vec<_>,TypeCheckFailed>>() else{
                    self.self_type = old_type;
                    return Err(TypeCheckFailed);
                };
                
                self.self_type = old_type;
                Ok(TypedStmtNode::Impl { ty: self_type, methods})
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
    pub fn check(mut self,stmts:Vec<StmtNode>)->Result<(TypeContext,Vec<TypedStmtNode>),TypeCheckFailed>{
        let option_type = {
            let generic_parameter_type = Type::Param { name: "T".to_string(), index: 0 };
            let option_id = self.type_context.enums.define_enum("Option".to_string(),vec![
                EnumVariant{
                    discrim:0,
                    name : "Some".to_string(),
                    fields : vec![
                        ("val".to_string(),generic_parameter_type.clone())
                    ]
                },
                EnumVariant{
                    discrim:1,
                    name: "None".to_string(),
                    fields: Vec::new()
                }
            ]);
            let option_type = Type::Enum { generic_args: vec![generic_parameter_type], id: option_id, name: "Option".to_string() };
            self.environment.add_type("Option".to_string(),option_type.clone() );
            option_type
        };
        let id = self.declare_new_function();
        self.environment.add_function("input".to_string(), Vec::new(), Type::String, id);
        let id = self.declare_new_function();
        self.environment.add_function("panic".to_string(), vec![Type::String], Type::Never, id);
        {
            let id = self.declare_new_function();
            let param_type = Type::Param { name:"T".to_string(), index:0 };
            self.environment.add_generic_function("push".to_string(), vec![Type::Array(Box::new(param_type.clone())),param_type.clone()], Type::Unit, id,
                [param_type].into_iter());
        }
        {
            let id = self.declare_new_function();
            let param_type = Type::Param { name:"T".to_string(), index:0 };
            self.environment.add_generic_function("pop".to_string(), vec![Type::Array(Box::new(param_type.clone()))], param_type.clone(), id,
                [param_type].into_iter());
        }
        {
            let id = self.declare_new_function();
            self.environment.add_function("parse_int".to_string(), vec![Type::String], 
                substitute(option_type.clone(),&[Type::Int]), id);
        }
        self.check_stmts(&stmts).map (|stmts| (self.type_context,stmts))
    }
}