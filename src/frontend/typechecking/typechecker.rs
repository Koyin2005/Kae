use std::collections::HashSet;

use indexmap::{IndexMap, IndexSet};

use crate::frontend::{name_resolution::resolved_ast::ResolvedStmt, parsing::ast::{ExprNode, ExprNodeKind, LiteralKind, ParsedAssignmentTargetKind, ParsedBinaryOp, ParsedFunction, ParsedGenericArgs, ParsedGenericParam, ParsedGenericParams, ParsedLogicalOp, ParsedPath, ParsedPatternNode, ParsedPatternNodeKind, ParsedType, ParsedUnaryOp, PathSegment, StmtNode, Symbol}, tokenizing::SourceLocation, typechecking::typed_ast::{TypedEnumVariant, TypedPatternMatchArm}};

use super::{generics::{infer_types,  substitute}, names::{  DefId, Environment, Function,  Identifiers, Method,}, patterns, typed_ast::{BinaryOp, GenericName, InitKind, LogicalOp, NumberKind, PatternNode, PatternNodeKind, ResolvedSymbol, TypedAssignmentTarget, TypedAssignmentTargetKind, TypedExprNode, TypedExprNodeKind, TypedFunction, TypedFunctionSignature, TypedMethod, TypedStmtNode, UnaryOp}, types::{EnumId, EnumVariant, GenericArgs, GenericParamType, Type, TypeContext}};


enum Item{
    Variant(Type,EnumId,usize),
    Method(Type,Symbol,Option<Vec<Type>>),
    Type(Type)
}
#[derive(Clone)]
struct EnclosingFunction{
    return_type : Type
}
pub struct TypeCheckFailed;
#[derive(Default)]
pub struct TypeChecker{
    environment : Environment,
    enclosing_functions : Vec<EnclosingFunction>,
    self_type : Option<Type>,
    type_context : TypeContext,
    identifiers : Identifiers
}
impl TypeChecker{
    fn begin_scope(&mut self){
        self.environment.begin_scope();
    }
    fn end_scope(&mut self){
        self.environment.end_scope();
    }
    fn error(&self,message:String,line:u32){
        eprintln!("Error on line {}: {}",line,message);
    }
    fn type_mismatch_error(&self,line:u32,expected:&Type,got:&Type){
        self.error(format!("Expected \"{}\" got \"{}\".",expected,got),line);
    }
    pub fn define_bindings_in_pattern(&mut self,pattern:&PatternNode){
        match &pattern.kind{
            &PatternNodeKind::Name(id) => {
                let name = self.identifiers.get_variable_name(id).to_string();
                self.environment.add_variable(name, pattern.ty.clone(), false, id);
            },
            PatternNodeKind::Is(symbol, pattern) => {
                let name = self.identifiers.get_variable_name(symbol.id).to_string();
                self.define_bindings_in_pattern(pattern);
                self.environment.add_variable(name,pattern.ty.clone(), false, symbol.id);
            },
            PatternNodeKind::Bool(_)|PatternNodeKind::Float(_)|PatternNodeKind::Int(_)|PatternNodeKind::String(_)|PatternNodeKind::Wildcard => (),
            PatternNodeKind::Tuple(elements) =>{
                for element in elements{
                    self.define_bindings_in_pattern(element);
                }
            },
            PatternNodeKind::Array(before, mid, after) => {
                for element in before{
                    self.define_bindings_in_pattern(element);
                }
                if let Some(mid) =  mid{
                    self.define_bindings_in_pattern(mid);
                }
                for element in after{
                    self.define_bindings_in_pattern(element);
                }
            },
            PatternNodeKind::Struct { fields } => {
                for (_,pattern) in fields{
                    self.define_bindings_in_pattern(pattern);
                }
            },
        }
        
    }
    
    pub fn resolve_pattern(&mut self,pattern:&ParsedPatternNode,expected_type:Option<Type>) -> Result<PatternNode,TypeCheckFailed>{
        let (kind,ty)= match &pattern.kind{
            ParsedPatternNodeKind::Name(name) => {
                let id = self.identifiers.define_variable(name.clone());
                (PatternNodeKind::Name(id),expected_type.clone().ok_or_else(||{
                    self.error(format!("Cannot infer type of binding '{}'.",name),pattern.location.start_line);
                    TypeCheckFailed
                })?)
            },
            ParsedPatternNodeKind::Is(name, right_pattern) => {
                let id = self.identifiers.define_variable(name.content.clone());
                let right_pattern = self.resolve_pattern(right_pattern,expected_type.clone())?;
                let ty = right_pattern.ty.clone();
                (PatternNodeKind::Is(ResolvedSymbol{id,location:name.location},Box::new(right_pattern)),ty)
            },
            ParsedPatternNodeKind::Wildcard => {
                (PatternNodeKind::Wildcard,expected_type.clone().ok_or_else(||{
                    self.error("Cannot infer type of '_'.".to_string(),pattern.location.start_line);
                    TypeCheckFailed
                })?)
            },
            ParsedPatternNodeKind::Tuple(patterns) => {
                let elements = if let Some(ty) = expected_type.clone(){
                    let elements = match ty {
                        Type::Tuple(elements) if elements.len() == patterns.len() => elements,
                        _ => {
                            self.type_mismatch_error(pattern.location.start_line,&Type::Tuple(vec![Type::Unknown;patterns.len()]),&ty);
                            return Err(TypeCheckFailed);
                        }
                    };
                    elements.into_iter().map(|element| Some(element)).collect()
                }
                else{
                    vec![None;patterns.len()]
                };
                let patterns : Vec<_> = patterns.iter().zip(elements.clone()).map(|(pattern,ty)| self.resolve_pattern(pattern,ty) ).collect::<Result<_,_>>()?;
                let elements = patterns.iter().map(|pattern| pattern.ty.clone()).collect();
                (PatternNodeKind::Tuple(patterns),Type::Tuple(elements))
            },
            ParsedPatternNodeKind::Literal(literal) => {
                match literal{
                    LiteralKind::Int(int) => {
                        (PatternNodeKind::Int(*int),Type::Int)
                    },
                    LiteralKind::Float(float) => {
                        (PatternNodeKind::Float(*float),Type::Float)
                    },
                    LiteralKind::Bool(bool) => {
                        (PatternNodeKind::Bool(*bool),Type::Bool)
                    },
                    LiteralKind::String(string) => {
                        (PatternNodeKind::String(string.clone()),Type::String)
                    }
                }
            },
            ParsedPatternNodeKind::Struct { path, fields } => {
                let ty = self.check_type(&ParsedType::Path(path.clone()))?;
                let field_names_and_types = match &ty{
                    Type::Struct {  id, .. } => {
                        self.type_context.structs.get_struct_info(todo!("Use correct ids")).unwrap().fields.clone()
                    },
                    Type::EnumVariant { id, variant_index,.. } => {
                        self.type_context.enums.get_enum(todo!("Use correct ids")).variants[*variant_index].fields.clone()
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
                    let pattern = self.resolve_pattern(pattern,Some(expected_type.clone()))?;
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
                (PatternNodeKind::Struct { fields  },ty)
            },
            ParsedPatternNodeKind::Array(before, ignore, after) => {
                let mut expected_type = if let Some(ty) = expected_type.clone() {
                    let Type::Array(elements) = ty else {
                        self.type_mismatch_error(pattern.location.start_line,&Type::Array(Box::new(Type::Unknown)),&ty);
                        return Err(TypeCheckFailed);
                    };
                    Some(*elements)
                } else {
                    None
                };

                let before = before.iter().map(|pattern|{
                    let pattern = self.resolve_pattern(pattern,expected_type.clone())?;
                    if expected_type.is_none(){
                        expected_type = Some(pattern.ty.clone());
                    }
                    Ok(pattern)
                }).collect::<Result<Vec<_>,_>>()?;
                let ignore = ignore.as_ref().map(|pattern|{
                    let pattern = self.resolve_pattern(pattern,expected_type.clone())?;
                    if expected_type.is_none(){
                        expected_type = Some(pattern.ty.clone());
                    }
                    Ok(pattern)
                }).map_or(Ok(None), |result| result.map(|value| Some(Box::new(value))))?;
                let after = after.iter().map(|pattern|{
                    let pattern = self.resolve_pattern(pattern,expected_type.clone())?;
                    if expected_type.is_none(){
                        expected_type = Some(pattern.ty.clone());
                    }
                    Ok(pattern)
                }).collect::<Result<Vec<_>,_>>()?;

                let element_type = if let Some(ty) = expected_type{
                    ty
                }
                else{
                    self.error(format!("Cannot infer type of empty array."),pattern.location.end_line);
                    return Err(TypeCheckFailed);
                };
                (PatternNodeKind::Array(before, ignore, after),Type::Array(Box::new(element_type)))
            }
        };
        if let Some(expected_type) = &expected_type{
            self.check_type_match(&ty, expected_type, pattern.location.start_line)?;
        }
        Ok(PatternNode { location:pattern.location,kind ,ty})
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
            let ty = self.check_type(&param.ty)?;
            let pattern = self.resolve_pattern(&param.pattern,Some(ty.clone()))?;
            if !patterns::is_exhaustive(&[&pattern], &ty, &self.type_context){
                self.error("Can't use non-irrefutable pattern in function parameter.".to_string(), pattern.location.start_line);
                return Err(TypeCheckFailed);
            }
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
        self.begin_scope();
        self.enclosing_functions.push(EnclosingFunction { return_type:  signature.return_type.clone()});
        let body = (||{
            let mut variable_names =  IndexSet::new();
            for (pattern,_) in &signature.params{
                let mut bindings = Vec::new();
                patterns::collect_bindings(pattern,&mut bindings);
                for binding in bindings{
                    if !variable_names.insert(binding.id){
                        self.error(format!("Repeated parameter with name '{}'.",self.identifiers.get_variable_name(binding.id)),binding.location.start_line);
                        return Err(TypeCheckFailed);
                    }
                }
                self.define_bindings_in_pattern(pattern);
            }
            let body = match self.check_expr(&function.body, Some(&signature.return_type)){
                Ok(body) => body,
                Err(_) => {
                    return Err(TypeCheckFailed);
                }
            };
            Ok(body)
        })();
        self.end_scope();
        self.enclosing_functions.pop();
        body.map(|body| TypedFunction{ signature, body:Box::new(body) })
    }

    fn get_type_of_value(&self,name:&str) -> Option<(Type,DefId)>{
        if let Some(variable) = self.environment.get_variable(name){
            Some((variable.ty.clone(),DefId::Variable(variable.id)))
        }
        else if let Some(function) = self.environment.get_function(name){
            let params = function.param_types.clone();
            let return_type = function.return_type.clone();
            let generic_args = function.generic_types.clone();
            let ty = Type::Function{params,return_type:Box::new(return_type),generic_args};
            Some((ty,DefId::Function(function.id)))
        }
        else{
            None
        }
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
    fn check_expr(&mut self,expr:&ExprNode,expected_type : Option<&Type>)->Result<TypedExprNode,TypeCheckFailed>{
        let (ty,kind) = match &expr.kind{
            ExprNodeKind::Literal(literal) => {
                match literal{
                    &LiteralKind::Int(int) => (Type::Int,TypedExprNodeKind::Number(NumberKind::Int(int))),
                    &LiteralKind::Float(float) => (Type::Float,TypedExprNodeKind::Number(NumberKind::Float(float))),
                    &LiteralKind::Bool(bool) => (Type::Bool,TypedExprNodeKind::Bool(bool)),
                    LiteralKind::String(string) => (Type::String,TypedExprNodeKind::String((string as &str).into()))
                }
            },
            ExprNodeKind::Get(name) => {
                match self.get_type_of_value(name){
                    Some((ty,def)) => {
                        (ty,TypedExprNodeKind::Get(def))
                    },
                    None => {
                        self.error(format!("Cannot use undefined value '{}'.",name),expr.location.start_line);
                        return Err(TypeCheckFailed);
                    }
                }
            },
            ExprNodeKind::Grouping(expr) => {
                let TypedExprNode { ty, kind,.. } = self.check_expr(expr, expected_type)?;
                (ty,kind)
            },
            ExprNodeKind::Unary { op, operand } => {
                let op = match op{
                    ParsedUnaryOp::Negate => UnaryOp::Negate
                };
                let operand = self.check_expr(operand, None)?;
                let ty = match (op,&operand.ty){
                    (UnaryOp::Negate,ty) =>  if matches!(ty,Type::Int|Type::Float) { Ok(ty.clone())} else { Err((op,ty))}
                };
                let ty = match ty{
                    Ok(ty) => ty,
                    Err((op,ty)) => {
                        self.error(format!("'{}' does not support operand of type '{}'.",op,ty),expr.location.start_line);
                        return Err(TypeCheckFailed);
                    }
                };
                (ty,TypedExprNodeKind::Unary { op, operand: Box::new(operand) })
            },
            ExprNodeKind::BinaryOp { op, left, right } => {
                let op = match op{
                    ParsedBinaryOp::Add => BinaryOp::Add,
                    ParsedBinaryOp::Subtract => BinaryOp::Subtract,
                    ParsedBinaryOp::Multiply => BinaryOp::Multiply,
                    ParsedBinaryOp::Divide => BinaryOp::Divide,
                    ParsedBinaryOp::Lesser => BinaryOp::Lesser,
                    ParsedBinaryOp::Greater => BinaryOp::Greater,
                    ParsedBinaryOp::LesserEquals => BinaryOp::LesserEquals,
                    ParsedBinaryOp::GreaterEquals => BinaryOp::GreaterEquals,
                    ParsedBinaryOp::Equals => BinaryOp::Equals,
                    ParsedBinaryOp::NotEquals => BinaryOp::NotEquals 
                };
                let left = self.check_expr(left, None)?;
                let right = self.check_expr(right, None)?;
                let ty = match (op,&left.ty,&right.ty) {
                    (BinaryOp::Add | BinaryOp::Subtract | BinaryOp::Multiply | BinaryOp::Divide,left,right)  => {
                        if left == right && matches!(left,Type::Int|Type::Float) {
                            Ok(left.clone())
                        }
                        else{
                            Err((op,left,right))
                        }
                    },
                    (BinaryOp::Lesser | BinaryOp::LesserEquals | BinaryOp::Greater | BinaryOp::GreaterEquals,left,right) => {
                        if left == right && matches!(left,Type::Float|Type::Int){
                            Ok(Type::Bool)
                        }
                        else{
                            Err((op,left,right))
                        }
                    },
                    (BinaryOp::Equals | BinaryOp::NotEquals,left,right)  => {
                        if left == right{
                            Ok(Type::Bool)
                        }
                        else{
                            Err((op,left,right))
                        }
                    }
                };
                let ty = match ty{
                    Ok(ty) => ty,
                    Err((op,left,right)) => {
                        self.error(format!("'{}' does not support '{}' and '{}'.",op,left,right),expr.location.start_line);
                        return Err(TypeCheckFailed);
                    }
                };
                (ty,TypedExprNodeKind::Binary { op, left: Box::new(left), right: Box::new(right) })
            },
            ExprNodeKind::Logical { op, left, right } => {
                let op = match op{
                    ParsedLogicalOp::And => LogicalOp::And,
                    ParsedLogicalOp::Or => LogicalOp::Or
                };
                let left = self.check_expr(left, Some(&Type::Bool))?;
                let right = self.check_expr(right, Some(&Type::Bool))?;
                (Type::Bool,TypedExprNodeKind::Logical { op, left: Box::new(left), right: Box::new(right) })
            },
            ExprNodeKind::Assign { lhs, rhs } => {
                let (ty,target_kind) = match &lhs.kind{
                    ParsedAssignmentTargetKind::Name(name) => {
                        let Some((ty,id)) = self.get_type_of_value(name) else {
                            self.error(format!("Cannot use undefined value '{}'.",name),lhs.location.start_line);
                            return Err(TypeCheckFailed);
                        };
                        match id{
                            DefId::Function(func) => {
                                self.error(format!("Cannot assign to function '{}'.",name), lhs.location.start_line);
                                return Err(TypeCheckFailed);
                            },
                            DefId::Variable(variable) => {
                                (ty,TypedAssignmentTargetKind::Variable(variable))
                            }
                        }
                    },
                    ParsedAssignmentTargetKind::Index { lhs, rhs } => {
                        let lhs = self.check_expr(lhs, None)?;
                        let rhs = self.check_expr(rhs, None)?;
                        let result_ty = match (&lhs.ty,&rhs.ty){
                            (Type::Array(element_type),Type::Int) => *element_type.clone(),
                            (lhs_ty,rhs_ty) => {
                                self.error(format!("Cannot index into '{}' with '{}'.",lhs_ty,rhs_ty),lhs.location.start_line);
                                return Err(TypeCheckFailed);
                            }
                        };
                        (result_ty,TypedAssignmentTargetKind::Index { lhs: Box::new(lhs), rhs: Box::new(rhs) })
                    },
                    ParsedAssignmentTargetKind::Field { lhs, field } => {
                        let lhs = self.check_expr(lhs, None)?;
                        let Some(ty) = lhs.ty.get_field(&field.content, &self.type_context) else {
                            self.error(format!("{} has no '{}' field.",lhs.ty,field.content),field.location.start_line);
                            return Err(TypeCheckFailed);
                        };
                        (ty,TypedAssignmentTargetKind::Field { lhs: Box::new(lhs), name: field.clone() })
                    }
                };
                let rhs = self.check_expr(&rhs,Some(&ty))?;
                (ty.clone(),TypedExprNodeKind::Assign { lhs: TypedAssignmentTarget{location:lhs.location,ty,kind:target_kind}, rhs: Box::new(rhs) })
            },
            ExprNodeKind::Print(exprs) => {
                let exprs =  exprs.iter().map(|expr| self.check_expr(expr, None)).collect::<Result<Vec<_>,_>>()?;
                (Type::Unit,TypedExprNodeKind::Print(exprs))
            },
            ExprNodeKind::TypenameOf(ty) => {
                let ty = self.check_type(ty)?;
                (Type::String,TypedExprNodeKind::TypenameOf(ty))
            },
            ExprNodeKind::Tuple(elements) => {
                let elements = match expected_type{
                    Some(Type::Tuple(element_types)) if element_types.len() == elements.len() => {
                        elements.iter().zip(element_types).map(|(element,element_type)|{
                            self.check_expr(element, Some(element_type))
                        }).collect::<Result<Vec<_>,_>>()?
                    },
                    _ => {
                        elements.iter().map(|element|{
                            self.check_expr(element, None)
                        }).collect::<Result<Vec<_>,_>>()?
                    }
                };
                let element_types = elements.iter().map(|element| element.ty.clone()).collect::<Vec<_>>();
                if element_types.is_empty() {(Type::Unit,TypedExprNodeKind::Unit)} else {(Type::Tuple(element_types),TypedExprNodeKind::Tuple(elements))}
            },
            ExprNodeKind::Array(elements) => {
                let mut expected_element_type = match expected_type{
                    Some(Type::Array(elements)) => Some(*elements.clone()),
                    _ => None
                };

                let elements = elements.iter().map(|element|{
                    let element = self.check_expr(element, expected_element_type.as_ref())?;
                    if expected_element_type.is_none(){
                        expected_element_type = Some(element.ty.clone());
                    }
                    Ok(element)
                }).collect::<Result<Vec<_>,_>>()?;
                let Some(element_type) = expected_element_type else {
                    self.error("Cannot infer type of empty array.".to_string(),expr.location.start_line);
                    return Err(TypeCheckFailed);
                };
                (Type::Array(Box::new(element_type)),TypedExprNodeKind::Array(elements))
            },
            ExprNodeKind::While { condition, body } => {
                let condition = self.check_expr(condition, Some(&Type::Bool))?;
                let body = self.check_expr(body, Some(&Type::Unit))?;
                (Type::Unit,TypedExprNodeKind::While { condition: Box::new(condition), body: Box::new(body) })
            },
            ExprNodeKind::If { condition, then_branch, else_branch } => {
                let condition = self.check_expr(&condition, Some(&Type::Bool))?;
                let then_branch = self.check_expr(then_branch, expected_type)?;
                let else_branch = if let Some(else_branch) = else_branch{
                    Some(self.check_expr(else_branch, expected_type)?)
                }
                else{
                    None
                };
                let ty = if let Some(else_branch) = &else_branch{
                    match (&then_branch.ty,&else_branch.ty){
                        (Type::Never,ty) | (ty,Type::Never) => ty.clone(),
                        (then_type,else_type) if then_type == else_type => then_type.clone(),
                        (then_type,else_type) => {
                            self.error(format!("'if' of type '{}' has incompatible type with 'else' {}.",then_type,else_type),else_branch.location.start_line);
                            return Err(TypeCheckFailed);
                        }
                    }
                }
                else if let ty @ (Type::Unit|Type::Never) = then_branch.ty.clone(){
                    ty
                } else {
                    self.error(format!("'if' with no else, must have type '{}'.",Type::Unit), then_branch.location.start_line);
                    return Err(TypeCheckFailed);
                };
                (ty,TypedExprNodeKind::If { condition:Box::new(condition), then_branch: Box::new(then_branch), else_branch: else_branch.map(|else_branch| Box::new(else_branch)) })
            },
            ExprNodeKind::Match { matchee, arms } => {
                let matchee = self.check_expr(matchee, None)?;
                let mut expected_type = expected_type.cloned();
                let arms = arms.iter().map(|arm|{
                    let pattern = self.resolve_pattern(&arm.pattern, Some(matchee.ty.clone()))?;
                    self.begin_scope();
                    self.define_bindings_in_pattern(&pattern);
                    let result = self.check_expr(&arm.expr, expected_type.as_ref());
                    self.end_scope();
                    let arm_expr = result?;
                    if let Some(expected_type) = expected_type.as_mut(){
                        if *expected_type == Type::Never && arm_expr.ty != Type::Never{
                            *expected_type = arm_expr.ty.clone();
                        }
                    }
                    
                    Ok(TypedPatternMatchArm{expr:arm_expr,ty:pattern.ty.clone(),pattern,location:arm.location})  
                }).collect::<Result<Vec<_>,_>>()?;
                (expected_type.unwrap_or(Type::Never),TypedExprNodeKind::Match { matchee:Box::new(matchee), arms })
            },
            ExprNodeKind::Return(return_expr) => {
                let Some(enclosing_function) = self.enclosing_functions.last() else{
                    self.error("Cannot 'return' outside of a function.".to_string(),expr.location.start_line);
                    return Err(TypeCheckFailed);
                };
                let return_type = enclosing_function.return_type.clone();
                let return_expr = if let Some(expr) =  return_expr.as_ref().map(|return_expr| self.check_expr(return_expr, Some(&return_type))){
                    Some(Box::new(expr?))
                } else {
                    None
                };
                (Type::Never,TypedExprNodeKind::Return { expr: return_expr })
            },
            ExprNodeKind::Function(function) => {
                let signature = self.check_signature(function)?;
                let function =  self.check_function(function, signature)?;
                let params = function.signature.params.iter().map(|(_,ty)|{ ty.clone()}).collect();
                let return_type = function.signature.return_type.clone();
                let ty = Type::Function { generic_args:Vec::new(), params , return_type: Box::new(return_type) };
                (ty,TypedExprNodeKind::Function(function))
            },
            ExprNodeKind::Block { stmts, expr } => {
                self.begin_scope();
                let result = (||{
                    let stmts = self.check_stmts(stmts)?;
                    let expr = if let Some(expr) = expr.as_ref().map(|expr| self.check_expr(expr, expected_type)){
                        Some(expr?)
                    }
                    else{
                        None
                    };
                    Ok((stmts,expr))
                })();
                self.end_scope();
                let (stmts,expr) = result?;
                let ty = if let Some(expr) = expr.as_ref(){
                    expr.ty.clone()
                }
                else if stmts.iter().any(|stmt| match stmt {
                    TypedStmtNode::Expr(expr) | TypedStmtNode::ExprWithSemi(expr) | TypedStmtNode::Let { expr,.. } => expr.ty == Type::Never,
                    _ => false
                }){
                    Type::Never
                } else {
                    Type::Unit
                };
                (ty,TypedExprNodeKind::Block { stmts, expr: expr.map(Box::new) })
            },
            ExprNodeKind::Index { lhs, rhs } => {
                let lhs = self.check_expr(lhs, None)?;
                let rhs = self.check_expr(rhs, None)?;
                
                let elemnt_type = match (&lhs.ty,&rhs.ty) {
                    (Type::Array(element_type),Type::Int) => *element_type.clone(),
                    (lhs,rhs) => {
                        self.error(format!("Cannot index into '{}' with '{}'.",lhs,rhs), expr.location.start_line);
                        return Err(TypeCheckFailed);
                    }
                };

                (elemnt_type,TypedExprNodeKind::Index { lhs: Box::new(lhs), rhs: Box::new(rhs) })
            },
            ExprNodeKind::Call { callee, args } => {
                let generic_function = if let ExprNodeKind::Get(name) = &callee.kind{
                    self.get_type_of_value(name).map_or(Ok(None),|(ty,id)|{
                        let DefId::Function(func) = id else {
                            return Ok(None);
                        };
                        let Some(is_generic) = self.environment.get_function_by_id(func).map(|func| func.is_generic) else {
                            unreachable!("All functions in scope should be defined.")
                        };
                        let Type::Function { generic_args, params, return_type } = ty.clone() else {
                            unreachable!("Functions should only have function types.")
                        };
                        if is_generic && !generic_args.is_empty(){
                            if params.len() != args.len(){
                                self.error(format!("Expected '{}' args got '{}'.",params.len(),args.len()),expr.location.start_line);
                                return Err(TypeCheckFailed);
                            }
                            enum InferenceError{
                                InferenceFailed,
                                TypeCheckFailed
                            }
                            let (args,generic_args) = (||{
                                let mut inferred_args : IndexMap<_,_> = generic_args.iter().cloned().map(|ty| (ty,None)).collect();
                                if let Some(expected_type) = expected_type{
                                    infer_types(&mut inferred_args, &return_type,expected_type).map_err(|_| InferenceError::InferenceFailed)?;
                                }
                                let args = args.iter().zip(params).map(|(arg,param_type)|{
                                    let expected_param_type = inferred_args.get(&param_type).and_then(|ty: &Option<Type>| ty.as_ref());
                                    let expr = self.check_expr(arg, expected_param_type).map_err(|_| InferenceError::TypeCheckFailed)?;
                                    infer_types(&mut inferred_args,&param_type,&expr.ty).map_err(|_| InferenceError::InferenceFailed )?;
                                    Ok(expr)
                                } ).collect::<Result<Vec<_>,_>>()?;
                                inferred_args.into_iter().map(|(_,ty)| match ty{
                                    Some(ty) => Ok(ty),
                                    None => Err(InferenceError::InferenceFailed)
                                }).collect::<Result<Vec<_>,_>>().map(|inferred_args| (args,inferred_args))
                            })().map_err(|err|{
                                    if let InferenceError::InferenceFailed =  err{
                                        self.error(format!("Cannot fully infer generic parameters."),expr.location.start_line);
                                    }
                                    TypeCheckFailed
                                }
                            )?;
                            let return_type = substitute(*return_type, &generic_args);
                            Ok(Some((return_type.clone(),TypedExprNodeKind::Call { callee: Box::new(TypedExprNode{
                                location:callee.location,
                                kind: TypedExprNodeKind::GetGeneric{name:GenericName::Function(func),args:generic_args},
                                ty
                            }), 
                            args})))
                        }
                        else{
                            Ok(None)
                        }
                    })
                } else {
                    Ok(None)
                }?;
                if let Some((ty,function)) = generic_function{
                    (ty,function)
                }
                else{
                    let callee = self.check_expr(callee, None)?;
                    let Type::Function { params, return_type,.. } = callee.ty.clone() else {
                        self.error(format!("Cannot call '{}'.",callee.ty), callee.location.start_line);
                        return Err(TypeCheckFailed);
                    }; 
                    if params.len() != args.len(){
                        self.error(format!("Expected '{}' args got '{}'.",params.len(),args.len()),expr.location.start_line);
                        return Err(TypeCheckFailed);
                    }

                    let args = args.iter().zip(params).map(|(arg,param_type)|{
                        self.check_expr(arg, Some(&param_type))
                    } ).collect::<Result<Vec<_>,_>>()?;


                    (*return_type,TypedExprNodeKind::Call { callee: Box::new(callee), args })
                }
            },
            _ => todo!("EXPR")
        };
        if let Some(expected) = expected_type{
            if self.check_type_match(&ty, expected,expr.location.start_line).is_err(){
                return Err(TypeCheckFailed);
            }
        }
        Ok(TypedExprNode { location: expr.location, ty, kind })
    }


    fn next_item(&mut self,item:Item,segment:&PathSegment,full_location : SourceLocation)->Result<Item,TypeCheckFailed>{
        let next_item = match item{
            Item::Type(ty) => {
                if let Type::Enum { id,generic_args,.. } = ty{
                    self.type_context.enums.get_enum(todo!("Use correct ids")).variants.iter().find(|variant| &variant.name == &segment.name.content).map(|variant| 
                        Item::Variant(Type::EnumVariant { generic_args, id, name:variant.name.clone(), variant_index: variant.discrim },todo!("Use correct ids"), variant.discrim))
                }
                else if let Some(method) = self.environment.get_method(&ty, &segment.name.content){
                    Some(Item::Method(ty.clone(),segment.name.clone(),method.generic_types.clone()))
                }
                else{
                    None
                }
            },
            _ => None
            
        };
        let Some(next_item) = next_item else {
            self.error("Invalid path.".to_string(), full_location.start_line);
            return Err(TypeCheckFailed);
        };
        let generic_args = if let Some(parsed_generic_args) = &segment.generic_args{
            let generic_args = self.check_generic_args(parsed_generic_args)?;
            
            Some((generic_args,parsed_generic_args.location))
        }
        else{
            None
        };
        if let Some((generic_args,location)) = generic_args{
            match next_item{
                Item::Type(ty) => {
                    let ty = self.get_substituted(ty, &generic_args,location)?;
                    Ok(Item::Type(ty))
                }
                Item::Method(ty, method,expected) => {
                    let generic_arg = if let Some(expected_generic_args) = expected{
                        if generic_args.len() != expected_generic_args.len(){
                            self.error(format!("Expected '{}' generic arguments got '{}'.",expected_generic_args.len(),generic_args.len()),location.start_line);
                            return Err(TypeCheckFailed);
                        }
                        Some(generic_args)
                    }
                    else{
                        None
                    };
                    Ok(Item::Method(ty, method, generic_arg))
                },
                Item::Variant(..) => {
                    self.error(format!("Cannot pass generic parameters to variant type."), segment.location.start_line);
                    Err(TypeCheckFailed)
                }
            }
        }
        else if let Item::Method(ty, method,expected) = next_item {
            if let Some(expected_generic_args) = expected{
                self.error(format!("Expected '{}' generic arguments got '{}'.",expected_generic_args.len(),0),segment.location.start_line);
                return Err(TypeCheckFailed);
            }
            else{
                Ok(Item::Method(ty, method, expected))
            }
        }
        else{
            
            Ok(next_item)
        }
    }

    fn get_item_from_path(&mut self,path:&ParsedPath)->Result<Item,TypeCheckFailed>{
        let ty = self.get_named_type(&path.head.name.content,path.location)?;
        let generic_args = if let Some(generic_args) = path.head.generic_args.as_ref() { Some((self.check_generic_args(generic_args)?,generic_args.location)) } else {None};
        let mut item =  Item::Type(if let Some((generic_args,location)) = generic_args { self.get_substituted(ty,&generic_args ,location )?}else { ty });
        for segment in &path.segments{
            item = self.next_item(item,segment, path.location)?;
        }
        Ok(item) 
    }
    fn get_expr_path(&mut self,path:&ParsedPath)->Result<(Type, TypedExprNodeKind), TypeCheckFailed>{
        if path.segments.is_empty(){
            if let Some(generic_args) = path.head.generic_args.as_ref(){
                if let Some((ty,DefId::Function(id))) = self.get_type_of_value(&path.head.name.content){
                    let Type::Function { generic_args:expected,.. } = ty.clone() else {
                        unreachable!("Can't have non function with function value.")
                    };
                    let generic_args = self.check_generic_args(generic_args)?;
                    if generic_args.len() != expected.len(){
                        self.error(format!("Expected '{}' generic arguments got '{}'.",expected.len(),generic_args.len()),path.head.location.start_line);
                        return Err(TypeCheckFailed);
                    }
                    return Ok((substitute(ty, &generic_args),TypedExprNodeKind::GetGeneric { name:GenericName::Function(id), args: generic_args}));
                }
                else{
                    self.error("Can only pass generic args to functions or types.".to_string(), path.head.location.start_line);
                    return Err(TypeCheckFailed);
                }
            }
            return todo!("VALUES");
        }
        else{
            let item = self.get_item_from_path(path)?;
            match item {
                Item::Method(base_type, method_name, generic_args) =>{
                    let method = self.environment.get_method(&base_type, &method_name.content).expect("Already checked for method.");
                    let ty = Type::Function { generic_args: method.generic_types.clone().unwrap_or_default(), params: method.param_types.clone(), return_type: Box::new(method.return_type.clone())};
                    if let Some(generic_args) = generic_args{
                        Ok((substitute(ty, &generic_args),TypedExprNodeKind::GetGeneric { name:GenericName::Method{
                            ty:base_type,
                            method_name:method_name.content,
                        }, args: generic_args}))
                    }
                    else{
                        
                        Ok((ty,TypedExprNodeKind::GetMethod { ty: base_type, method: method_name }))
                    }
                },
                Item::Variant(ty, enum_id, discrim) => {
                    let variant = &self.type_context.enums.get_enum(enum_id).variants[discrim];
                    if !variant.fields.is_empty(){
                        let variant_name = variant.name.clone();
                        self.error(format!("Cannot initialize '{}' variant without fields.",variant_name), path.location.start_line);
                        return Err(TypeCheckFailed);
                    }
                    else{
                        Ok((ty,TypedExprNodeKind::StructInit { kind: InitKind::Variant(enum_id, discrim), fields: Vec::new() }))
                    }
                },
                Item::Type(ty) => {
                    self.error(format!("Cannot get value for type '{}'.",ty), path.location.start_line);
                    return Err(TypeCheckFailed);
                }
            }
        }
    }
    fn check_generic_args(&mut self,args:&ParsedGenericArgs)->Result<Vec<Type>,TypeCheckFailed>{
        args.types.iter().map(|ty| self.check_type(ty)).collect::<Result<Vec<_>,_>>()
    }
    fn get_substituted(&mut self,ty:Type,generic_args:&[Type],location : SourceLocation)->Result<Type,TypeCheckFailed>{
        let expected_args = match &ty { 
            Type::Struct { generic_args, .. }|Type::Enum { generic_args, .. } if generic_args.iter().all(|ty| !ty.is_closed()) => {
                generic_args
            },
            ty => {
                self.error(format!("Cannot apply generic args to non-generic type \"{}\".",ty), location.start_line);
                return Err(TypeCheckFailed);
            }
        };
        if generic_args.len() != expected_args.len(){
            self.error(format!("Expected '{}' generic args, but got '{}'.",expected_args.len(),generic_args.len()),location.start_line);
            return Err(TypeCheckFailed);
        }
        let subbed_generic_args = generic_args;
        Ok(substitute(ty, &subbed_generic_args))
    }
    fn get_named_type(&mut self,name:&str,location : SourceLocation)->Result<Type,TypeCheckFailed>{
        Ok(match name{
            "int" => Type::Int,
            "float" => Type::Float,
            "string" => Type::String,
            "bool" => Type::Bool,
            "never" => Type::Never,
            "Self" => if let Some(ty) = self.self_type.clone() {
                ty
            }
            else{
                self.error("Cannot use \"Self\" in this context.".to_string(),location.start_line);
                return Err(TypeCheckFailed);
            },
            type_name => {
                if let Some(index) = self.environment.get_generic_param(&name){
                    Type::Param(GenericParamType { name: name.to_string(), index })
                }
                else if let Some(ty) = self.environment.get_type(type_name){
                    ty.clone()
                }
                else{
                    self.error(format!("Used undefined type \"{}\".",name), location.start_line);
                    return Err(TypeCheckFailed);
                }
            }
        })
    }
    fn check_type(&mut self,ty:&ParsedType)->Result<Type,TypeCheckFailed>{
        
        fn get_type_at_path(this:&mut TypeChecker,path:&ParsedPath)->Result<Type,TypeCheckFailed>{
            let (Item::Type(ty) | Item::Variant(ty,..)) = this.get_item_from_path(path)? else {
                this.error(format!("Cannot get a type from this path."), path.location.start_line);
                return Err(TypeCheckFailed);
            };
            Ok(ty)
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
    fn check_generic_params(&mut self,generic_params : &ParsedGenericParams)->Result<Vec<GenericParamType>,TypeCheckFailed>{
        let mut had_error = false;
        let mut generic_param_names = IndexSet::new();
        
        for ParsedGenericParam(name) in &generic_params.0{
            if !generic_param_names.insert(name.content.clone()){
                self.error(format!("Repeated generic parameter name \"{}\".",name.content),name.location.start_line);
                had_error = true;
            }
        }
        if had_error{
            return Err(TypeCheckFailed);
        }
        
        let generic_params =  generic_param_names.iter().map(|name|{
            let index = self.environment.add_generic_param(name.clone());
            GenericParamType{name:name.clone(),index}
        }).collect();
        Ok(generic_params)
        
    }

    fn check_type_not_in_local_scope(&mut self,name:&str,location : SourceLocation)->Result<(),TypeCheckFailed>{
        
        if self.environment.is_type_in_local_scope(name){
            self.error(format!("A type with name '{}' is already defined.",name),location.start_line);
            return Err(TypeCheckFailed);
        }

        Ok(())
    }
    fn check_stmt(&mut self,stmt:&StmtNode)->Result<Option<TypedStmtNode>,TypeCheckFailed>{
        let stmt = match stmt{
            &StmtNode::Expr { ref expr, has_semi } => {
                Some(if !has_semi{
                    TypedStmtNode::Expr( self.check_expr(expr, Some(&Type::Unit))?)
                }
                else{
                    TypedStmtNode::ExprWithSemi(self.check_expr(expr, None)?)
                })
            },
            StmtNode::Let { pattern, expr ,ty,id} => {
                let ty = if let Some(ty) = ty.as_ref(){ self.check_type(ty).map(Some)} else {Ok(None)};
                let expr = self.check_expr(expr, ty.as_ref().ok().and_then(|ty| ty.as_ref()));
                let (pattern,expr) = match (||{
                    match (ty,expr) {
                        (Ok(ty),Ok(expr)) => {
                            Ok((ty.unwrap_or_else(||expr.ty.clone()),expr))
                        },
                        (Ok(ty),Err(_)) => {
                            Err(ty)
                        },
                        (Err(_),Ok(expr)) => {
                            Err(Some(expr.ty.clone()))
                        },
                        (Err(_),Err(_)) => Err(None)
                    }

                })() {
                    Ok((ty,expr)) => {
                        let pattern = self.resolve_pattern(pattern, Some(ty.clone()))?;
                        if !patterns::is_exhaustive(&[&pattern],&ty,&self.type_context){
                            self.error("Can't use non-irrefutable pattern in 'let' statement.".to_string(), pattern.location.start_line);
                            self.define_bindings_in_pattern(&pattern);
                            return Err(TypeCheckFailed);
                        }
                        self.define_bindings_in_pattern(&pattern);
                        (pattern,expr)
                    },
                    Err(expected) => {
                        let pattern = self.resolve_pattern(pattern, expected)?;
                        self.define_bindings_in_pattern(&pattern);
                        return Err(TypeCheckFailed);
                    }
                };
                Some(TypedStmtNode::Let{
                    pattern,
                    expr
                })
            },
            StmtNode::Fun { name,generic_params, function ,id} => {
                let function_name = name.content.clone();
                if self.environment.is_function_in_local_scope(&function_name){
                    self.error(format!("Repeated function name '{}'.",function_name), name.location.start_line);
                    return Err(TypeCheckFailed);
                }
                let id = self.identifiers.define_function(function_name);
                let generic_params = if let Some(generic_params) = generic_params.as_ref(){
                    Some(self.check_generic_params(generic_params)?)
                } else {
                    None
                };
                let function = (||{
                    let Ok(signature) = self.check_signature(function) else {
                        self.environment.add_function(name.content.clone(), Function { 
                            id, 
                            is_generic: generic_params.is_some(),
                            generic_types: generic_params.as_ref().unwrap_or(&Vec::new()).iter().map(|param|{
                                Type::Param(param.clone())
                            }).collect(),
                            param_types:vec![Type::Unknown;function.params.len()], 
                            return_type:Type::Unknown 
                        });
                        return Err(TypeCheckFailed);
                    };

                    let param_types = signature.params.iter().map(|(_,ty)| ty.clone()).collect();
                    let return_type = signature.return_type.clone();

                    self.environment.add_function(name.content.clone(), Function { 
                        id, 
                        is_generic: generic_params.is_some(),
                        generic_types: generic_params.as_ref().unwrap_or(&Vec::new()).iter().map(|param|{
                            Type::Param(param.clone())
                        }).collect(),
                        param_types, 
                        return_type 
                    });
                    self.check_function(function, signature)
                })();
                let name = ResolvedSymbol { id, location: name.location };
                Some(if let Some(generic_params) = generic_params{
                    self.environment.remove_generic_params(generic_params.len());
                    function.map(|function| TypedStmtNode::GenericFunction { name, function , generic_params: generic_params.iter().map(|param| param.index).collect()})
                }
                else{
                    function.map(|function| TypedStmtNode::Fun { name , function })
                }?)
            },
            StmtNode::Struct { name, generic_params, fields ,id} => {
                self.check_type_not_in_local_scope(&name.content,name.location)?;
                let struct_name = name.content.clone();
                let generic_params = if let Some(generic_params) = generic_params{
                    Some(match self.check_generic_params(generic_params){
                        Ok(params) => params,
                        Err(_) => {
                            self.environment.add_type(struct_name, Type::Unknown);
                            return Err(TypeCheckFailed);
                        }
                    })
                }
                else{
                    None
                };
                let id = self.type_context.structs.define_struct (vec![].into_iter() );
                let generic_param_types = generic_params.map_or(Vec::new(), |params| params.into_iter().map(|param| Type::Param(param)).collect());
                let struct_type = Type::Struct { 
                    generic_args: generic_param_types.clone(), 
                    id:todo!("Use correct ids"), 
                    name: struct_name.clone()
                };
                self.environment.add_type(struct_name.clone(), struct_type.clone());
                let mut field_names = HashSet::new();
                let fields = fields.iter().map(|(field,ty)|{
                    let field_type = self.check_type(ty)?;
                    if !field_names.insert(&field.content){
                        self.error(format!("Repeated field '{}'.",field.content), field.location.start_line);
                        return Err(TypeCheckFailed);
                    }
                    if field_type == struct_type{
                        self.error(format!("Can't declare recursive 'struct' '{}'.",field_type),field.location.start_line);
                        return Err(TypeCheckFailed);
                    }
                    Ok((field.clone(),field_type))
                }).collect::<Result<Vec<_>,_>>();

                self.environment.remove_generic_params(generic_param_types.len());
                fields.map(|fields| {
                    self.type_context.structs.update_struct_info(&id, |struct_info|{
                        struct_info.add_fields(fields.clone().into_iter().map(|(name,ty)|{
                            (name.content,ty)
                        }));
                    });
                })?;
                None
            },
            StmtNode::Enum {name,generic_params,variants,id} => {
                self.check_type_not_in_local_scope(&name.content, name.location)?;
                let enum_name = name.content.clone();
                let generic_params = if let Some(generic_params) = generic_params.as_ref(){
                    Some(self.check_generic_params(generic_params)?)
                } else {
                    None
                };
                let id = self.type_context.enums.define_enum(enum_name.clone(),Vec::new());
                let enum_type = 
                    Type::Enum { 
                        id:todo!("Use correct ids"), 
                        name: enum_name.clone(),
                        generic_args:generic_params.as_ref().unwrap_or(&Vec::new()).iter().cloned().map(|param| Type::Param(param)).collect()
                    };

                self.environment.add_type(enum_name.clone(), enum_type.clone());                
                let variants = (||{
                    let mut seen_variant_names = HashSet::new();
                    variants.iter().map(|variant|{
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
                            if ty == enum_type{
                                self.error(format!("Can't declare recursive 'enum' '{}'.",ty),field_name.location.start_line);
                                return Err(TypeCheckFailed);
                            }
                            Ok((field_name.clone(),ty))
                        }).collect::<Result<Vec<_>,_>>()?;
                        Ok(TypedEnumVariant{
                            name : variant.name.clone(),
                            fields
                        })
                    }).collect::<Result<Vec<_>,_>>()
                })();
                self.environment.remove_generic_params(generic_params.unwrap_or_default().len());
                variants.map(|variants| {
                    self.type_context.enums.update_enum(id, |enum_|{
                        enum_.variants = variants.iter().enumerate().map(|(i,variant)|{
                            EnumVariant{
                                discrim:i,
                                name : variant.name.content.clone(),
                                fields:variant.fields.iter().map(|(field_name,ty)|{(field_name.content.clone(),ty.clone())}).collect()
                            }
                        }).collect();
                    });
                })?;
                None
            },
            StmtNode::Impl { ty, methods,id } => {
                let self_type = self.check_type(ty)?;
                let old_type = self.self_type.take();
                self.self_type = Some(self_type.clone());
                let methods = methods.iter().map(|method|{
                    let generic_params = if let Some(generic_params) = method.generic_params.as_ref(){
                        Some(self.check_generic_params(generic_params)?)
                    } else {
                        None
                    };
                    let is_generic = generic_params.is_some();
                    let method_function_and_receiver = (||{
                        let signature = self.check_signature(&method.function)?;
                        let receiver_info = method.has_receiver.then(||{
                            method.function.params.first().unwrap().by_ref
                        });
                        if !self.environment.add_method(
                            self_type.clone(),
                        method.name.content.clone(),
                        Method{
                                name : method.name.content.clone(),
                                self_param_info : receiver_info,
                                generic_types : generic_params.as_ref().map(|params| params.iter().cloned().map(|param| Type::Param(param)).collect()),
                                param_types : signature.params.iter().map(|(_,ty)| ty.clone()).collect(),
                                return_type : signature.return_type.clone()
                            }
                        ){
                            self.error(format!("There is already a method with name '{}' for type \"{}\".",method.name.content,self_type), method.name.location.start_line);
                            return Err(TypeCheckFailed);
                        }
                        let method_function = self.check_function(&method.function, signature.clone())?;
                        Ok((method_function,receiver_info))
                    })();

                    self.environment.remove_generic_params(generic_params.unwrap_or(Vec::new()).len());
                    let (method_function,receiver_info) = method_function_and_receiver?;
                    Ok(TypedMethod{name:method.name.clone(),function:method_function,receiver_info,is_generic})
                }).collect::<Result<Vec<_>,TypeCheckFailed>>();
                self.self_type = old_type;
                Some(TypedStmtNode::Impl { ty: self_type, methods:methods?})
            }
        };
        Ok(stmt)
    }
    fn check_stmts(&mut self,stmts:&[StmtNode])->Result<Vec<TypedStmtNode>,TypeCheckFailed>{
        let mut typed_stmts = Vec::new();
        let mut had_error  = false;   
        for stmt in stmts{
            if let Ok(stmt) = self.check_stmt(stmt){
                let Some(stmt) = stmt else {
                    continue;
                };
                typed_stmts.push(stmt);
            }
            else{
                had_error = true;
            }
        }

        if !had_error { Ok(typed_stmts)} else {Err(TypeCheckFailed)}

    }
    pub fn check(mut self,stmts:Vec<ResolvedStmt>)->Result<(TypeContext,Vec<TypedStmtNode>,Identifiers),TypeCheckFailed>{
        let input = self.identifiers.define_function("input".to_string());
        self.environment.add_function("input".to_string(), Function { id:input, is_generic: false, generic_types: vec![], param_types: vec![], return_type: Type::String });
        let panic = self.identifiers.define_function("panic".to_string());
        self.environment.add_function("panic".to_string(), Function{id:panic,is_generic:false,generic_types:vec![],param_types:vec![Type::String], return_type: Type::Never});
        todo!("FIX")
    }
}