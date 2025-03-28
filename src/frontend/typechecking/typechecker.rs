use std::cell::Cell;

use fxhash::{FxHashMap, FxHashSet};

use crate::{data_structures::IndexVec, frontend::{ast_lowering::{hir::{self}, SymbolInterner}, tokenizing::SourceLocation, typechecking::typed_ast::{self, FieldExpr}}, identifiers::{EnumIndex, FieldIndex, FuncIndex, ImplIndex, ItemIndex, StructIndex}};
use super::{
    env::Environment, generics::infer_types, patterns::{self, is_exhaustive}, typed_ast::{BinaryOp, ConstructorKind, Expr, ExprKind, FieldPattern, Function, FunctionId, FunctionParam, FunctionSignature, GenericName, LogicalOp, NumberKind, Pattern, PatternKind, PatternMatchArm, Stmt, StmtKind, UnaryOp}, types::{GenericArgs, GenericParamType, Type}, EnumDef, FieldDef, StructDef, VariantDef};
use super::TypeContext;

#[derive(Clone)]
struct EnclosingFunction{
    return_type : Type
}
pub type NameContext = ();
struct TypeLowerer;
impl TypeLowerer{
    fn error(&self,message:String,span:SourceLocation){
        eprintln!("Error on line {}: {}",span.start_line,message);
    }
    fn lower_type(&self,ty:&hir::Type) -> Type{
        match &ty.kind{
            hir::TypeKind::Tuple(elements) => Type::Tuple(elements.into_iter().map(|ty| self.lower_type(ty)).collect()),
            hir::TypeKind::Array(element) => Type::Array(Box::new(self.lower_type(element))),
            hir::TypeKind::Function(args, return_type) => Type::Function(
                GenericArgs::new(),
                args.into_iter().map(|ty| self.lower_type(ty)).collect(),
                Box::new(return_type.as_ref().map_or(Type::new_unit(), |ty| self.lower_type(ty)))
            ),
            hir::TypeKind::Path(path) => {
                match path.def{
                    hir::PathDef::Enum(enum_index) => {
                        Type::Enum(GenericArgs::new(), enum_index)
                    },
                    hir::PathDef::PrimitiveType(ty) => match ty{
                        hir::PrimitiveType::Int => Type::Int,
                        hir::PrimitiveType::Bool => Type::Bool,
                        hir::PrimitiveType::Float => Type::Float,
                        hir::PrimitiveType::Never => Type::Never,
                        hir::PrimitiveType::String => Type::String
                    },
                    hir::PathDef::Struct(struct_index) => {
                        Type::Struct(GenericArgs::new(), struct_index)
                    },
                    _ => {
                        self.error(format!("Cannot use {} as type.","TODO: ADD ACTUAL PATH ERROR"), path.span);
                        Type::Unknown
                    }
                }
            }

        }
    }
}

enum Item{
    Struct(StructIndex),
    Enum(EnumIndex),
    Function(FuncIndex)
}
pub struct TypeCheckFailed;
struct ParamToCheck{
    pattern : hir::Pattern,
    ty : Type
}
struct FunctionToCheck{
    params : Vec<ParamToCheck>,
    return_type : Type,
    body : hir::Expr
}
pub struct TypeChecker<'a>{
    environment : Environment,
    enclosing_functions : Vec<EnclosingFunction>,
    self_type : Option<Type>,
    interner : &'a SymbolInterner,
    context : TypeContext,
    items : IndexVec<ItemIndex,Item>,
    functions : IndexVec<FuncIndex,(hir::Ident,Option<FunctionToCheck>)>,
    checked_functions : IndexVec<FunctionId,Function>,
    had_error : Cell<bool>
}
impl<'a> TypeChecker<'a>{
    pub fn new(interner:&'a SymbolInterner)->Self{
        Self{
            environment: Environment::new(),
            enclosing_functions : Vec::new(),
            interner,
            self_type : None,
            items: IndexVec::new(),
            functions:IndexVec::new(),
            checked_functions:IndexVec::new(),
            context : TypeContext::new(),
            had_error : Cell::new(false)
        }
    }


    fn error(&self,message:String,span:SourceLocation){
        eprintln!("Error on line {}: {}",span.start_line,message);
        self.had_error.set(true);
    }
    fn display_path(&self,path:&hir::PathDef) -> String{
        match path{
            &hir::PathDef::Enum(enum_index) => {
                format!("enum {}",self.interner.get(self.context.enums[enum_index].name.index))
            },
            &hir::PathDef::Struct(struct_index) => {
                format!("struct {}",self.interner.get(self.context.structs[struct_index].name.index))
            },
            &hir::PathDef::Variable(variable) => {
                format!("variable {}",self.interner.get(self.context.variables[variable]))
            },
            &hir::PathDef::Function(function) => {
                format!("function {}",self.interner.get(self.functions[function].0.index))
            },
            &hir::PathDef::Variant(enum_index, variant_index) => {
                format!("variant {}",self.interner.get(self.context.enums[enum_index].variants[variant_index].0.name.index))
            },
            &hir::PathDef::PrimitiveType(primitive_ty) => {
                match primitive_ty{
                    hir::PrimitiveType::Bool => "bool".to_string(),
                    hir::PrimitiveType::Float => "float".to_string(),
                    hir::PrimitiveType::Int => "int".to_string(),
                    hir::PrimitiveType::Never => "never".to_string(),
                    hir::PrimitiveType::String => "string".to_string(),
                }
            }
        }
    }
    fn type_mismatch_error(&self,span:SourceLocation,expected:&Type,got:&Type){
        self.error(format!("Expected \"{}\" got \"{}\".",expected.display_type(&self.context, self.interner),got.display_type(&self.context, self.interner)),span);
    }
    pub fn define_bindings_in_pattern(&mut self,pattern:&Pattern){
        match &pattern.kind{
            &PatternKind::Binding(id,ref inner_pattern) => {
                self.environment.define_variable_type(id, pattern.ty.clone());
                if let Some(pattern) =  inner_pattern.as_ref(){
                    self.define_bindings_in_pattern(pattern);
                }
            },
            PatternKind::Tuple(elements) =>{
                for element in elements{
                    self.define_bindings_in_pattern(element);
                }
            },
            PatternKind::Constructor {fields,.. } => {
                for FieldPattern{index:_,pattern} in fields{
                    self.define_bindings_in_pattern(pattern);
                }
            },
            PatternKind::Literal(_)|PatternKind::Wildcard => (),
        }
        
    }
    
    pub fn check_pattern(&mut self,pattern:hir::Pattern, expected_type:Option<Type>) -> Result<Pattern,TypeCheckFailed>{
        let (kind,ty)= match pattern.kind{
            hir::PatternKind::Binding(id,_,inner_pattern) => {
                let binding_pattern = if let Some(pattern) = inner_pattern{ 
                    let pattern = self.check_pattern(*pattern, expected_type.clone())?;
                    Some(Box::new(pattern))
                }
                else{ 
                    None 
                };
                let ty = if let Some(pat) = binding_pattern.as_ref(){
                    pat.ty.clone()
                }
                else if let Some(expected_type) = expected_type.clone(){
                    expected_type
                } 
                else {
                    self.error(format!("Cannot infer type of binding '{}'.",self.interner.get(self.context.variables[id])),pattern.span);
                    return Err(TypeCheckFailed);
                };
                (PatternKind::Binding(id,binding_pattern),ty)
            },
            hir::PatternKind::Wildcard => {
                (PatternKind::Wildcard,expected_type.clone().ok_or_else(||{
                    self.error("Cannot infer type of '_'.".to_string(),pattern.span);
                    TypeCheckFailed
                })?)
            },
            hir::PatternKind::Tuple(patterns) => {
                let elements = if let Some(ty) = expected_type.clone(){
                    let elements = match ty {
                        Type::Tuple(elements) if elements.len() == patterns.len() => elements,
                        _ => {
                            self.type_mismatch_error(pattern.span,&Type::Tuple(vec![Type::Unknown;patterns.len()]),&ty);
                            return Err(TypeCheckFailed);
                        }
                    };
                    elements.into_iter().map(|element| Some(element)).collect()
                }
                else{
                    vec![None;patterns.len()]
                };
                let patterns : Vec<_> = patterns.into_iter().zip(elements.clone()).map(|(pattern,ty)| self.check_pattern(pattern,ty) ).collect::<Result<_,_>>()?;
                let elements = patterns.iter().map(|pattern| pattern.ty.clone()).collect();
                (PatternKind::Tuple(patterns),Type::Tuple(elements))
            },
            hir::PatternKind::Literal(literal) => {
                (PatternKind::Literal(literal),match literal{
                    hir::LiteralKind::Int(_) => Type::Int,
                    hir::LiteralKind::Float(_) => Type::Float,
                    hir::LiteralKind::Bool(_) => Type::Bool,
                    hir::LiteralKind::String(_) => Type::String
                })
            },
            hir::PatternKind::Struct(path, fields ) => {
                todo!("Struct patterns")
            },
        };
        if let Some(expected_type) = &expected_type{
            self.check_type_match(&ty, expected_type, pattern.span)?;
        }
        Ok(Pattern { span:pattern.span,kind ,ty})
    }
    fn check_type_match(&mut self,ty:&Type,expected_type:&Type,span:SourceLocation)->Result<(),TypeCheckFailed>{
        if ty != expected_type &&  ty != &Type::Never {
            self.type_mismatch_error(span, expected_type, ty);
            return Err(TypeCheckFailed);
        }
        Ok(())
    }
    fn check_expr(&mut self,expr:hir::Expr,expected_type : Option<&Type>)->Result<Expr,TypeCheckFailed>{
        let (ty,kind) = match expr.kind{
            hir::ExprKind::Literal(literal) => {
                let ty = match literal{
                    hir::LiteralKind::Int(_) => Type::Int,
                    hir::LiteralKind::Float(_) => Type::Float,
                    hir::LiteralKind::Bool(_) => Type::Bool,
                    hir::LiteralKind::String(_) => Type::String
                };
                (ty,ExprKind::Literal(literal))
            },
            hir::ExprKind::Typename(ty) => (Type::String,ExprKind::Typename(TypeLowerer.lower_type(&ty))),
            hir::ExprKind::Tuple(elements) => 
                match expected_type{
                    Some(ty @ Type::Tuple(element_types)) if element_types.len() == elements.len() => {
                        let elements = elements.into_iter().zip(element_types).map(|(expr,ty)|{
                            self.check_expr(expr, Some(ty))
                        }).collect::<Result<Vec<_>,_>>()?;
                        (ty.clone(),ExprKind::Tuple(elements))
                    },
                    _ => {
                        let elements = elements.into_iter().map(|expr|{
                            self.check_expr(expr, None)
                        }).collect::<Result<Vec<_>,_>>()?;
                        (Type::Tuple(elements.iter().map(|element| element.ty.clone()).collect()),ExprKind::Tuple(elements))
                    }
                },
            hir::ExprKind::Array(elements) => {
                let mut element_type = if let Some(Type::Array(element)) = expected_type{
                    Some(*element.clone())
                }
                else{
                    None
                };
                let elements = elements.into_iter().map(|element|{
                    let expr = self.check_expr(element, element_type.as_ref())?;
                    if element_type.is_none(){
                        element_type = Some(expr.ty.clone());
                    }
                    Ok(expr)
                }).collect::<Result<Vec<_>,_>>()?;
                (
                    if let Some(element_type) = element_type{
                        Type::Array(Box::new(element_type))
                    } 
                    else {
                        self.error(format!("Cannot infer type of empty array."),expr.span);
                        return Err(TypeCheckFailed);
                    },
                    ExprKind::Array(elements)
                )
            },
            hir::ExprKind::Binary(op, left, right) => {
                let (left_type,right_type) = match (op,expected_type){
                    (BinaryOp::Add | BinaryOp::Subtract | BinaryOp::Multiply | BinaryOp::Divide,Some(ty @ &(Type::Int | Type::Float))) => (Some(ty.clone()),Some(ty.clone())),
                    (BinaryOp::Add , Some(&Type::String)) => (Some(Type::String),Some(Type::String)),
                    _ => (None,None)
                };
                let left = self.check_expr(*left, left_type.as_ref())?;
                let right = self.check_expr(*right, right_type.as_ref())?;
                let result_type = if left.ty == right.ty { 
                    match (&left.ty,op) {
                        (_,BinaryOp::NotEquals | BinaryOp::Equals) => Some(Type::Bool),
                        (ty @ (Type::Int | Type::Float), op ) => match op{
                            BinaryOp::Add|BinaryOp::Subtract|BinaryOp::Multiply|BinaryOp::Divide => Some(ty.clone()),
                            BinaryOp::Lesser | BinaryOp::Greater | BinaryOp::LesserEquals | BinaryOp::GreaterEquals | BinaryOp::NotEquals | BinaryOp::Equals => Some(Type::Bool),
                        },
                        (Type::String,BinaryOp::Add) => Some(Type::String),
                        _ => None
                    }
                }
                else { None };
                let Some(result_type) = result_type else {
                    self.error(format!("Can't apply '{}' to '{}' and '{}'.",op,left.ty.display_type(&self.context, &self.interner),right.ty.display_type(&self.context, &self.interner)),expr.span);
                    return Err(TypeCheckFailed);
                };
                (result_type,ExprKind::Binary { op, left: Box::new(left), right: Box::new(right) })
            },
            hir::ExprKind::Logical(op, left, right) => {
                let left = self.check_expr(*left, Some(&Type::Bool))?;
                let right = self.check_expr(*right, Some(&Type::Bool))?;
                if left.ty != right.ty || left.ty != Type::Bool{
                    self.error(format!("Can't apply '{}' to '{}' and '{}'.",op,left.ty.display_type(&self.context, &self.interner),right.ty.display_type(&self.context, &self.interner)),expr.span);
                    return Err(TypeCheckFailed);
                }
                (Type::Bool,ExprKind::Logical { op, left: Box::new(left), right: Box::new(right) })
            },
            hir::ExprKind::Unary(op, operand) => {
                let expected_type = match (expected_type,op){
                    (Some(ty @ (Type::Int|Type::Float)),UnaryOp::Negate) => Some(ty.clone()),
                    _ => None
                };
                let operand = self.check_expr(*operand, expected_type.as_ref())?;
                let Some(result_type) = expected_type else {
                    self.error(format!("Can't apply '{}' to '{}'.",op,operand.ty.display_type(&self.context, &self.interner)), expr.span);
                    return Err(TypeCheckFailed);
                };
                (result_type,ExprKind::Unary { op, operand: Box::new(operand) })
            },
            hir::ExprKind::Field(receiver, field) => {
                let receiver = self.check_expr(*receiver, None)?;
                let (generic_args,struct_index) = match &receiver.ty{
                    &Type::Struct(ref generic_args, struct_index) => (generic_args.clone(),struct_index),
                    ty => {
                        self.error(format!("'{}' has no fields.",ty.display_type(&self.context, &self.interner)), receiver.span);
                        return Err(TypeCheckFailed);
                    } 
                };
                let Some((field_index,field_ty)) = self.context.get_field_index(ConstructorKind::Struct(struct_index), field.index).map(|field_index|{
                    (field_index,self.context.get_field_type(ConstructorKind::Struct(struct_index), &generic_args, field_index))
                }) else {
                    self.error(format!("'{}' has no field '{}'.",receiver.ty.display_type(&self.context, &self.interner),self.interner.get(field.index)),field.span);
                    return Err(TypeCheckFailed);
                };
                (field_ty,ExprKind::Field(Box::new(receiver),field_index))
            },
            hir::ExprKind::Print(operands) => {
                let operands = operands.into_iter().map(|operand|{
                    self.check_expr(operand, None)
                }).collect::<Result<Vec<_>,_>>()?;
                (Type::new_unit(),ExprKind::Print(operands))
            },
            hir::ExprKind::While(condition, body) => {
                let condition = self.check_expr(*condition, Some(&Type::Bool))?;
                let body = self.check_expr(*body, Some(&Type::new_unit()))?;
                (Type::new_unit(),ExprKind::While { condition:Box::new(condition), body:Box::new(body) })
            },
            hir::ExprKind::If(condition,then_branch ,else_branch )  => {
                let condition = self.check_expr(*condition, Some(&Type::Bool))?;
                let then_branch = self.check_expr(*then_branch, expected_type)?;
                if let Some(else_branch) =  else_branch{
                    let else_branch = self.check_expr(*else_branch, expected_type)?;
                    let ty = if then_branch.ty == Type::Never {
                        else_branch.ty.clone()
                    }
                    else if else_branch.ty == Type::Never || else_branch.ty == then_branch.ty{
                        then_branch.ty.clone()
                    }
                    else{
                        self.error(format!("'if' and 'else' have incompatible types of {} and {}.",
                            then_branch.ty.display_type(&self.context, self.interner),
                            else_branch.ty.display_type(&self.context, self.interner)),
                        then_branch.span);
                        return Err(TypeCheckFailed);
                    };
                    (ty,ExprKind::If { condition: Box::new(condition), then_branch: Box::new(then_branch), else_branch: Some(Box::new(else_branch)) })
                
                }
                else if matches!(&then_branch.ty,Type::Never) || then_branch.ty.is_unit(){
                    (Type::new_unit(),ExprKind::If { condition: Box::new(condition), then_branch: Box::new(then_branch), else_branch: None })
                }
                else{
                    self.error(format!("'if' of type '{}' must have 'else'.",then_branch.ty.display_type(&self.context, self.interner)), then_branch.span);
                    return Err(TypeCheckFailed);
                }
            },
            hir::ExprKind::Match(matchee, arms) => {
                let matched_expr = self.check_expr(*matchee, None)?;
                let mut expected_type = expected_type.cloned();
                let arms = arms.into_iter().map(|arm|{
                    let pattern = self.check_pattern(arm.pat, Some(matched_expr.ty.clone()))?;
                    self.define_bindings_in_pattern(&pattern);
                    let body = self.check_expr(arm.body, expected_type.as_ref())?;
                    if expected_type.is_none() && body.ty != Type::Never{
                        expected_type = Some(body.ty.clone());
                    }
                    Ok(PatternMatchArm{
                        span:SourceLocation::new(pattern.span.start_line, body.span.end_line),
                        pattern,
                        body
                    })
                }).collect::<Result<Vec<_>,_>>()?;
                let patterns = arms.iter().map(|arm| &arm.pattern).collect::<Vec<_>>();
                if !is_exhaustive(&patterns, &matched_expr.ty, &self.context){
                    self.error("Pattern match is not exhaustive.".to_string(),matched_expr.span);
                    return Err(TypeCheckFailed);
                }
                (expected_type.unwrap_or(Type::Never),ExprKind::Match { matchee: Box::new(matched_expr), arms })
            },
            hir::ExprKind::Index(indexed,index ) => {
                let indexed = self.check_expr(*indexed,None)?;
                let index = self.check_expr(*index, None)?;
                let (Type::Array(element_type),Type::Int) = (indexed.ty.clone(),index.ty.clone()) else{
                    self.error(format!("'[]' only supports '{}' and '{}'.",indexed.ty.display_type(&self.context, self.interner),index.ty.display_type(&self.context, self.interner)), indexed.span);
                    return Err(TypeCheckFailed);
                };
                (*element_type,ExprKind::Index { lhs: Box::new(indexed), rhs: Box::new(index) })
            },
            hir::ExprKind::StructLiteral(path,fields) => {
                let kind = match path.def {
                    hir::PathDef::Struct(struct_index) => ConstructorKind::Struct(struct_index),
                    hir::PathDef::Variant(enum_index, variant_index) => ConstructorKind::Variant(enum_index, variant_index),
                    def => {
                        self.error(format!("Expected a struct or enum constructor got '{}'.",self.display_path(&def)), path.span);
                        return Err(TypeCheckFailed);
                    }
                };
                let generic_args = GenericArgs::new();
                let fields = {
                    let mut seen_fields = FxHashSet::default();
                    fields.into_iter().map(|field_expr|{
                        let Some(field_index) = self.context.get_field_index(kind, field_expr.field.index) else {
                            self.error(format!("Undefined field '{}'.",self.interner.get(field_expr.field.index)), field_expr.field.span);
                            return Err(TypeCheckFailed);
                        };
                        if !seen_fields.insert(field_index){
                            self.error(format!("Repeated field '{}'.",self.interner.get(field_expr.field.index)), field_expr.field.span);
                            return Err(TypeCheckFailed);
                        }
                        let field_type = self.context.get_field_type(kind, &generic_args, field_index);
                        let Ok(field_expr) = self.check_expr(field_expr.expr, Some(&field_type)) else {
                            return Err(TypeCheckFailed);
                        };
                        Ok(FieldExpr{index:field_index,expr:field_expr})
                    }).collect::<Result<Vec<_>,_>>()?
                };
                let ty = match kind{
                    ConstructorKind::Struct(struct_index) => Type::Struct(generic_args, struct_index),
                    ConstructorKind::Variant(enum_index,_) => Type::Enum(generic_args, enum_index)
                };
                (ty,ExprKind::Constructor { kind, fields })
            },
            hir::ExprKind::Assign(target, value) => {
                let target = self.check_expr(*target, expected_type)?;
                let value = self.check_expr(*value, Some(&target.ty))?;
                (Type::new_unit(),ExprKind::Assign { lhs:Box::new(target), rhs: Box::new(value) })
            },
            hir::ExprKind::Block(stmts, expr) => {
                let stmts = self.check_stmts(stmts)?;
                let (ty,expr) = if let Some(expr) = expr{
                    let expr = self.check_expr(*expr, expected_type)?;
                    (expr.ty.clone(),Some(expr))
                }
                else{
                    let is_never = stmts.iter().any(|stmt| 
                        matches!(&stmt.kind,StmtKind::Expr(expr) | StmtKind::Let {  expr,.. } if expr.ty == Type::Never)
                    );
                    (if is_never{
                        expected_type.cloned().unwrap_or_else(|| Type::new_unit())
                    }
                    else{
                        Type::new_unit()
                    },None)
                };
                (ty,ExprKind::Block { stmts, expr:expr.map(Box::new) })
            },
            hir::ExprKind::Function(function) => {
                let (param_types,return_type,function) = self.lower_function(*function);
                let function  = self.check_function(function)?;
                (Type::Function(GenericArgs::new(), param_types,Box::new(return_type)),ExprKind::AnonFunction(function))
            },
            hir::ExprKind::Return(return_expr) => {
                let Some(enclosing_function) = self.enclosing_functions.last() else {
                    self.error(format!("Can't have 'return' outside of function."), expr.span);
                    return Err(TypeCheckFailed);
                };
                let return_ty = enclosing_function.return_type.clone();
                let return_expr = if let Some(return_expr) = return_expr{
                    Some(self.check_expr(*return_expr, Some(&return_ty))?)
                }
                else if return_ty.is_unit(){
                    None
                }
                else{
                    self.error(format!("Cannot use empty return in non '()' function."),expr.span);
                    return Err(TypeCheckFailed);
                };
                (Type::Never,ExprKind::Return { expr: return_expr.map(Box::new) })
            },
            hir::ExprKind::Call(callee, args) => {
                let callee = self.check_expr(*callee, None)?;
                let Type::Function(generic_args, params, return_type) = &callee.ty else {
                    self.error(format!("Expected a callable type got '{}'.",callee.ty.display_type(&self.context, self.interner)), callee.span);
                    return Err(TypeCheckFailed);
                };
                if params.len() != args.len(){
                    self.error(format!("Expected '{}' args got '{}'.",params.len(),args.len()),expr.span);
                    return Err(TypeCheckFailed);
                }
                let args = args.into_iter().zip(params).map(|(arg,ty)|  self.check_expr(arg, Some(ty))).collect::<Result<Vec<_>,_>>()?;
                let return_type = *return_type.clone();
                (return_type,ExprKind::Call { callee: Box::new(callee), args })
                
            },
            hir::ExprKind::Path(path) => {
                match path.def{
                    def @ hir::PathDef::Variant(enum_index, variant_index) => {
                        let VariantDef(variant_info) = &self.context.enums[enum_index].variants[variant_index];
                        if variant_info.fields.is_empty(){
                            (Type::Enum(GenericArgs::new(), enum_index),ExprKind::Constructor { kind: ConstructorKind::Variant(enum_index, variant_index), fields: vec![] })
                        }
                        else{
                            self.error(format!("Constructing '{}' requires fields.",self.display_path(&def)), path.span);
                            return Err(TypeCheckFailed);
                        }
                    },
                    hir::PathDef::Variable(variable) => {
                        (self.environment.get_variable_type(variable),ExprKind::Variable(variable))
                    },
                    hir::PathDef::Function(function) => {
                        (self.environment.get_function_type(function),ExprKind::Function(function))
                    },
                    def => {
                        self.error(format!("Expected a value got '{}'.",self.display_path(&def)), path.span);
                        return Err(TypeCheckFailed);
                    }
                }
            }
        };
        if let Some(expected) = expected_type{
            if self.check_type_match(&ty, expected,expr.span).is_err(){
                return Err(TypeCheckFailed);
            }
        }
        Ok(Expr { span:expr.span, ty, kind })
    }
    fn check_recursive(&self,ty:&Type)->Result<(),TypeCheckFailed>{
        match ty{
            Type::Array(element) => {
                self.check_recursive(element)?;
            },
            Type::Bool | Type::Int | Type::Float | Type::String | Type::Unknown | Type::Never | Type::Param(_) => (),
            Type::Function(generic_args, params, return_type) => {
                generic_args.iter().try_for_each(|arg| self.check_recursive(&arg.ty))?;
                params.iter().try_for_each(|param| self.check_recursive(param))?;
                self.check_recursive(return_type)?;
            },
            Type::Struct(generic_args, index) => {
                generic_args.iter().try_for_each(|arg| self.check_recursive(&arg.ty))?;

            },
            Type::Enum(generic_args, index) => {
                generic_args.iter().try_for_each(|arg| self.check_recursive(&arg.ty))?;

            },
            Type::Tuple(elements) => elements.iter().try_for_each(|element| self.check_recursive(element))?,
        }
        Ok(())
    }
    fn check_stmt(&mut self,stmt:hir::Stmt)->Result<Option<Stmt>,TypeCheckFailed>{
        let kind = match stmt.kind{
            hir::StmtKind::Expr(expr)=> Some(StmtKind::Expr(self.check_expr(expr, Some(&Type::new_unit()))?)),
            hir::StmtKind::Semi(expr) => {
                let expr = self.check_expr(expr, None)?;
                let fake_pattern = Pattern { span: SourceLocation::one_line(expr.span.start_line), kind: PatternKind::Wildcard, ty: expr.ty.clone() };
                Some(StmtKind::Let{
                    pattern: fake_pattern,
                    expr
                })
            },
            hir::StmtKind::Let(pattern,ty,expr) => {
                let ty = ty.as_ref().map(|ty| TypeLowerer.lower_type(ty));
                let expr = self.check_expr(expr, ty.as_ref());
                let type_and_expr = match (ty,expr) {
                    (Some(ty),Ok(expr)) => {
                        Ok((ty,expr))
                    },
                    (Some(ty),Err(_)) => Err(Some(ty)),
                    (None,Ok(expr)) => Err(Some(expr.ty.clone())),
                    (None,Err(_)) => Err(None)
                };
                let (pattern,expr) = match type_and_expr {
                        Ok((ty,expr)) => {
                            let pattern = self.check_pattern(pattern, Some(ty.clone()))?;
                            self.define_bindings_in_pattern(&pattern);
                            if !patterns::is_exhaustive(&[&pattern],&ty,&self.context){
                                self.error("Can't use non-irrefutable pattern in 'let' statement.".to_string(), pattern.span);
                                return Err(TypeCheckFailed);
                            }
                            (pattern,expr)
                        },
                        Err(expected) => {
                            let pattern = self.check_pattern(pattern, expected)?;
                            self.define_bindings_in_pattern(&pattern);
                            return Err(TypeCheckFailed);
                        }
                };
 
                Some(StmtKind::Let{
                    pattern,
                    expr
                })
            },
            hir::StmtKind::Item(item) => {
                match self.items[item]{
                    Item::Struct(struct_index) => {
                        let args = GenericArgs::new();
                        self.check_recursive(&Type::Struct(args, struct_index))?;
                        
                    },
                    Item::Enum(enum_index) => {
                        let args = GenericArgs::new();
                        self.check_recursive(&&Type::Enum(args, enum_index))?;
                    },
                    Item::Function(function) => {
                        let (_,function) = &mut self.functions[function];
                        let function = function.take().expect("Should be able to take a function body");
                        let function = self.check_function(function)?;
                        self.checked_functions.push(function);

                    },
                }
                None
            }
        };
        Ok(kind.map(|kind|Stmt{kind}))
    }
    fn check_function(&mut self,function:FunctionToCheck) -> Result<Function,TypeCheckFailed>{
        self.enclosing_functions.push(EnclosingFunction { return_type: function.return_type.clone()});
        let params_and_body =  (||{
            let params = function.params.into_iter().map(|param|{
                let pattern = param.pattern;
                let ty = param.ty;
                let pattern = self.check_pattern(pattern, Some(ty.clone()))?;
                self.define_bindings_in_pattern(&pattern);
                Ok(FunctionParam{
                    pattern,
                    ty,
                })
            }).collect::<Result<Vec<_>,_>>()?;
            let body = self.check_expr(function.body, Some(&function.return_type))?;
            Ok((params,body))
        })();
        self.enclosing_functions.pop();
        let (params,body) = params_and_body?;
        Ok(Function { 
            signature: FunctionSignature{
                params,
                return_type:function.return_type
            }, 
            body:Box::new(body) 
        })
    }
    fn check_stmts(&mut self,stmts:Vec<hir::Stmt>)->Result<Vec<Stmt>,TypeCheckFailed>{
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
    fn lower_function(&mut self,function:hir::Function) -> (Vec<Type>,Type,FunctionToCheck){
        let return_type = function.return_type.as_ref().map_or_else(Type::new_unit, |ty| TypeLowerer.lower_type(ty));
        let mut param_types = Vec::new();
        let params = function.params.into_iter().map(|param|{
            let param_type = TypeLowerer.lower_type(&param.ty);
            param_types.push(param_type.clone());
            ParamToCheck{ 
                pattern : param.pattern,
                ty:param_type
            }
        }).collect();
        (param_types,return_type.clone(),FunctionToCheck { params,return_type,body:function.body })
    }
    fn lower_item(&mut self,item:hir::Item) -> Item{
        match item{
            hir::Item::Struct(generics, struct_info) => {
                Item::Struct(self.context.structs.push(StructDef{
                    name : struct_info.name,
                    fields : struct_info.fields.into_iter().map(|field|{
                        FieldDef{
                            name : field.name,
                            ty : TypeLowerer.lower_type(&field.ty)
                        }
                    }).collect()
                }))
            },
            hir::Item::Enum(generics, name,variants) => {
                Item::Enum(self.context.enums.push(EnumDef{
                    name,
                    variants:variants.into_iter().map(|variant|{
                        VariantDef(StructDef { name: variant.name, fields: variant.fields.into_iter().map(|field|{
                            FieldDef { name: field.name, ty: TypeLowerer.lower_type(&field.ty) }
                        }).collect() })
                    }).collect()
                }))
            },
            hir::Item::Function(function_def) => {
                let (param_types,return_type,function) = self.lower_function(function_def.function);
                let function_index = self.functions.push((function_def.name,
                    Some(function))
                );
                self.environment.define_function_type(function_index, Type::Function(GenericArgs::new(), param_types, Box::new(return_type)));
                Item::Function(function_index)
            },
            hir::Item::Impl(ty, methods) => {
                todo!("Impl lowering")
            }
        }
    }
    fn lower_items(&mut self,items:IndexVec<ItemIndex,hir::Item>){
        self.items = items.into_iter().map(|item|{
            self.lower_item(item)
        }).collect();
    }   
    pub fn check(mut self,items:IndexVec<ItemIndex,hir::Item>,stmts:Vec<hir::Stmt>)->Result<(TypeContext,Vec<Stmt>),TypeCheckFailed>{
        self.lower_items(items);
        let stmts = self.check_stmts(stmts)?;
        Ok((self.context,stmts))
    }
}