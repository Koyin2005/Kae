use std::{collections::{BTreeSet, HashMap, HashSet}, marker::PhantomData};

use fxhash::{FxHashMap, FxHashSet};

use crate::frontend::{name_resolution::resolved_ast::ConstructorPatternField, parsing::ast::{ExprNode, ExprNodeKind, LiteralKind, NodeId, ParsedAssignmentTargetKind, ParsedBinaryOp, ParsedEnumVariant, ParsedFunction, ParsedLogicalOp, ParsedParam, ParsedPath, ParsedPatternNode, ParsedPatternNodeKind, ParsedType, ParsedUnaryOp, PathSegment, StmtNode}, typechecking::{typed_ast::{BinaryOp, LogicalOp, UnaryOp}, types::Type}};

use super::{resolved_ast::{ConstructorField, ConstructorKind, ResolvedExpr, ResolvedExprKind, ResolvedFunction, ResolvedFunctionParam, ResolvedMatchArm, ResolvedPattern, ResolvedPatternKind, ResolvedStmt}, EnumInfo, FieldIndex, FieldInfo, Fields, FuncIndex, FunctionInfo, FunctionParamInfo, IndexVec, IntoIndex, NameContext, StructIndex, StructInfo, VariableIndex, VariantIndex, VariantInfo};

pub struct ResolutionError;
#[derive(Default,Clone)]
pub struct Scope{
    functions : FxHashMap<String,FuncIndex>,
    types : FxHashMap<String,Type>,
    variables : FxHashSet<String>
}
pub struct Resolver<'a>{
    context : NameContext,
    prev_scopes : Vec<Scope>,
    current_scope : Scope,
    variant_map : FxHashMap<NodeId,&'a [ParsedEnumVariant]>,
    scope_map : FxHashMap<NodeId,Scope>,
    constructor_map : FxHashMap<NodeId,ConstructorKind>,
    field_map : FxHashMap<NodeId,FieldIndex>

}
impl<'a> Resolver<'a>{
    fn push_scope(&mut self,scope:Scope){
        let old_scope = std::mem::replace(&mut self.current_scope, scope);
        self.prev_scopes.push(old_scope);

    }
    fn begin_scope(&mut self){
        self.push_scope(Scope::default());
    }
    fn end_scope(&mut self)->Scope{
        std::mem::replace(&mut self.current_scope, self.prev_scopes.pop().expect("Can only end a scope if a scope already exists"))
    }
    fn error(&self,message:String,line:u32){
        eprintln!("Error on line {} : {}",line,message)
    }
    fn resolve_type_by_name(&self,name:&str)->Option<Type>{
        
        match name{
            "int" => Some(Type::Int),
            "string" => Some(Type::String),
            "float" => Some(Type::Float),
            "bool" => Some(Type::Bool),
            "never" => Some(Type::Never),
            name => {
                let Some(ty) =  self.current_scope.types.get(name).or_else(||{ 
                    self.prev_scopes.iter().rev().filter_map(|scope| scope.types.get(name)).next()
                }) else {
                    return None;
                };
                Some(ty.clone())
            }
        }
    }
    fn resolve_type_path(&self,path:&ParsedPath) -> Result<Type,ResolutionError>{
        if path.segments.is_empty(){
            let Some(ty) = self.resolve_type_by_name(&path.head.name.content) else {
                self.error(format!("Cannot use undefined type '{}'.",path.head.name.content),path.head.location.start_line);
                return Err(ResolutionError);
            };
            Ok(ty)
        }
        else{
            let Some(base_type) = self.resolve_type_by_name(&path.head.name.content)else {
                self.error(format!("Cannot use undefined type '{}'.",path.head.name.content),path.head.location.start_line);
                return Err(ResolutionError);
            };
            todo!("ENUM TYPES")
        }
    }
    fn resolve_type(&self,ty:&ParsedType) -> Result<Type,ResolutionError>{
        match ty{
            ParsedType::Tuple(elements) => {
                Ok(Type::Tuple(elements.iter().map(|element| self.resolve_type(element)).collect::<Result<_,_>>()?))
            },
            ParsedType::Array(element) => {
                Ok(Type::Array(Box::new(self.resolve_type(element)?)))
            },
            ParsedType::Fun(args, return_type) => {
                Ok(
                    Type::Function { 
                        generic_args: Vec::new(), 
                        params: args.iter().map(|arg| self.resolve_type(arg)).collect::<Result<Vec<_>,_>>()?, 
                        return_type: Box::new(if let Some(return_type) = return_type{
                            self.resolve_type(&return_type)?
                        }
                        else{
                            Type::Unit
                        })
                    }
                )
            },
            ParsedType::Path(path) => {
                self.resolve_type_path(path)
            }
        }
    }
    fn resolve_pattern(&mut self,pattern:&ParsedPatternNode)->Result<ResolvedPattern,ResolutionError>{
        let kind = match &pattern.kind{
            ParsedPatternNodeKind::Name(variable) => {
                ResolvedPatternKind::Binding(self.define_variable(variable),None)
            },
            ParsedPatternNodeKind::Is(variable,checked_pattern) => {
                ResolvedPatternKind::Binding(self.define_variable(&variable.content), Some(Box::new(self.resolve_pattern(checked_pattern)?)))
            },
            ParsedPatternNodeKind::Tuple(elements) => {
                let elements = elements.iter().map(|element| self.resolve_pattern(element)).collect::<Result<Vec<_>,_>>()?;
                if elements.is_empty() { ResolvedPatternKind::Unit } else { ResolvedPatternKind::Tuple(elements) }
            },
            ParsedPatternNodeKind::Array(before,mid ,after) => {
                let before = before.iter().map(|element| self.resolve_pattern(element)).collect::<Result<Vec<_>,_>>()?;
                let mid = if let Some(mid) = mid.as_ref() { Some(self.resolve_pattern(mid)?) } else { None };
                let after = after.iter().map(|element| self.resolve_pattern(element)).collect::<Result<Vec<_>,_>>()?;
                todo!("Array patterns")
            },
            ParsedPatternNodeKind::Struct { fields,.. } => {
                let kind = self.constructor_map.remove(&pattern.id).expect("All struct constructors");
                let fields = fields.iter().map(|(_,field_pattern)| {
                    let pattern = self.resolve_pattern(field_pattern)?;
                    Ok(ConstructorPatternField{field:FieldIndex::new(0),pattern})
                }).collect::<Result<Vec<_>,_>>()?;
                ResolvedPatternKind::Constructor(kind, fields)
            },
            ParsedPatternNodeKind::Wildcard => ResolvedPatternKind::Wildcard,
            ParsedPatternNodeKind::Literal(literal) => ResolvedPatternKind::Literal(literal.clone())
        };
        Ok(ResolvedPattern{
            span : pattern.location,
            kind
        })
    }
    fn resolve_function(&mut self,id:NodeId,function:&ParsedFunction)->Result<ResolvedFunction,ResolutionError>{
        let scope = self.scope_map.remove(&id).expect("All scopes should be defined");
        self.push_scope(scope);
        let function = (||{
            let mut variables_in_args = BTreeSet::new();
            let params = function.params.iter().map(|ParsedParam{pattern,ty,..}|{
                let pattern = self.resolve_pattern(pattern)?;
                let ty = self.resolve_type(ty)?;
                let mut variables_in_pattern = BTreeSet::new();
                pattern.find_bindings(&mut variables_in_pattern);
                let repeated_variables = variables_in_args.intersection(&variables_in_pattern).copied().collect::<Box<_>>();
                if !repeated_variables.is_empty(){
                    let mut variables = String::new();
                    for (i,variable) in repeated_variables.iter().copied().enumerate(){
                        if i == repeated_variables.len()-1{
                            variables += " and ";
                        }
                        else if i < repeated_variables.len() - 1{
                            variables += ",";
                        }
                        variables += self.context.variable_info.get(variable).expect("All variables should have info");
                    }
                }
                variables_in_args.append(&mut variables_in_pattern);
                Ok(ResolvedFunctionParam{
                    pattern,
                    ty  
                })
            }).collect::<Result<Vec<_>,_>>()?;
            let return_type = if let Some(return_type) = &function.return_type { self.resolve_type(return_type)? } else { Type::Unit };
            let body = self.resolve_expr(&function.body)?;

            Ok((params,return_type,body))

        })();
        let scope = self.end_scope();
        let (params,return_type,body) = function?;
        Ok(ResolvedFunction{
            params,
            return_type,
            body,
            scope
        })
    }

    fn resolve_expr(&mut self,expr:&ExprNode) -> Result<ResolvedExpr,ResolutionError>{
        let kind = match &expr.kind {
            ExprNodeKind::Grouping(expr) => self.resolve_expr(expr)?.kind,
            ExprNodeKind::Function(function) =>  ResolvedExprKind::FunctionExpr(Box::new(self.resolve_function(expr.id,function)?)),
            ExprNodeKind::TypenameOf(ty) => ResolvedExprKind::Typename(self.resolve_type(ty)?),
            ExprNodeKind::Literal(literal)  => ResolvedExprKind::Literal(literal.clone()),
            ExprNodeKind::Array(elements) => ResolvedExprKind::Array(elements.iter().map(|element| self.resolve_expr(element)).collect::<Result<Vec<_>,_>>()?),
            ExprNodeKind::Tuple(elements) => if elements.is_empty() { ResolvedExprKind::Unit } else { ResolvedExprKind::Tuple(elements.iter().map(|element| self.resolve_expr(element)).collect::<Result<Vec<_>,_>>()?)},
            ExprNodeKind::Block { stmts, expr:result_expr } => {
                let scope = self.scope_map.remove(&expr.id).expect("All blocks should have scopes");
                self.push_scope(scope);
                let body = (||{
                    let stmts = self.resolve_stmts(stmts)?;
                    let result_expr = if let Some(result_expr) = result_expr.as_ref(){
                        Some(Box::new(self.resolve_expr(result_expr)?))
                    }
                    else{
                        None
                    };
                    Ok((stmts,result_expr))
                })();
                let scope = self.end_scope();
                let (stmts,result_expr) = body?;
                ResolvedExprKind::Block { scope, stmts, expr:result_expr }
            },
            ExprNodeKind::BinaryOp { op, left, right } => {
                let op = match op {
                    ParsedBinaryOp::Add => BinaryOp::Add,
                    ParsedBinaryOp::Subtract => BinaryOp::Subtract,
                    ParsedBinaryOp::Multiply => BinaryOp::Multiply,
                    ParsedBinaryOp::Divide => BinaryOp::Divide,
                    ParsedBinaryOp::Equals => BinaryOp::Equals,
                    ParsedBinaryOp::NotEquals => BinaryOp::NotEquals,
                    ParsedBinaryOp::Greater => BinaryOp::Greater,
                    ParsedBinaryOp::GreaterEquals => BinaryOp::GreaterEquals,
                    ParsedBinaryOp::Lesser => BinaryOp::Lesser,
                    ParsedBinaryOp::LesserEquals => BinaryOp::LesserEquals,
                };
                ResolvedExprKind::Binary(op, Box::new(self.resolve_expr(left)?), Box::new(self.resolve_expr(right)?))
            },
            ExprNodeKind::Logical { op, left, right } => {
                let op = match op {
                    ParsedLogicalOp::And => LogicalOp::And,
                    ParsedLogicalOp::Or => LogicalOp::Or
                };
                ResolvedExprKind::Logical(op, Box::new(self.resolve_expr(left)?), Box::new(self.resolve_expr(right)?))
            },
            ExprNodeKind::Unary { op, operand } => {
                let op = match op {
                    ParsedUnaryOp::Negate => UnaryOp::Negate,
                };
                ResolvedExprKind::Unary(op, Box::new(self.resolve_expr(operand)?))
            },
            ExprNodeKind::StructInit { fields,.. } => {
                let constructor = self.constructor_map.remove(&expr.id).expect("All constructors should have kinds");
                let fields = fields.iter().map(|(_,field_expr)|{
                    Ok(ConstructorField{
                        field : self.field_map.remove(&field_expr.id).expect("All constructor fields should be defined"),
                        expr : self.resolve_expr(field_expr)?

                    })
                }).collect::<Result<Vec<_>,_>>()?;
                ResolvedExprKind::Constructor { kind: constructor,fields }
            },
            ExprNodeKind::Match { matchee, arms } => {
                let matchee = self.resolve_expr(matchee)?;
                let arms = arms.iter().map(|arm|{
                    let scope = self.scope_map.remove(&arm.id).expect("All pattern arms should have scopes");
                    self.push_scope(scope);
                    let arm = (||{
                        let pattern = self.resolve_pattern(&arm.pattern)?;
                        let body = self.resolve_expr(&arm.expr)?;
                        Ok((pattern,body))
                    })();
                    let scope = self.end_scope();
                    let (pattern,body) = arm?;
                    Ok(ResolvedMatchArm{
                        scope,
                        pattern,
                        body
                    })
                }).collect::<Result<Vec<_>,_>>()?;
                ResolvedExprKind::Match(Box::new(matchee),arms)
            },
            ExprNodeKind::Index { lhs, rhs } => ResolvedExprKind::Index(Box::new(self.resolve_expr(lhs)?), Box::new(self.resolve_expr(rhs)?)),
            ExprNodeKind::Property(expr, field) => ResolvedExprKind::Field(Box::new(self.resolve_expr(expr)?), field.clone()),
            ExprNodeKind::While { condition, body } => ResolvedExprKind::While(Box::new(self.resolve_expr(condition)?), Box::new(self.resolve_expr(body)?)),
            ExprNodeKind::If { condition, then_branch, else_branch } => 
                ResolvedExprKind::If(Box::new(self.resolve_expr(condition)?), Box::new(self.resolve_expr(then_branch)?), 
                    else_branch.as_ref().map_or(Ok(None),|branch| self.resolve_expr(branch).map(Box::new).map(Some))?),
            ExprNodeKind::Print(args) => ResolvedExprKind::Print(args.iter().map(|arg| self.resolve_expr(arg)).collect::<Result<Vec<_>,_>>()?),
            ExprNodeKind::Call { callee, args } => ResolvedExprKind::Call(Box::new(self.resolve_expr(callee)?), args.iter().map(|arg| self.resolve_expr(arg)).collect::<Result<Vec<_>,_>>()?),
            ExprNodeKind::Return(expr) => {
                ResolvedExprKind::Return(expr.as_ref().map_or(Ok(None),|expr| self.resolve_expr(expr).map(Box::new).map(Some))?)
            },
            ExprNodeKind::MethodCall { receiver, method, args } => ResolvedExprKind::MethodCall(
                Box::new(self.resolve_expr(receiver)?),
                PathSegment{
                    name : method.clone(),
                    location : method.location,
                    generic_args : None
                },
                args.iter().map(|arg| self.resolve_expr(arg)).collect::<Result<Vec<_>,_>>()?
            ),
            ExprNodeKind::Assign { lhs, rhs } => todo!("Assignments"),
            ExprNodeKind::Get(_) | ExprNodeKind::GetPath(_) => todo!("Paths and variables")
        };
        let expr = ResolvedExpr { span: expr.location, kind };
        Ok(expr)
    }
    fn define_variable(&mut self,name:&str)->VariableIndex{
        let variable_index = self.context.variable_info.push(name.to_string());
        self.current_scope.variables.insert(name.to_string());
        variable_index
    }
    fn resolve_stmt(&mut self,stmt:&StmtNode) -> Result<Option<ResolvedStmt>,ResolutionError>{
        let stmt = match stmt{
            StmtNode::Expr { expr, has_semi } => {
                let expr = self.resolve_expr(expr)?;
                Some(if *has_semi { ResolvedStmt::Semi(expr) } else { ResolvedStmt::Expr(expr) })
            },
            StmtNode::Enum {..}|StmtNode::Struct {.. } => {
                None
            },
            StmtNode::Impl { ty, methods,id } => {
                None
            },
            &StmtNode::Fun { ref name, ref generic_params, ref function,id } => {
                self.resolve_function(id, function)?;
                None
            },
            StmtNode::Let { pattern, expr, ty,id } => {
                let pattern = self.resolve_pattern(pattern)?;
                let ty = ty.as_ref().map_or(Ok(None),|ty| self.resolve_type(ty).map(Some))?;
                let expr = self.resolve_expr(expr)?;
                Some(ResolvedStmt::Let(pattern, ty, expr))
            }
        };
        Ok(stmt)
    }
    fn find_names_in_function<'b:'a>(&mut self,id:NodeId,function:&'b ParsedFunction)->Result<(),ResolutionError>{
        self.begin_scope();
        let found_names_in_function = self.find_names_in_expr(&function.body);
        let scope = self.end_scope();   
        self.scope_map.insert(id, scope);
        found_names_in_function
    }
    fn find_names_in_expr<'b:'a>(&mut self,expr:&'b ExprNode)->Result<(),ResolutionError>{
        match &expr.kind{
            ExprNodeKind::Array(elements) | 
            ExprNodeKind::Tuple(elements) | 
            ExprNodeKind::Print(elements) => 
                elements.iter().try_for_each(|element| self.find_names_in_expr(element)),
            ExprNodeKind::BinaryOp {  left:first, right:second,.. } | 
            ExprNodeKind::Logical {   left:first, right:second,.. } |
            ExprNodeKind::While { condition:first, body:second } | 
            ExprNodeKind::Index { lhs:first, rhs:second } => {
                self.find_names_in_expr(first)?;
                self.find_names_in_expr(second)
            },
            ExprNodeKind::Assign { lhs, rhs } => {
                match &lhs.kind{
                    ParsedAssignmentTargetKind::Field { lhs, .. } => {
                        self.find_names_in_expr(lhs)?;
                    },
                    ParsedAssignmentTargetKind::Index { lhs, rhs } => {
                        self.find_names_in_expr(lhs)?;
                        self.find_names_in_expr(rhs)?;
                    },
                    ParsedAssignmentTargetKind::Name(_) => ()
                }
                self.find_names_in_expr(rhs)
            },
            ExprNodeKind::Match { matchee, arms } => {
                self.find_names_in_expr(matchee)?;
                arms.iter().try_for_each(|arm|{
                    self.find_names_in_expr(&arm.expr)
                })
            },
            ExprNodeKind::Unary { operand:expr,.. } | 
            ExprNodeKind::Grouping(expr) |
            ExprNodeKind::Property(expr, _) => {
                self.find_names_in_expr(expr)
            },
            ExprNodeKind::MethodCall { receiver:first, args,.. } | ExprNodeKind::Call { callee:first, args } => {
                self.find_names_in_expr(first)?;
                args.iter().try_for_each(|arg| self.find_names_in_expr(arg))
            },
            ExprNodeKind::If { condition, then_branch, else_branch } => {
                self.find_names_in_expr(condition)?;
                self.find_names_in_expr(then_branch)?;
                if let Some(else_branch) = else_branch{
                    self.find_names_in_expr(else_branch)?;
                }
                Ok(())
            },
            ExprNodeKind::Return(expr) => {
                if let Some(expr) = expr{
                    self.find_names_in_expr(expr)?;
                }
                Ok(())
            },
            ExprNodeKind::Block { stmts, expr:result_expr } => {
                self.begin_scope();
                let found_names_in_block = (||{
                    self.find_names_in_stmts(stmts)?;
                    if let Some(expr) = result_expr{
                        self.find_names_in_expr(expr)
                    }
                    else{
                        Ok(())
                    }
                })();
                let block_scope = self.end_scope();
                self.scope_map.insert(expr.id, block_scope);
                found_names_in_block
            },
            ExprNodeKind::StructInit {  fields ,..} => {
                for (_,field_expr) in fields{
                    self.find_names_in_expr(field_expr)?;
                }
                Ok(())
            },
            ExprNodeKind::Function(function) => {
                self.find_names_in_function(expr.id, function)
            },
            ExprNodeKind::Get(_) | ExprNodeKind::GetPath(_) | ExprNodeKind::TypenameOf(_) | ExprNodeKind::Literal(_) => {
                Ok(())
            },
        }
    }
    fn find_name_in_stmt<'b:'a>(&mut self,stmt:&'b StmtNode)->Result<(),ResolutionError>{
        match stmt{
            StmtNode::Enum { name, variants,id,.. } => {
                self.variant_map.insert(*id, variants);
                let mut seen_variants = HashSet::new();
                let variants = variants.iter().map(|variant|{
                    if !seen_variants.insert(&variant.name.content as &str){
                        self.error(format!("Repeated variant with name '{}'.",variant.name.content), variant.name.location.start_line);
                        return Err(ResolutionError);
                    }
                    Ok(VariantInfo{
                        name:variant.name.content.clone(),
                        fields: Fields::default(),
                    })
                }).collect::<Result<IndexVec<VariantIndex,_>,_>>()?;
                let variant_names = variants.iter().enumerate().map(|(i,variant)|{
                    (variant.name.clone(),VariantIndex::new(i))
                }).collect();
                let enum_index = self.context.enum_info.push(
                    EnumInfo{ 
                        name:name.content.clone(),
                        variants,
                        variant_names
                    });
                self.context.enum_id_map.insert(*id, enum_index);
                if self.current_scope.types.insert(name.content.clone(),Type::Enum { generic_args: Vec::new(), id:enum_index, name:name.content.clone() }).is_some(){
                    self.error(format!("Can't re-define type with name in same scope '{}'.",name.content), name.location.start_line);
                    return Err(ResolutionError);
                }
            },
            StmtNode::Struct { name,id,.. } => {
                let struct_index = self.context.struct_info.push(StructInfo{
                    name:name.content.clone(),
                    fields:Fields::default()
                });
                self.context.struct_id_map.insert(*id,struct_index);
                if self.current_scope.types.insert(name.content.clone(),Type::Struct { generic_args: Vec::new(), id:struct_index, name:name.content.clone() }).is_some(){
                    self.error(format!("Can't re-define type with name  in same scope'{}'.",name.content), name.location.start_line);
                    return Err(ResolutionError);
                }
            },
            StmtNode::Expr { expr, .. } => {
                self.find_names_in_expr(expr)?;
            },
            StmtNode::Impl { ty, methods,id } => {
                todo!("Find names in impl")
            },
            StmtNode::Fun { name,id,function,.. } => {
                let func_index = self.context.function_info.push(FunctionInfo{
                    name : name.content.clone(),
                    params : vec![FunctionParamInfo(Type::Unknown);function.params.len()],
                    return_type : Type::Unknown
                });
                self.context.function_id_map.insert(*id,func_index);
                if let Some(_) = self.current_scope.functions.insert(name.content.clone(), func_index){
                    self.error(format!("Can't re-define function with name '{}'.",name.content), name.location.start_line);
                    return Err(ResolutionError);
                }
                self.find_names_in_function(*id, function)?;
            },
            StmtNode::Let { expr, ..} => {
                self.find_names_in_expr(expr)?;
            }
        }
        Ok(())
    }
    fn find_names_in_stmts<'b:'a>(&mut self,stmts : &'b [StmtNode])->Result<(),ResolutionError>{
        for stmt in stmts{
            self.find_name_in_stmt(stmt)?;
        }
        Ok(())
    }
    
    fn bind_names_in_function<'b:'a>(&mut self,id:NodeId,function:&'b ParsedFunction)->Result<(),ResolutionError>{
        self.begin_scope();
        let function_signature = (||{
            let param_types = function.params.iter().map(|param|{
                self.resolve_type(&param.ty)
            }).collect::<Result<Vec<_>,_>>()?;
            let return_type = function.return_type.as_ref().map_or(Ok(Type::Unit),|ty| self.resolve_type(ty))?;
            Ok::<_,ResolutionError>((param_types,return_type))
        })();
        let found_names_in_function = if let Ok((param_types,return_type)) = function_signature{
            let function_index = self.context.function_id_map[&id];
            let function_info = self.context.function_info.get_mut(function_index).expect("All functions should be declared");
            for (param,param_ty) in (&mut function_info.params).into_iter().zip(param_types){
                param.0 = param_ty;
            }   
            function_info.return_type = return_type;
            self.bind_names_in_expr(&function.body)
        } else { Err(ResolutionError)};
        let scope = self.end_scope();   
        self.scope_map.insert(id, scope);
        found_names_in_function
    }
    fn bind_names_in_expr<'b:'a>(&mut self,expr:&'b ExprNode)->Result<(),ResolutionError>{
        match &expr.kind{
            ExprNodeKind::Array(elements) | 
            ExprNodeKind::Tuple(elements) | 
            ExprNodeKind::Print(elements) => 
                elements.iter().try_for_each(|element| self.bind_names_in_expr(element)),
            ExprNodeKind::BinaryOp {  left:first, right:second,.. } | 
            ExprNodeKind::Logical {   left:first, right:second,.. } |
            ExprNodeKind::While { condition:first, body:second } | 
            ExprNodeKind::Index { lhs:first, rhs:second } => {
                self.bind_names_in_expr(first)?;
                self.bind_names_in_expr(second)
            },
            ExprNodeKind::Assign { lhs, rhs } => {
                match &lhs.kind{
                    ParsedAssignmentTargetKind::Field { lhs, .. } => {
                        self.bind_names_in_expr(lhs)?;
                    },
                    ParsedAssignmentTargetKind::Index { lhs, rhs } => {
                        self.bind_names_in_expr(lhs)?;
                        self.bind_names_in_expr(rhs)?;
                    },
                    ParsedAssignmentTargetKind::Name(_) => ()
                }
                self.bind_names_in_expr(rhs)
            },
            ExprNodeKind::Match { matchee, arms } => {
                self.bind_names_in_expr(matchee)?;
                arms.iter().try_for_each(|arm|{
                    self.bind_names_in_expr(&arm.expr)
                })
            },
            ExprNodeKind::Unary { operand:expr,.. } | 
            ExprNodeKind::Grouping(expr) |
            ExprNodeKind::Property(expr, _) => {
                self.bind_names_in_expr(expr)
            },
            ExprNodeKind::MethodCall { receiver:first, args,.. } | ExprNodeKind::Call { callee:first, args } => {
                self.bind_names_in_expr(first)?;
                args.iter().try_for_each(|arg| self.bind_names_in_expr(arg))
            },
            ExprNodeKind::If { condition, then_branch, else_branch } => {
                self.bind_names_in_expr(condition)?;
                self.bind_names_in_expr(then_branch)?;
                if let Some(else_branch) = else_branch{
                    self.bind_names_in_expr(else_branch)?;
                }
                Ok(())
            },
            ExprNodeKind::Return(expr) => {
                if let Some(expr) = expr{
                    self.bind_names_in_expr(expr)?;
                }
                Ok(())
            },
            ExprNodeKind::Block { stmts, expr:result_expr } => {
                self.begin_scope();
                let found_names_in_block = (||{
                    self.bind_names_in_stmts(stmts)?;
                    if let Some(expr) = result_expr{
                        self.bind_names_in_expr(expr)
                    }
                    else{
                        Ok(())
                    }
                })();
                let block_scope = self.end_scope();
                self.scope_map.insert(expr.id, block_scope);
                found_names_in_block
            },
            ExprNodeKind::StructInit {  fields ,..} => {
                for (_,field_expr) in fields{
                    self.bind_names_in_expr(field_expr)?;
                }
                Ok(())
            },
            ExprNodeKind::Function(function) => {
                self.bind_names_in_function(expr.id,function)
            },
            ExprNodeKind::Get(_) | ExprNodeKind::GetPath(_) | ExprNodeKind::TypenameOf(_) | ExprNodeKind::Literal(_) => {
                Ok(())
            },
        }
    }
    fn bind_names_in_stmt<'b:'a>(&mut self,stmt:&'b StmtNode)->Result<(),ResolutionError>{
        match stmt{
            StmtNode::Struct {  id, generic_params, fields,.. } => {
                let struct_index = self.context.struct_id_map.get(id).copied().expect("All structs should be defined");
                let mut field_types:HashMap<_,_> = fields.iter().map(|(field_name,field_ty)|{
                    Ok((field_name.content.clone(),self.resolve_type(field_ty)?))
                }).collect::<Result<HashMap<_,_>,_>>()?;

                let struct_info = self.context.struct_info.get_mut(struct_index).expect("All structs should be defined");
                let mut field_info = IndexVec::new();
                let mut field_names = HashMap::new();

                for (field_name,_) in fields{
                    let ty = field_types.remove(&field_name.content).expect("All fields should still be in here");
                    let field_index = field_info.push(FieldInfo{
                        name : field_name.content.clone(),
                        ty
                    });
                    field_names.insert(field_name.content.clone(), field_index);
                }
                struct_info.fields.info = field_info;
                struct_info.fields.names = field_names;
            },
            StmtNode::Enum {  id, generic_params, variants ,..} => {
                let enum_index = self.context.enum_id_map.get(id).copied().expect("All enums should be defined");
                for variant in variants{
                    let mut field_types:HashMap<_,_> = variant.fields.iter().map(|(field_name,field_ty)|{
                        Ok((field_name.content.clone(),self.resolve_type(field_ty)?))
                    }).collect::<Result<HashMap<_,_>,_>>()?;

                    let enum_info = self.context.enum_info.get_mut(enum_index).expect("All enums should be defined");
                    let variant_index =  enum_info.variant_names.get(&variant.name.content).copied().expect("All variants nice and defined");
                    let variant_info = enum_info.variants.get_mut(variant_index).expect("All variants should be defined");
                    let mut field_info = IndexVec::new();
                    let mut field_names = HashMap::new();

                    for (field_name,_) in &variant.fields{
                        let ty = field_types.remove(&field_name.content).expect("All fields should still be in here");
                        let field_index = field_info.push(FieldInfo{
                            name : field_name.content.clone(),
                            ty
                        });
                        field_names.insert(field_name.content.clone(), field_index);
                    }
                    variant_info.fields.info = field_info;
                    variant_info.fields.names = field_names;
                }
            },
            StmtNode::Let { id, expr, ty,.. } => {
                if let Some(ty) = ty {
                    let ty = self.resolve_type(ty)?;
                    self.context.variable_id_type_map.insert(*id, ty);
                }
                self.bind_names_in_expr(expr)?;
            },
            StmtNode::Fun { id, generic_params, function,.. } => {
                self.bind_names_in_function(*id,function)?;
            },
            StmtNode::Expr { expr, .. } => {
                self.bind_names_in_expr(expr)?;
            },
            StmtNode::Impl { id, ty, methods } => {
                todo!("Bind impls")
            }
        }
        Ok(())
    }
    fn bind_names_in_stmts<'b:'a>(&mut self,stmts : &'b [StmtNode])->Result<(),ResolutionError>{
        for stmt in stmts{
            self.bind_names_in_stmt(stmt)?;
        }
        Ok(())
    }
    pub fn new()->Self{
        Self{
            constructor_map:HashMap::default(),
            field_map:HashMap::default(),
            scope_map:HashMap::default(),
            context:NameContext::default(),
            prev_scopes:Vec::new(),
            current_scope:Scope::default(),
            variant_map:Default::default()
        }
    }
    pub fn resolve<'b:'a>(mut self,stmts:&'b [StmtNode]) -> Result<(NameContext,Vec<ResolvedStmt>),ResolutionError>{
        self.find_names_in_stmts(stmts)?;
        self.bind_names_in_stmts(stmts)?;
        let stmts = self.resolve_stmts(stmts)?;
        Ok((self.context,stmts))
    }
    fn resolve_stmts(&mut self,stmts : &[StmtNode]) -> Result<Vec<ResolvedStmt>,ResolutionError>{
        let mut resolved_stmts = Vec::new();
        for stmt in stmts{
            if let Some(stmt) = self.resolve_stmt(stmt)?{
                resolved_stmts.push(stmt);
            }
        }
        Ok(resolved_stmts)
    }
}