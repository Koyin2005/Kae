use std::{collections::{HashMap, HashSet}, marker::PhantomData};

use fxhash::{FxHashMap, FxHashSet};

use crate::frontend::{parsing::ast::{ExprNode, ExprNodeKind, NodeId, ParsedAssignmentTargetKind, ParsedEnumVariant, ParsedFunction, ParsedPath, ParsedPatternNode, ParsedType, StmtNode}, typechecking::types::Type};

use super::{EnumInfo, FieldInfo, Fields, FuncIndex, FunctionInfo, FunctionParamInfo, IndexVec, IntoIndex, NameContext, StructIndex, StructInfo, VariantIndex, VariantInfo};

pub struct ResolutionError;
#[derive(Default)]
struct Scope{
    functions : FxHashMap<String,FuncIndex>,
    types : FxHashMap<String,Type>
}
pub struct Resolver<'a>{
    context : NameContext,
    prev_scopes : Vec<Scope>,
    current_scope : Scope,
    variant_map : FxHashMap<NodeId,&'a [ParsedEnumVariant]>,
    scope_map : FxHashMap<NodeId,Scope>

}
impl<'a> Resolver<'a>{
    fn begin_scope(&mut self){
        let old_scope = std::mem::replace(&mut self.current_scope, Scope::default());
        self.prev_scopes.push(old_scope);
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
    fn resolve_pattern(&mut self,pattern:&ParsedPatternNode) -> Result<(),ResolutionError>{
        Ok(())
    }
    fn resolve_expr(&mut self,expr:&ExprNode) -> Result<(),ResolutionError>{
        Ok(())
    }
    fn resolve_stmt(&mut self,stmt:&StmtNode) -> Result<(),ResolutionError>{
        match stmt{
            StmtNode::Expr { expr, has_semi } => {

            },
            StmtNode::Enum { name, generic_params, variants ,id} => {
                
            },
            StmtNode::Impl { ty, methods,id } => {

            },
            StmtNode::Struct { name, generic_params, fields,id } => {

            },
            StmtNode::Fun { name, generic_params, function,id } => {

            },
            StmtNode::Let { pattern, expr, ty,id } => {

            }
        }
        Ok(())
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
        let found_names_in_function = self.bind_names_in_expr(&function.body);
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
                self.bind_names_in_function(expr.id, function)
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
            StmtNode::Fun { id, name, generic_params, function } => {
                self.bind_names_in_function(*id, function)?;
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
            scope_map:HashMap::default(),
            context:NameContext::default(),
            prev_scopes:Vec::new(),
            current_scope:Scope::default(),
            variant_map:Default::default()
        }
    }
    pub fn resolve<'b:'a>(mut self,stmts:&'b [StmtNode]) -> Result<NameContext,ResolutionError>{
        self.find_names_in_stmts(stmts)?;
        self.bind_names_in_stmts(stmts)?;
        self.resolve_stmts(stmts)?;
        Ok(self.context)
    }
    fn resolve_stmts(&mut self,stmts : &[StmtNode]) -> Result<(),ResolutionError>{
        for stmt in stmts{
            self.resolve_stmt(stmt)?;
        }
        Ok(())
    }
}