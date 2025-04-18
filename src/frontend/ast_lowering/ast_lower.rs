use std::cell::Cell;

use fxhash::FxHashSet;

use crate::{
    data_structures::{IndexVec, IntoIndex}, 
    frontend::{
        ast_lowering::hir::{Generics, VariantDef}, parsing::ast::{self, NodeId, ParsedType, Symbol}, 
        tokenizing::SourceLocation
    }, 
    identifiers::GenericParamIndex
};

use super::{
    hir::{self, FunctionDef, GenericArg, GenericOwner, HirId, Ident, Item, LiteralKind, PatternKind}, 
    name_finding::{self, Record, ResolutionResult, Scope}, 
    SymbolInterner
};
use crate::identifiers::{VariantIndex,ItemIndex,FieldIndex,ScopeIndex};

pub struct LoweringErr;
pub struct AstLowerer<'a>{
    symbol_interner : &'a mut SymbolInterner,
    items : IndexVec<ItemIndex,Item>,
    name_info : name_finding::NamesFound,
    current_scope : ScopeIndex,
    current_generic_stack : Vec<GenericOwner>,
    next_id : HirId,
    had_error : Cell<bool>
}

impl<'a> AstLowerer<'a>{
    pub fn new(interner:&'a mut SymbolInterner,name_info:name_finding::NamesFound)->Self{
        Self {
            symbol_interner:interner,
            items:IndexVec::new(),
            current_scope:ScopeIndex::new(0),
            name_info,
            current_generic_stack:Vec::new(),
            next_id : HirId::default(),
            had_error : false.into()
        }
    }
    fn next_id(&mut self) -> HirId{
        let prev_id = self.next_id;
        self.next_id = self.next_id.next();
        prev_id
    }
    fn error(&self,msg:String,span:SourceLocation){
        eprintln!("Error on Line {}: {}",span.start_line,msg);
        self.had_error.set(true);
    }
    fn begin_scope(&mut self,id:NodeId){
        let scope = self.name_info.scope_map[&id];
        self.current_scope = scope;
    }
    fn end_scope(&mut self){
        self.current_scope = self.name_info.all_scopes[self.current_scope].prev_scope.expect("Non global scopes must have prev_scope");
    }
    fn get_current_scope_mut(&mut self)->&mut name_finding::Scope{
        &mut self.name_info.all_scopes[self.current_scope]
    }
    fn get_current_scope(&self)->&name_finding::Scope{
        &self.name_info.all_scopes[self.current_scope]
    }
    fn add_item(&mut self,item:Item) -> ItemIndex{
        self.items.push(item)
    }
    fn intern_symbol(&mut self,symbol:ast::Symbol) -> hir::Ident{
        let symbol_index = self.symbol_interner.intern(symbol.content);
        let span = symbol.location;
        hir::Ident{
            index : symbol_index,
            span
        }
    }
    fn lower_generic_args(&mut self,args:Option<ast::ParsedGenericArgs>) -> Result<Vec<GenericArg>,LoweringErr>{
        if let Some(args)=  args{
            Ok(args.types.into_iter().map(|arg|{
                Ok(GenericArg{ ty: self.lower_type(arg)?})
            }).collect::<Result<Vec<_>,_>>()?)
        }
        else{
            Ok(Vec::new())
        }
    }
    fn get_last_generic_param(&self,name:hir::Ident) -> Option<(GenericOwner,GenericParamIndex)>{
        self.current_generic_stack.iter().rev().filter_map(|&generic_owner|{
            self.name_info.generics[&generic_owner].iter().enumerate().rev().find(|(_,param)|{
                param.index == name.index
            }).map(|(index,_)|{
                (generic_owner,GenericParamIndex::new(index as u32))
            })
        }).next()
    }
    fn resolve_base_path_def(&self,name:hir::Ident) -> Option<hir::PathDef>{
        Some(match self.symbol_interner.get(name.index){
            "int" => hir::PathDef::PrimitiveType(hir::PrimitiveType::Int),
            "float" => hir::PathDef::PrimitiveType(hir::PrimitiveType::Float),
            "string" => hir::PathDef::PrimitiveType(hir::PrimitiveType::String),
            "bool" => hir::PathDef::PrimitiveType(hir::PrimitiveType::Bool),
            "never" => hir::PathDef::PrimitiveType(hir::PrimitiveType::Never),
            _ => match self.get_current_scope().get_type(name.index, &self.name_info.all_scopes){
                ResolutionResult::Type(ty) => match ty{
                    name_finding::Type::Enum(enum_index) => hir::PathDef::Enum(enum_index),
                    name_finding::Type::PrimitiveType(primitive_ty) => hir::PathDef::PrimitiveType(primitive_ty),
                    name_finding::Type::Struct(struct_index) => hir::PathDef::Struct(struct_index),
                },
                ResolutionResult::None => match self.get_last_generic_param(name) {
                    Some((_,index)) => {
                       hir::PathDef::GenericParam(index, name.index)
                    },
                    None => return None
                }
                _ => return None
            }
        })

    }
    fn resolve_path_def(&self,name:hir::Ident,prev_def:Option<hir::PathDef>,namespace:hir::Namespace)->Option<hir::PathDef>{
        if let Some(prev) = prev_def{
            match &prev{
                &hir::PathDef::Enum(enum_index) => {
                    let (_,_,ref variant_names) = self.name_info.enum_defs[enum_index];
                    if let Some(&variant) = variant_names.get(&name.index){
                        return Some(hir::PathDef::Variant(enum_index, variant))
                        
                    }
                    None
                },
                _ => None
            }
        }
        else if namespace == hir::Namespace::Value{
            let def = match Scope::get_value(self.current_scope,name.index, &self.name_info.all_scopes){
                ResolutionResult::Function(function) => {
                    hir::PathDef::Function(function)
                },
                ResolutionResult::Variable(variable,kind) => {
                    if kind == name_finding::VariableUse::Upvar{
                        self.error(format!("Cannot use variable '{}' from inner function.",self.symbol_interner.get(self.name_info.variables[variable].2.index)), name.span);
                    }
                    hir::PathDef::Variable(variable)
                },
                ResolutionResult::Type(_)|ResolutionResult::None => return None
            };
            Some(def)
        }
        else if namespace == hir::Namespace::Type {
            self.resolve_base_path_def(name)
        }
        else{
            None
        }
    }
    fn resolve_path(&mut self,path:ast::ParsedPath,namespace:hir::Namespace)->Option<hir::Path>{
        let name = self.intern_symbol(path.head.name);
        let mut span = name.span;
        let base_generic_args = self.lower_generic_args(path.head.generic_args).ok()?;
        let base_path_def = if !path.segments.is_empty(){
            self.resolve_base_path_def(name)
        }
        else{
            self.resolve_path_def(name, None, namespace)
        };
        let Some(mut def) = base_path_def else {
            self.error(format!("Unknown identifier '{}'.",self.symbol_interner.get(name.index)), name.span);
            return None;
        };
        let base_path_def = def;
        let segments = path.segments.into_iter().map(|segment|{
            let name = self.intern_symbol(segment.name);
            let generic_args = self.lower_generic_args(segment.generic_args).ok()?;
            let Some(next_def) = self.resolve_path_def(name, Some(def),namespace) else {
                self.error(format!("Unknown variant, or method '{}'.",self.symbol_interner.get(name.index)), name.span);
                return None;
            };
            span.end_line = name.span.end_line;
            def = next_def;
            Some(hir::PathSegment{
               def:next_def,
               ident:name,
               args:generic_args
            })
        }).collect::<Vec<_>>();
        let segments = {
            let mut new_segments = vec![hir::PathSegment{
                def:base_path_def,
                ident:name,
                args:base_generic_args
            }];
            new_segments.extend(segments.into_iter().collect::<Option<Vec<_>>>()?);
            new_segments
        };
        Some(hir::Path{
            span,
            def,
            segments
        })
    }
    fn lower_generic_params(&mut self,owner:GenericOwner,generics:Option<ast::ParsedGenericParams>) -> Generics{
        let generics = if let Some(ast::ParsedGenericParams(params)) = generics {
            let mut generics = Generics::new(); 
            let mut seen_names = FxHashSet::default();
            for ast::ParsedGenericParam(param) in params{
                let name = self.intern_symbol(param);
                if !seen_names.insert(name.index){
                    self.error(format!("Repeated generic param '{}'.",self.symbol_interner.get(name.index)), name.span);
                    continue;
                }
                generics.params.push(hir::GenericParam(name));
            }
            generics
        }
        else{
            Generics::new()
        };
        self.current_generic_stack.push(owner);
        generics
    }
    fn lower_type(&mut self,ty:ast::ParsedType) -> Result<hir::Type,LoweringErr>{
        let (kind,span) = match ty{
            ast::ParsedType::Array(span,element) => { 
                let element_ty = self.lower_type(*element);
                (hir::TypeKind::Array(Box::new(element_ty?)),span)
            },
            ast::ParsedType::Tuple(span,elements) => {
                let element_types = elements.into_iter().map(|element| self.lower_type(element)).collect::<Vec<_>>();
                (hir::TypeKind::Tuple(element_types.into_iter().collect::<Result<_,_>>()?),span)
            },
            ast::ParsedType::Fun(span, params, return_type) => {
                let param_types = params.into_iter().map(|param| self.lower_type(param)).collect::<Vec<_>>();
                let return_type = return_type.map(|return_type|self.lower_type(*return_type).map(Box::new)).map_or(Ok(None),|result| result.map(Some))?;
                (hir::TypeKind::Function(param_types.into_iter().collect::<Result<_,_>>()?, return_type),span)
            },
            ast::ParsedType::Path(path) => {
                let span = path.location;
                (hir::TypeKind::Path(self.resolve_path(path,hir::Namespace::Type).ok_or(LoweringErr)?),span)
            }
        };
        Ok(hir::Type{
            kind,
            span
        })
    }
    fn lower_function(&mut self,id:NodeId,function:ast::ParsedFunction) -> Result<hir::Function,LoweringErr>{
        self.begin_scope(id);
        let params =  (||{
            let params : Vec<_> = function.params.into_iter().map(|param|{
                let pattern = self.define_bindings_and_lower_pattern(param.pattern);
                (pattern,self.lower_type(param.ty))
            }).collect();
            params.into_iter().map(|(pattern,ty)|{
                let pattern = pattern?;
                let ty = ty?;
                Ok(hir::Param{
                    pattern,
                    ty
                })
            }).collect::<Result<Vec<_>,_>>()
        })();
        let return_type =  function.return_type.map(|ty| self.lower_type(ty)).map_or(Ok(None), |ty| ty.map(Some));
        let body = self.lower_expr(function.body);
        self.end_scope();
        Ok(hir::Function{
            params:params?,
            return_type:return_type?,
            body:body?
        })

    }
    fn define_bindings_and_lower_pattern(&mut self,pattern:ast::ParsedPatternNode) -> Result<hir::Pattern,LoweringErr>{
        let variables = self.name_info.variable_def_map[&pattern.id].clone();
        for variable in variables{
            let (_,_,Ident { index:name, span:_ }) = self.name_info.variables[variable];
            self.get_current_scope_mut().define_variable(name, variable);
        }
        self.lower_pattern(pattern)
    }
    fn lower_pattern(&mut self,pattern:ast::ParsedPatternNode) -> Result<hir::Pattern,LoweringErr>{
        let span = pattern.location;
        let (kind,span) = match pattern.kind{
            ast::ParsedPatternNodeKind::Is(name,matched_pattern ) => {
                let name = self.intern_symbol(name);
                let matched_pattern = self.lower_pattern(*matched_pattern);
                let id = *self.name_info.variable_defs.get(&pattern.id).expect("All bindings should be defined before lowered");
                (PatternKind::Binding(id,name, Some(Box::new(matched_pattern?))),span)
            },
            ast::ParsedPatternNodeKind::Literal(literal) => {
                let literal = match literal{
                    ast::LiteralKind::Bool(bool) => LiteralKind::Bool(bool),
                    ast::LiteralKind::Float(float) => LiteralKind::Float(float),
                    ast::LiteralKind::Int(int) => LiteralKind::Int(int),
                    ast::LiteralKind::String(string) => LiteralKind::String(self.symbol_interner.intern(string))
                };

                (PatternKind::Literal(literal),span)
            },
            ast::ParsedPatternNodeKind::Name(name) => {
                let name = self.intern_symbol(Symbol { content: name, location: span });
                let id = *self.name_info.variable_defs.get(&pattern.id).expect("All bindings should be defined before lowered");
                (PatternKind::Binding(id,name, None),span)
            },
            ast::ParsedPatternNodeKind::Tuple(elements) => {
                let elements:Vec<_> = elements.into_iter().map(|element|{
                    self.lower_pattern(element)
                }).collect();
                (PatternKind::Tuple(elements.into_iter().collect::<Result<Vec<_>,_>>()?),span)
            },
            ast::ParsedPatternNodeKind::Struct { path, fields } => {
                let path = self.resolve_path(path,hir::Namespace::Type).ok_or(LoweringErr);
                let fields:Vec<_> = fields.into_iter().filter_map(|(symbol,pattern)|{
                    let field_symbol = self.intern_symbol(symbol);
                    let pattern = self.lower_pattern(pattern);
                    Some(pattern.map(|pattern|{
                        hir::FieldPattern { name: field_symbol, pattern }
                    }))
                }).collect();
                (PatternKind::Struct(path?, fields.into_iter().collect::<Result<Vec<_>,_>>()?),span)
            }
            ast::ParsedPatternNodeKind::Wildcard => (PatternKind::Wildcard,span)
        };
        Ok(hir::Pattern{
            id : self.next_id(),
            kind,
            span
        })
    }
    fn lower_expr(&mut self,expr:ast::ExprNode) -> Result<hir::Expr,LoweringErr>{
        let span = expr.location;
        let kind = match expr.kind{
            ast::ExprNodeKind::Literal(literal) => hir::ExprKind::Literal(match literal{
                ast::LiteralKind::Bool(value) => LiteralKind::Bool(value),
                ast::LiteralKind::Int(value) => LiteralKind::Int(value),
                ast::LiteralKind::Float(value) => LiteralKind::Float(value),
                ast::LiteralKind::String(value) => LiteralKind::String(self.symbol_interner.intern(value))
            }),
            ast::ExprNodeKind::Grouping(expr) => self.lower_expr(*expr)?.kind,
            ast::ExprNodeKind::Tuple(elements) => hir::ExprKind::Tuple(
                elements.into_iter().map(|element|{
                    self.lower_expr(element)
                }).collect::<Vec<_>>().into_iter().collect::<Result<Vec<_>,_>>()?
            ),
            ast::ExprNodeKind::Array(elements) => hir::ExprKind::Array(
                elements.into_iter().map(|element|{
                    self.lower_expr(element)
                }).collect::<Vec<_>>().into_iter().collect::<Result<Vec<_>,_>>()?
            ),
            ast::ExprNodeKind::Unary { op, operand } => hir::ExprKind::Unary(
                match op{
                    ast::ParsedUnaryOp::Negate => hir::UnaryOp::Negate,
                }, 
                Box::new(self.lower_expr(*operand)?)
            ),
            ast::ExprNodeKind::BinaryOp { op, left, right } => {
                let left = self.lower_expr(*left);
                let right = self.lower_expr(*right);
                hir::ExprKind::Binary(
                    match op{
                        ast::ParsedBinaryOp::Add => hir::BinaryOp::Add,
                        ast::ParsedBinaryOp::Subtract => hir::BinaryOp::Subtract,
                        ast::ParsedBinaryOp::Multiply => hir::BinaryOp::Multiply,
                        ast::ParsedBinaryOp::Divide => hir::BinaryOp::Divide,
                        ast::ParsedBinaryOp::Equals => hir::BinaryOp::Equals,
                        ast::ParsedBinaryOp::Greater => hir::BinaryOp::Greater,
                        ast::ParsedBinaryOp::GreaterEquals => hir::BinaryOp::GreaterEquals,
                        ast::ParsedBinaryOp::Lesser => hir::BinaryOp::Lesser,
                        ast::ParsedBinaryOp::LesserEquals => hir::BinaryOp::LesserEquals,
                        ast::ParsedBinaryOp::NotEquals => hir::BinaryOp::NotEquals
                    }, 
                    Box::new(left?), 
                    Box::new(right?)
                )
            },
            ast::ExprNodeKind::Call { callee, args } => {
                let callee = self.lower_expr(*callee);
                hir::ExprKind::Call(
                    Box::new(callee?),
                    args.into_iter().map(|arg| self.lower_expr(arg)).collect::<Vec<_>>().into_iter().collect::<Result<Vec<_>,_>>()?
                )
            },
            ast::ExprNodeKind::While { condition, body } => {
                let condition = self.lower_expr(*condition);
                let body = self.lower_expr(*body);
                hir::ExprKind::While(Box::new(condition?), Box::new(body?))
            },
            ast::ExprNodeKind::If { condition, then_branch, else_branch } => {
                let condition = self.lower_expr(*condition);
                let then_branch = self.lower_expr(*then_branch);
                hir::ExprKind::If(
                    Box::new(condition?),
                    Box::new(then_branch?),
                    else_branch.map(|else_branch| self.lower_expr(*else_branch).map(Box::new)).map_or(Ok(None),|result| result.map(Some))?
                )
            },
            ast::ExprNodeKind::Match { matchee, arms } => {
                let matchee = self.lower_expr(*matchee);
                let arms = arms.into_iter().map(|arm|{
                    self.begin_scope(arm.id);
                    let pat = self.define_bindings_and_lower_pattern(arm.pattern);
                    let body = self.lower_expr(arm.expr);
                    self.end_scope();
                    Ok(hir::MatchArm{
                        pat:pat?,
                        body:body?
                    })
                }).collect::<Vec<_>>();
                hir::ExprKind::Match(Box::new(matchee?),arms.into_iter().collect::<Result<Vec<_>,_>>()? )
            },
            ast::ExprNodeKind::Block { stmts, expr:result_expr } => {
                self.begin_scope(expr.id);
                let stmts = self.lower_stmts(stmts);
                let expr = result_expr.map(|expr| self.lower_expr(*expr).map(Box::new)).map_or(Ok(None), |result| result.map(Some));
                self.end_scope();
                hir::ExprKind::Block(stmts, expr?)
            },
            ast::ExprNodeKind::Function(function) => hir::ExprKind::Function(Box::new(self.lower_function(expr.id,*function)?)),
            ast::ExprNodeKind::Print(args) => hir::ExprKind::Print(args.into_iter().map(|arg| self.lower_expr(arg)).collect::<Vec<_>>().into_iter().collect::<Result<Vec<_>,_>>()?),
            ast::ExprNodeKind::Get(name) => {
                let interned_name = self.symbol_interner.intern_symbol(Symbol { content: name, location: expr.location });
                match self.resolve_path_def(interned_name, None,hir::Namespace::Value) {
                    Some(def) => {
                        hir::ExprKind::Path(hir::Path { 
                            span:interned_name.span,def, 
                            segments: vec![hir::PathSegment{
                                def,
                                ident:interned_name,
                                args:Vec::new()
                            }],
                        })
                    },
                    None => {
                        self.error(format!("Undefined variable, or function '{}'.",self.symbol_interner.get(interned_name.index)), span);
                        return Err(LoweringErr);
                    }
                }
            },
            ast::ExprNodeKind::GetPath(path) => {
                hir::ExprKind::Path(self.resolve_path(path, hir::Namespace::Value).ok_or(LoweringErr)?)
            },
            ast::ExprNodeKind::Logical { op, left, right } => {
                let left = self.lower_expr(*left);
                let right = self.lower_expr(*right)?;
                hir::ExprKind::Logical(
                    match op{
                        ast::ParsedLogicalOp::And => hir::LogicalOp::And,
                        ast::ParsedLogicalOp::Or => hir::LogicalOp::Or
                    },
                    Box::new(left?),
                    Box::new(right)
                )
            },
            ast::ExprNodeKind::TypenameOf(ty) => hir::ExprKind::Typename(self.next_id(),self.lower_type(ty)?),
            ast::ExprNodeKind::Property(expr, field) => hir::ExprKind::Field(Box::new(self.lower_expr(*expr)?), self.intern_symbol(field)),
            ast::ExprNodeKind::Return(expr) => hir::ExprKind::Return(expr.map(|expr| self.lower_expr(*expr).map(Box::new)).map_or(Ok(None), |result| result.map(Some))?),
            ast::ExprNodeKind::StructInit { path, fields } => {
                let Some(path) = self.resolve_path(path, hir::Namespace::Type) else {
                    return Err(LoweringErr);
                };
                let fields = fields.into_iter().map(|(field_name,field_expr)|{
                    let field_name = self.intern_symbol(field_name);
                    let field_expr = self.lower_expr(field_expr);
                    field_expr.map(|expr| hir::FieldExpr{span:SourceLocation::new(field_name.span.start_line, expr.span.end_line),field:field_name,expr})
                }).collect::<Vec<_>>().into_iter().collect::<Result<Vec<hir::FieldExpr>,_>>()?;
                hir::ExprKind::StructLiteral(path, fields)
            },
            ast::ExprNodeKind::Assign { lhs, rhs } => {
                let lhs = match lhs.kind{
                    ast::ParsedAssignmentTargetKind::Name(name) => {
                        let interned_name = self.symbol_interner.intern_symbol(Symbol { content: name, location: expr.location });
                        match self.resolve_path_def(interned_name, None,hir::Namespace::Value) {
                            Some(def) => {
                                Ok(hir::Expr{
                                    id : self.next_id(),
                                    kind : hir::ExprKind::Path(hir::Path { 
                                        span:interned_name.span,def, 
                                        segments: vec![hir::PathSegment{
                                            def,
                                            ident:interned_name,
                                            args:Vec::new()
                                        }],
                                    }),
                                    span : interned_name.span
                                })
                            },
                            None => {
                                self.error(format!("Undefined variable, or function '{}'.",self.symbol_interner.get(interned_name.index)), span);
                                return Err(LoweringErr);
                            }
                        }
                    },
                    ast::ParsedAssignmentTargetKind::Index { lhs:indexed, rhs:index } => {
                        let indexed = self.lower_expr(*indexed).map(Box::new);
                        let index = self.lower_expr(*index).map(Box::new);
                        match (indexed,index) {
                            (Ok(indexed),Ok(index)) => Ok(hir::Expr{
                                id:self.next_id(),
                                kind:hir::ExprKind::Index(indexed, index),
                                span:lhs.location
                            }),
                            _ => Err(LoweringErr)
                        }
                    },
                    ast::ParsedAssignmentTargetKind::Field { lhs:receiver, field } => {
                        let receiver = self.lower_expr(*receiver);
                        receiver.map(|receiver|{
                            hir::Expr{
                                id : self.next_id(),
                                kind:hir::ExprKind::Field(Box::new(receiver), self.intern_symbol(field)),
                                span:lhs.location
                            }
                        })
                    }
                };
                let rhs = self.lower_expr(*rhs);
                match (lhs.map(Box::new),rhs.map(Box::new)) {
                    (Ok(lhs),Ok(rhs)) => hir::ExprKind::Assign(lhs, rhs),
                    _ => return Err(LoweringErr)
                }
            },
            ast::ExprNodeKind::Index { lhs, rhs } => {
                let lhs = self.lower_expr(*lhs).map(Box::new);
                let rhs = self.lower_expr(*rhs).map(Box::new);
                match (lhs,rhs) {
                    (Ok(lhs),Ok(rhs)) => hir::ExprKind::Index(lhs, rhs),
                    _ => return Err(LoweringErr)
                }
            },
            ast::ExprNodeKind::MethodCall { receiver, method:_method, args } => {
                let _receiver = self.lower_expr(*receiver).map(Box::new);
                let _args = args.into_iter().map(|arg| self.lower_expr(arg)).collect::<Vec<_>>().into_iter().collect::<Result<Vec<_>,_>>();
                todo!("Method calls")
            }
        };
        Ok(hir::Expr { id:self.next_id(), span, kind})
    }
    fn lower_fields(&mut self,fields:Vec<(Symbol,ParsedType)>,field_names:IndexVec<FieldIndex,hir::Ident>)->Result<IndexVec<FieldIndex,hir::FieldDef>,LoweringErr>{
        let fields = field_names.into_iter().zip(fields.into_iter()).map(|(field,(_,field_ty))|{
            let field_ty = self.lower_type(field_ty);
            field_ty.map(|field_ty| hir::FieldDef{
                name : field,
                ty : field_ty
            })
        }).collect();
        fields
    }
    fn lower_stmt(&mut self,stmt:ast::StmtNode) -> Result<hir::Stmt,LoweringErr>{
        let (kind,span) = match stmt{
            ast::StmtNode::Expr { expr, has_semi } => {
                let span = expr.location;
                let lowered_expr = self.lower_expr(expr)?;
                let kind = if has_semi {
                    hir::StmtKind::Semi(lowered_expr)
                }
                else{
                    hir::StmtKind::Expr(lowered_expr)
                };
                (kind,span)
            },
            ast::StmtNode::Let { id:_, pattern, expr, ty } => {
                let span = SourceLocation::new(pattern.location.start_line, expr.location.end_line);
                let ty = ty.map(|ty| self.lower_type(ty));
                let expr = self.lower_expr(expr);
                let pattern = self.define_bindings_and_lower_pattern(pattern);
                (hir::StmtKind::Let(pattern?, ty.map_or(Ok(None), |ty| ty.map(Some))?, expr?),span)
            },
            ast::StmtNode::Struct(struct_def) => {
                let name_finding::Item::Struct(struct_index) = self.name_info.items[&struct_def.id] else {
                    unreachable!("Should be a struct")
                };
                let generics = self.lower_generic_params(GenericOwner::Struct(struct_index),struct_def.generic_params);
                let name = self.name_info.structs[struct_index].name;
                let fields = self.lower_fields(struct_def.fields, self.name_info.structs[struct_index].fields.clone())?;
                (hir::StmtKind::Item(self.add_item(Item::Struct(generics,VariantDef { name, fields }))),name.span)
            },
            ast::StmtNode::Enum(enum_def) => {
                let name_finding::Item::Enum(enum_index) = self.name_info.items[&enum_def.id] else {
                    unreachable!("Should be an enum")
                };
                let generics = self.lower_generic_params(GenericOwner::Enum(enum_index),enum_def.generic_params);
                let (name,ref variants,_) = self.name_info.enum_defs[enum_index];
                let variants : Vec<_> = variants.iter().map(|variant|{
                    Record{
                        name:variant.name,
                        fields:variant.fields.clone()
                    }
                }).collect();
                let variants = variants.iter().zip(enum_def.variants).map(|(variant_info,variant)|{
                    let fields = variant_info.fields.clone();
                    self.lower_fields(variant.fields, fields).map(|fields|{
                        VariantDef { name:variant_info.name, fields }
                    })
                }).collect::<IndexVec<VariantIndex,_>>();
                (hir::StmtKind::Item(self.add_item(Item::Enum(generics,name,variants.into_iter().collect::<Result<IndexVec<_,_>,_>>()?))),name.span)
            },
            ast::StmtNode::Fun(function_def) => {
                let name_finding::Item::Function(func_index) = self.name_info.items[&function_def.id] else {
                    unreachable!("Should be a function")
                };
                let name = self.name_info.functions[func_index];
                let generics = self.lower_generic_params(GenericOwner::Function(func_index),function_def.generic_params);
                let function = self.lower_function(function_def.id, function_def.function)?;
                let span = SourceLocation::new(name.span.start_line, function.body.span.end_line);
                (hir::StmtKind::Item(self.add_item(Item::Function(FunctionDef { generics, name, function }))),span)
            },
            ast::StmtNode::Impl(_impl) => todo!("Impls")
        };
        Ok(hir::Stmt{
            kind,
            span 
        })
    }
    fn lower_stmts(&mut self,stmts:Vec<ast::StmtNode>) -> Vec<hir::Stmt>{
        let mut lowered_stmts = Vec::with_capacity(stmts.capacity());
        for stmt in stmts{
            if let Ok(stmt) = self.lower_stmt(stmt){
                lowered_stmts.push(stmt);
            }
        }
        lowered_stmts
    }
    pub fn lower(mut self,stmts:Vec<ast::StmtNode>) -> Result<(IndexVec<ItemIndex,Item>,Vec<hir::Stmt>),LoweringErr>{
        let stmts = self.lower_stmts(stmts);
        if self.had_error.get(){
            return Err(LoweringErr);
        }
        Ok((self.items,stmts))
    }
}