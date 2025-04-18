use std::cell::Cell;

use fxhash::FxHashSet;

use crate::{
    data_structures::IndexVec, 
    frontend::{
        ast_lowering::hir::{Generics, VariantDef}, parsing::ast::{self, NodeId, ParsedType, Symbol}, 
        tokenizing::SourceLocation
    }
};

use super::{
    hir::{self, DefId, DefIdMap,FunctionDef, GenericArg, GenericOwner, Hir, HirId, Ident, Item, LiteralKind, PatternKind}, name_finding::{self, NameScopes, Record}, 
    resolve::Resolver, SymbolInterner
};
use crate::identifiers::ItemIndex;

pub struct LoweringErr;
pub struct PathLoweringErr;
pub struct AstLowerer<'a>{
    symbol_interner : &'a mut SymbolInterner,
    items : IndexVec<ItemIndex,Item>,
    name_info : name_finding::NamesFound,
    current_generic_stack : Vec<GenericOwner>,
    def_id_map : DefIdMap<ItemIndex>,
    next_id : HirId,
    had_error : Cell<bool>,
    resolver : Resolver
}

impl<'a> AstLowerer<'a>{
    pub fn new(interner:&'a mut SymbolInterner,name_info:name_finding::NamesFound,name_scopes:NameScopes,)->Self{
        Self {
            symbol_interner:interner,
            items:IndexVec::new(),
            name_info,
            current_generic_stack:Vec::new(),
            next_id : HirId::default(),
            def_id_map : DefIdMap::new(),
            had_error : false.into(),
            resolver :  {
                let mut resolver = Resolver::new(name_scopes.namespaces);
                resolver.push_scope(name_scopes.base_scope);
                resolver
            }
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
        let scope = self.name_info.scope_map.get_mut(&id).expect("There should be a scope for this id").take().expect("A scope should be here!");
        self.resolver.push_scope(scope);
    }
    fn end_scope(&mut self){
        self.resolver.pop_scope();
    }
    fn add_item_with_optional_def(&mut self,item:Item,def:Option<DefId>) -> ItemIndex{
        let item = self.items.push(item);
        if let Some(def) = def{
            self.def_id_map.insert(def, item);
        }
        item
    }
    fn add_item_with_def(&mut self,item:Item,def:DefId) -> ItemIndex{
        self.add_item_with_optional_def(item, Some(def))
    }
    fn intern_symbol(&self,symbol:ast::Symbol) -> hir::Ident{
        symbol.into()
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
    fn lower_generic_params(&mut self,owner:GenericOwner,generics:Option<ast::ParsedGenericParams>) -> (Generics,bool){
        let (generics,has_generics) = if let Some(ast::ParsedGenericParams(id,params)) = generics {
            self.begin_scope(id);
            let mut generics = Generics::new(); 
            let mut seen_names = FxHashSet::default();
            for (ast::ParsedGenericParam(_),&(id,name)) in params.into_iter().zip(&self.name_info.generics[&owner]){
                if !seen_names.insert(name.index){
                    self.error(format!("Repeated generic param '{}'.",self.symbol_interner.get(name.index)), name.span);
                    continue;
                }
                generics.params.push(hir::GenericParam(name,id));
            }
            (generics,true)
        }
        else{
            (Generics::new(),false)
        };
        self.current_generic_stack.push(owner);
        (generics,has_generics)
    }
    fn lower_path(&mut self,path:ast::Path) -> Result<hir::Path,LoweringErr>{
        let resolutions = self.resolver.resolve_path(path.segments.iter().map(|segment| segment.name.content));
        if resolutions.len() != path.segments.len(){
            let head = path.segments.first().expect("There must always be at least 1 segment");
            if resolutions.is_empty(){
                self.error(format!("Cannot find {} in scope.",self.symbol_interner.get(head.name.content)), head.location);
                return Err(LoweringErr);
            }
            let mut base_path = String::new();
            for (i,segment) in path.segments.iter().take(resolutions.len()).enumerate(){
                if i>0{
                    base_path += "::";
                }
                base_path += &self.symbol_interner.get(segment.name.content);
            }
            let last = path.segments[resolutions.len()].name;
            let span = last.location;
            self.error(format!("Cannot find {} in {}.",self.symbol_interner.get(last.content),base_path),span);
            return Err(LoweringErr);
        }
        let final_res = resolutions.last().copied().expect("There should be at least one!");
        let segments = resolutions.into_iter().zip(path.segments).map(|(resolution,segment)|{
            Ok(hir::PathSegment{
                res:resolution,
                ident:segment.name.into(),
                args:self.lower_generic_args(segment.generic_args)?
            })
        }).collect::<Vec<_>>().into_iter().collect::<Result<Vec<_>,_>>()?;
        Ok(hir::Path{span:path.location,final_res,segments})
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
                (hir::TypeKind::Path(self.lower_path(path)?),span)
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
            let (_,Ident { index:name, span:_ }) = self.name_info.variables[variable];
            self.resolver.current_scope_mut().add_binding(name, hir::Resolution::Variable(variable));
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
                let path:Result<hir::Path,LoweringErr> = self.lower_path(path);
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
            ast::ExprNodeKind::GetPath(path) => {
                hir::ExprKind::Path(self.lower_path(path)?)
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
                let Ok(path) = self.lower_path(path) else {
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
                        let span = name.location;
                        self.lower_path(name).map(|path| hir::Expr{
                            id:self.next_id(),
                            span,
                            kind:hir::ExprKind::Path(path)
                        })
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
    fn lower_fields(&mut self,fields:Vec<(Symbol,ParsedType)>,field_names:Vec<hir::Ident>)->Result<Vec<hir::FieldDef>,LoweringErr>{
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
                let (generics,has_generics) = self.lower_generic_params(GenericOwner::Struct(struct_index),struct_def.generic_params);
                let name = self.name_info.structs[struct_index].name;
                let fields = self.lower_fields(struct_def.fields, self.name_info.structs[struct_index].fields.clone());
                if has_generics { self.end_scope(); }
                let item_id = self.add_item_with_def(Item::Struct(hir::StructDef{
                    id:struct_index,
                    name,
                    generics,
                    fields:fields?
                }),struct_index);
                (hir::StmtKind::Item(item_id),name.span)
            },
            ast::StmtNode::Enum(enum_def) => {
                let name_finding::Item::Enum(enum_id) = self.name_info.items[&enum_def.id] else {
                    unreachable!("Should be an enum")
                };
                let (generics,has_generics) = self.lower_generic_params(GenericOwner::Enum(enum_id),enum_def.generic_params);
                let (name,ref variants) = self.name_info.enum_defs[enum_id];
                let variants : Vec<_> = variants.iter().map(|(variant_id,variant)|{
                    (*variant_id,Record{
                        name:variant.name,
                        fields:variant.fields.clone()
                    })
                }).collect();
                let variants = variants.iter().zip(enum_def.variants).map(|((variant_id,variant_info),variant)|{
                    let fields = variant_info.fields.clone();
                    self.lower_fields(variant.fields, fields).map(|fields|{
                        VariantDef { id:*variant_id,name:variant_info.name, fields }
                    })
                }).collect::<Vec<_>>();
                if has_generics{ self.end_scope();}
                (hir::StmtKind::Item(self.add_item_with_def(Item::Enum(hir::EnumDef{
                    id:enum_id,
                    generics,
                    name,
                    variants : variants.into_iter().collect::<Result<_,_>>()?
                }),enum_id)),name.span)
            },
            ast::StmtNode::Fun(function_def) => {
                let name_finding::Item::Function(func_index) = self.name_info.items[&function_def.id] else {
                    unreachable!("Should be a function")
                };
                let name = self.name_info.functions[func_index];
                let (generics,has_generics) = self.lower_generic_params(GenericOwner::Function(func_index),function_def.generic_params);
                let function = self.lower_function(function_def.id, function_def.function)?;
                if has_generics{ self.end_scope();}
                let span = SourceLocation::new(name.span.start_line, function.body.span.end_line);
                (hir::StmtKind::Item(self.add_item_with_def(Item::Function(FunctionDef { id : func_index, generics, name, function }),func_index)),span)
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
    pub fn lower(mut self,stmts:Vec<ast::StmtNode>) -> Result<Hir,LoweringErr>{
        let stmts = self.lower_stmts(stmts);
        if self.had_error.get(){
            return Err(LoweringErr);
        }
        Ok(Hir{items:self.items,stmts,defs_to_items:self.def_id_map})
    }
}