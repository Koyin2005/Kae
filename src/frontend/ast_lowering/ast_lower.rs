use std::cell::{Cell, RefCell};

use fxhash::FxHashSet;

use crate::{
    data_structures::IndexVec, errors::ErrorReporter, frontend::{
        ast_lowering::hir::{Generics, VariantDef}, parsing::ast::{self, InferPathKind, NodeId, ParsedType, Symbol}, 
        tokenizing::SourceLocation
    }, identifiers::BodyIndex
};

use super::{
    hir::{self, DefId, DefIdMap, DefKind, Expr, FunctionDef, GenericArg, Hir, HirId, Ident, Item, LiteralKind, PatternKind, Resolution, Type}, name_finding::{self, NameScopes, Record}, resolve::Resolver, scope::{ScopeId, ScopeKind}, SymbolInterner
};
use crate::identifiers::ItemIndex;

pub struct LoweringErr;
pub struct PathLoweringErr;
pub struct AstLowerer<'a>{
    symbol_interner : &'a mut SymbolInterner,
    items : IndexVec<ItemIndex,Item>,
    name_info : name_finding::NamesFound,
    def_id_map : DefIdMap<ItemIndex>,
    next_id : Cell<HirId>,
    error_reporter: ErrorReporter,
    prev_scopes : RefCell<Vec<ScopeId>>,
    bodies : IndexVec<BodyIndex,Expr>,
    resolver : RefCell<Resolver>
}

impl<'a> AstLowerer<'a>{
    pub fn new(interner:&'a mut SymbolInterner,name_info:name_finding::NamesFound,name_scopes:NameScopes)->Self{
        Self {
            symbol_interner:interner,
            items:IndexVec::new(),
            name_info,
            next_id : Cell::new(HirId::default()),
            def_id_map : DefIdMap::new(),
            resolver :  RefCell::new(Resolver::new(name_scopes.namespaces,name_scopes.scope_tree)),
            prev_scopes : RefCell::new(Vec::new()),
            error_reporter: ErrorReporter::new(false),
            bodies : IndexVec::new()
        }
    }
    fn next_id(&self) -> HirId{
        let prev_id = self.next_id.get();
        self.next_id.set(prev_id.next());
        prev_id
    }
    fn expect_def_id(&self,id:NodeId,msg:&str) -> DefId{
        self.name_info.expect_def_id_with_message(id, msg)
    }
    fn error(&self,msg:String,span:SourceLocation){
        self.error_reporter.emit(msg, span);
    }
    fn begin_scope(&mut self,id:NodeId){
        self.prev_scopes.borrow_mut().push(self.resolver.borrow().current_scope_id());
        let scopes = self.name_info.scope_map.get_mut(&id).expect("There should be a scope for this id");
        self.resolver.borrow_mut().set_current_scope(scopes.pop().expect("There should be a scope here"));
    }
    fn end_scope(&self){
        let prev_scope = self.prev_scopes.borrow_mut().pop().expect("There should be a scope here.");
        self.resolver.borrow_mut().set_current_scope(prev_scope);
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
    fn lower_generic_args(&self,args:Option<&ast::ParsedGenericArgs>) -> Result<Vec<GenericArg>,LoweringErr>{
        if let Some(args)=  args{
            Ok(args.types.iter().map(|arg|{
                Ok(GenericArg{ ty: self.lower_type(arg)?})
            }).collect::<Result<Vec<_>,_>>()?)
        }
        else{
            Ok(Vec::new())
        }
    }
    fn lower_generic_params(&mut self,owner:DefId,generics:Option<ast::ParsedGenericParams>) -> Result<Generics,LoweringErr>{
        let mut had_error = false;
        let generics = if let Some(ast::ParsedGenericParams(_,params)) = generics {
            let mut generics = Generics::new(); 
            let mut seen_names = FxHashSet::default();
            for (ast::ParsedGenericParam(_),&(id,name)) in params.into_iter().zip(&self.name_info.generics[owner]){
                if !seen_names.insert(name.index){
                    self.error(format!("Repeated generic param '{}'.",self.symbol_interner.get(name.index)), name.span);
                    had_error = true;
                    continue;
                }
                generics.params.push(hir::GenericParam(name,id));
            }
            generics
        }
        else{
            Generics::new()
        };
        (!had_error).then_some(generics).ok_or(LoweringErr)
    }
    fn validate_path(&self,resolution:Resolution, name: Symbol) -> bool{
        let mut had_error = false;
        match resolution {
            Resolution::Definition(DefKind::Param,_) => {
                let mut scope = self.resolver.borrow().current_scope_id();
                let resolver = self.resolver.borrow();
                let scopes = resolver.scopes();
                let mut found_item = false;
                while let Some(parent) = scopes.get_parent(scope) {
                    match scopes.get_scope(scope).kind(){
                        ScopeKind::Item(_) => {
                            if found_item{
                                if let Some((name_index,_)) =  scopes.get_scope(scope).bindings_iter().find(|(_,res)| *res == resolution){
                                    self.error(format!("Cannot use generic parameter '{}' from outer item.",self.symbol_interner.get(name_index)), name.location);
                                    had_error = true;
                                    break;
                                    }
                            }
                            found_item = true;
                        },
                        _ => ()
                    }
                    scope = parent;
                }
                
            },
            _ => ()
        }
        !had_error
    }
    fn lower_path(&self,path:&ast::Path) -> Result<hir::QualifiedPath,LoweringErr>{
        let resolutions = self.resolver.borrow().resolve_path(path.segments.iter().map(|segment| segment.name.content));
        if resolutions.is_empty(){
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
        let resolution_len = resolutions.len();
        let final_res = resolutions.last().copied().expect("There should be at least one!");
        self.validate_path(final_res, path.segments.last().expect("There should be at least one segment").name);
        let segments = resolutions.into_iter().zip(&path.segments).map(|(resolution,segment)|{
            Ok(hir::PathSegment{
                res:resolution,
                ident:segment.name.into(),
                args:self.lower_generic_args(segment.generic_args.as_ref())?
            })
        }).collect::<Vec<_>>().into_iter().collect::<Result<Vec<_>,_>>()?;
        let full_path = hir::QualifiedPath::FullyResolved(hir::Path{span:path.location,final_res,segments});
        /*Number of path segments is always greater or equal to the number of resolutions along a path*/
        let unresolved_segments = path.segments.len() - resolution_len;
        if unresolved_segments == 0{
            return Ok(full_path);
        }
        let (Resolution::Primitive(_) | Resolution::SelfType(_) | Resolution::Definition(hir::DefKind::Enum|hir::DefKind::Struct,_)) = final_res else {
            let mut base_path = String::new();
            for (i,segment) in path.segments.iter().take(resolution_len).enumerate(){
                if i>0{
                    base_path += "::";
                }
                base_path += &self.symbol_interner.get(segment.name.content);
            }
            let last = path.segments[resolution_len].name;
            let span = last.location;
            self.error(format!("Cannot find {} in {}.",self.symbol_interner.get(last.content),base_path),span);
            return Err(LoweringErr);
        };
        let mut full_path = full_path;
        for offset in 0..unresolved_segments{
            let i = resolution_len + offset;
            let segment = &path.segments[i];
            full_path = hir::QualifiedPath::TypeRelative(Box::new(Type {span: full_path.span() , kind: hir::TypeKind::Path(full_path) }),hir::PathSegment{
                res : Resolution::None,
                ident : segment.name.into(),
                args : self.lower_generic_args(segment.generic_args.as_ref())?
            });
        }
        Ok(full_path)
        
    }
    fn lower_type(&self,ty:&ast::ParsedType) -> Result<hir::Type,LoweringErr>{
        let (kind,span) = match ty{
            &ast::ParsedType::Array(span,ref element) => { 
                let element_ty = self.lower_type(element);
                (hir::TypeKind::Array(Box::new(element_ty?)),span)
            },
            &ast::ParsedType::Tuple(span,ref elements) => {
                let element_types = elements.iter().map(|element| self.lower_type(element)).collect::<Vec<_>>();
                (hir::TypeKind::Tuple(element_types.into_iter().collect::<Result<_,_>>()?),span)
            },
            &ast::ParsedType::Fun(span, ref params, ref return_type) => {
                let param_types = params.into_iter().map(|param| self.lower_type(param)).collect::<Vec<_>>();
                let return_type = return_type.as_ref().map(|return_type|self.lower_type(return_type).map(Box::new)).map_or(Ok(None),|result| result.map(Some))?;
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
    fn lower_function_sig(&mut self,sig:ast::FunctionSig) -> Result<(Vec<hir::Param>,Option<hir::Type>),LoweringErr>{
        
        let params =  (||{
            let params : Vec<_> = sig.params.into_iter().map(|param|{
                let pattern = self.define_bindings_and_lower_pattern(param.pattern);
                (pattern,self.lower_type(&param.ty))
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

        let return_type = sig.return_type.map(|return_type| self.lower_type(&return_type)).transpose();
        params.and_then(|params| return_type.map(|return_type| (params,return_type)))
    }
    fn lower_function(&mut self,id:NodeId,sig:ast::FunctionSig,body:ast::ExprNode) -> Result<hir::Function,LoweringErr>{
        self.begin_scope(id);
        let params_and_return_type = self.lower_function_sig(sig);
        let body = self.lower_expr(body);
        self.end_scope();

        let (params,return_type) = params_and_return_type?;
        Ok(hir::Function{
            params:params,
            return_type:return_type,
            body:self.bodies.push(body?)
        })

    }
    fn define_bindings_and_lower_pattern(&mut self,pattern:ast::ParsedPatternNode) -> Result<hir::Pattern,LoweringErr>{
        let variables = self.name_info.variable_def_map[&pattern.id].clone();
        for variable in variables{
            let (_,Ident { index:name, span:_ }) = self.name_info.variables[variable];
            self.resolver.borrow_mut().current_scope_mut().add_binding(name, hir::Resolution::Variable(variable));
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
            ast::ParsedPatternNodeKind::Path(path) => {
                let path = self.lower_path(&path);
                (PatternKind::Struct(hir::InferOrPath::Path(path?), vec![]),span)
            },
            ast::ParsedPatternNodeKind::Tuple(elements) => {
                let elements:Vec<_> = elements.into_iter().map(|element|{
                    self.lower_pattern(element)
                }).collect();
                (PatternKind::Tuple(elements.into_iter().collect::<Result<Vec<_>,_>>()?),span)
            },
            ast::ParsedPatternNodeKind::Struct { path, fields } => {
                let path:Result<hir::InferOrPath,LoweringErr> = match path.infer_path{
                    ast::InferPathKind::Infer(symbol) => {
                        Ok(hir::InferOrPath::Infer(pattern.location,symbol.map(|symbol|{self.intern_symbol(symbol)})))
                    },
                    ast::InferPathKind::Path(path) => {
                        self.lower_path(&path).map(|path| hir::InferOrPath::Path(path))
                    }
                };
                let fields:Vec<_> = fields.into_iter().filter_map(|(symbol,pattern)|{
                    let field_symbol = self.intern_symbol(symbol);
                    let pattern = self.lower_pattern(pattern);
                    Some(pattern.map(|pattern|{
                        hir::FieldPattern { id:self.next_id(),name: field_symbol, pattern }
                    }))
                }).collect();
                (PatternKind::Struct(path?, fields.into_iter().collect::<Result<Vec<_>,_>>()?),span)
            }
            ast::ParsedPatternNodeKind::Wildcard => (PatternKind::Wildcard,span),
            ast::ParsedPatternNodeKind::Infer(name) => (PatternKind::Struct(hir::InferOrPath::Infer(pattern.location,Some(self.intern_symbol(name))), vec![]),pattern.location)
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
            ast::ExprNodeKind::Function(sig,body) => hir::ExprKind::Function(Box::new(self.lower_function(expr.id,sig,*body)?)),
            ast::ExprNodeKind::Print(args) => hir::ExprKind::Print(args.into_iter().map(|arg| self.lower_expr(arg)).collect::<Vec<_>>().into_iter().collect::<Result<Vec<_>,_>>()?),
            ast::ExprNodeKind::GetPath(path) => {
                hir::ExprKind::Path(match path.infer_path{
                    InferPathKind::Infer(name) => {
                        if let Some(name) = name{
                            hir::PathExpr::Infer(self.intern_symbol(name))
                        }
                        else{
                            self.error(format!("Cannot use '_' in this position."), path.location);
                            return Err(LoweringErr);
                        }
                    },
                    InferPathKind::Path(path) => {
                        hir::PathExpr::Path(self.lower_path(&path)?)
                    }
                }
                )
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
            ast::ExprNodeKind::Property(expr, field) => hir::ExprKind::Field(Box::new(self.lower_expr(*expr)?), self.intern_symbol(field)),
            ast::ExprNodeKind::Return(expr) => hir::ExprKind::Return(expr.map(|expr| self.lower_expr(*expr).map(Box::new)).map_or(Ok(None), |result| result.map(Some))?),
            ast::ExprNodeKind::StructInit { path, fields } => {
                let path = match path.infer_path{
                    InferPathKind::Infer(name) => {
                        hir::InferOrPath::Infer(path.location,name.map(|name| self.intern_symbol(name)))
                    },
                    InferPathKind::Path(path) => {
                        let Ok(path) = self.lower_path(&path) else {
                            return Err(LoweringErr);
                        };
                        hir::InferOrPath::Path(path)
                    }
                };
                let fields = fields.into_iter().map(|(field_name,field_expr)|{
                    let field_name = self.intern_symbol(field_name);
                    let field_expr = self.lower_expr(field_expr);
                    field_expr.map(|expr| hir::FieldExpr{span:SourceLocation::new(field_name.span.start_line, expr.span.end_line),field:field_name,expr,id: self.next_id()})
                }).collect::<Vec<_>>().into_iter().collect::<Result<Vec<hir::FieldExpr>,_>>()?;
                hir::ExprKind::StructLiteral(path, fields)
            },
            ast::ExprNodeKind::Assign { lhs, rhs } => {
                let lhs = self.lower_expr(*lhs);
                let rhs = self.lower_expr(*rhs);
                match (lhs.map(Box::new),rhs.map(Box::new)) {
                    (Ok(lhs),Ok(rhs)) => hir::ExprKind::Assign(lhs, rhs),
                    _ => return Err(LoweringErr)
                }
            },
            ast::ExprNodeKind::MethodCall { receiver, method, args } => {
                let receiver = self.lower_expr(*receiver).map(Box::new);
                let generic_args = self.lower_generic_args(method.generic_args.as_ref());
                let args = args.into_iter().map(|arg| self.lower_expr(arg)).collect::<Vec<_>>().into_iter().collect::<Result<Vec<_>,_>>()?;
                hir::ExprKind::MethodCall(receiver?, hir::PathSegment { res: Resolution::None, ident: self.intern_symbol(method.name),args: generic_args? },args)
            },
            ast::ExprNodeKind::Instantiate { lhs, args } => {
                let _ = self.lower_expr(*lhs);
                let _ = self.lower_generic_args(Some(&args));
                self.error(format!("Cannot have generic arguments here."),span);
                return Err(LoweringErr);
            },
            ast::ExprNodeKind::Index { lhs, rhs } => {
                let lhs = self.lower_expr(*lhs);
                let rhs = self.lower_expr(*rhs);
                hir::ExprKind::Index(Box::new(lhs?), Box::new(rhs?))
            }
        };
        Ok(hir::Expr { id:self.next_id(), span, kind})
    }
    fn lower_fields(&mut self,fields:Vec<(Symbol,ParsedType)>,field_names:Vec<hir::Ident>)->Result<Vec<hir::FieldDef>,LoweringErr>{
        let fields = field_names.into_iter().zip(fields.into_iter()).map(|(field,(_,field_ty))|{
            let field_ty = self.lower_type(&field_ty);
            field_ty.map(|field_ty| hir::FieldDef{
                name : field,
                ty : field_ty
            })
        }).collect();
        fields
    }
    fn lower_item(&mut self,item:ast::Item) -> Result<(DefId,hir::Item,SourceLocation),LoweringErr>{
        Ok(match item{
            ast::Item::Struct(struct_def) => {
                let struct_id = self.expect_def_id(struct_def.id, "Should be a struct");
                self.begin_scope(struct_def.id);
                let generics = self.lower_generic_params(struct_id,struct_def.generic_params);
                let name = self.name_info.structs[struct_id].name;
                let fields = self.lower_fields(struct_def.fields, self.name_info.structs[struct_id].fields.clone());
                self.end_scope();
                (struct_id,
                Item::Struct(hir::StructDef{
                    id:struct_id,
                    name,
                    generics:generics?,
                    fields:fields?
                }),name.span)
            },
            ast::Item::Enum(enum_def) => {
                let enum_id = self.expect_def_id(enum_def.id, "Should be an enum");
                self.begin_scope(enum_def.id);
                let generics = self.lower_generic_params(enum_id,enum_def.generic_params);
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
                self.end_scope();
                (enum_id,
                Item::Enum(hir::EnumDef{
                    id:enum_id,
                    generics:generics?,
                    name,
                    variants : variants.into_iter().collect::<Result<_,_>>()?
                }),
                name.span)
            },
            ast::Item::Fun(function_def) => {
                let func_id = self.expect_def_id(function_def.id, "Should be a function");
                let name = self.name_info.name_map[func_id];
                //Begin item scope
                self.begin_scope(function_def.id);
                let ast::ParsedFunction{proto:ast::FunctionProto{name:_,generic_params,sig},body} = function_def.function;
                let generics = self.lower_generic_params(func_id,generic_params);
                let function = self.lower_function(function_def.id, sig,body);
                //End item scope
                self.end_scope();
                let function = function?;
                let span = SourceLocation::new(name.span.start_line, self.bodies[function.body].span.end_line);
                (func_id,Item::Function(FunctionDef { id : func_id, generics:generics?, name, function }),span)
            },
            ast::Item::Impl(impl_) => {
                let impl_id =  self.expect_def_id(impl_.id,"There should be an impl");
                self.begin_scope(impl_.id);
                let ty = self.lower_type(&impl_.ty);
                let generics = self.lower_generic_params(impl_id, impl_.generic_params);
                let methods = (||{
                    let mut had_error = false;
                    let mut methods = Vec::with_capacity(impl_.methods.len());
                    for mut method in impl_.methods{
                        let method = (||{
                            let method_id = self.expect_def_id(method.id, "Should be a method");
                            let name = self.name_info.name_map[method_id];
                            self.begin_scope(method.id);
                            let generics = self.lower_generic_params(method_id,method.function.proto.generic_params.take());
                            let function = self.lower_function(method.id,method.function.proto.sig, method.function.body);
                            self.end_scope();
                            Ok(FunctionDef { id:method_id, generics:generics?, name, function:function? })
                        })();
                        match method {
                            Ok(method) => {
                                methods.push(method);
                            },
                            Err(LoweringErr) => {
                                had_error = true;
                            }
                        }
                    }
                    if had_error{
                        return Err(LoweringErr);
                    }
                    Ok(methods)
                })();
                self.end_scope();
                (impl_id,Item::Impl(hir::Impl { id: impl_id, ty:ty?, generics:generics?, methods:methods? ,span:impl_.span}),impl_.span)
            },
        })

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
                let ty = ty.as_ref().map(|ty| self.lower_type(ty));
                let expr = self.lower_expr(expr);
                let pattern = self.define_bindings_and_lower_pattern(pattern);
                (hir::StmtKind::Let(pattern?, ty.map_or(Ok(None), |ty| ty.map(Some))?, expr?),span)
            },
            ast::StmtNode::Item(item) => {
                let (id,item,span) = self.lower_item(item)?;
                (hir::StmtKind::Item(self.add_item_with_def(item, id)),span)
            }
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
    pub fn lower(mut self, items: Vec<ast::Item>) -> Result<Hir,LoweringErr>{
        for item in items{
            let Ok((id,item,_)) = self.lower_item(item) else {
                continue;
            };
            self.add_item_with_def(item, id);
        }
        if self.error_reporter.error_occurred(){
            return Err(LoweringErr);
        }
        Ok(Hir{items:self.items,defs_to_items:self.def_id_map,bodies:self.bodies})
    }
}