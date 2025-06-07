use crate::{data_structures::IndexVec, errors::ErrorReporter, identifiers::BodyIndex, SymbolInterner};

use super::{ast_lowering::hir::{self, DefIdMap}, pattern_checking::{lowering::lower_to_pattern, PatternChecker}, thir::{self, Block, Expr, ExprId, Param, Stmt, StmtId, StmtKind, Thir, ThirBody}, typechecking::{checking::TypeCheckResults, context::TypeContext, types::{generics::GenericArgs, AdtKind}}};

pub struct ThirLoweringErr;


struct BodyLower<'a>{
    lower_context : &'a ThirLower<'a>,
    thir : ThirBody
}
impl <'a> BodyLower<'a>{
    fn lower(context:&'a ThirLower<'a>,body:hir::Body) -> ThirBody{
        let mut lower = Self { 
            lower_context:context, thir: ThirBody { 
                params: IndexVec::new(), 
                exprs: IndexVec::new(), 
                blocks: IndexVec::new(), 
                stmts: IndexVec::new(), 
                arms: IndexVec::new() 
            } 
        };
        for param in body.params{
            let pattern = lower.lower_pattern(param.pattern);
            lower.thir.params.push(Param{ty:pattern.ty.clone(),pattern});
        }
        lower.lower_expr(body.value);
        lower.thir
    }
    fn results(&self) -> &TypeCheckResults{
        &self.lower_context.results
    }
    fn type_context(&self) -> &TypeContext{
        self.lower_context.context
    }
    fn lower_stmts<F>(&mut self, stmts: impl Iterator<Item = hir::Stmt>) -> F where F : FromIterator<StmtId>{
        stmts.filter_map(|stmt| self.lower_stmt(stmt)).collect()
    }
    fn lower_exprs<F>(&mut self, exprs: impl Iterator<Item = hir::Expr>) -> F where F : FromIterator<ExprId>{
        exprs.map(|expr| self.lower_expr(expr)).collect()
    }
    fn lower_pattern(&mut self, pattern: hir::Pattern) -> thir::Pattern{
        let ty = self.results().node_types[&pattern.id].clone();
        let kind = match pattern.kind{
            hir::PatternKind::Binding(variable,name,sub_pattern) => {
                thir::PatternKind::Binding(name.index, variable, sub_pattern.map(|pattern| Box::new(self.lower_pattern(*pattern))))
            },
            hir::PatternKind::Wildcard => {
                thir::PatternKind::Wildcard
            },
            hir::PatternKind::Literal(literal) => {
                thir::PatternKind::Constant(literal)
            },
            hir::PatternKind::Tuple(patterns) => {
                thir::PatternKind::Tuple(patterns.into_iter().map(|pattern| self.lower_pattern(pattern)).collect())
            },
            hir::PatternKind::Struct(_,fields) => {
                let id = match self.results().resolutions[&pattern.id]{
                    hir::Resolution::Definition(hir::DefKind::Struct,id) => id,
                    res => unreachable!("Unknown resolution {:?} found for pattern",res)
                };
                let generic_args = self.results().generic_args[&pattern.id].clone();
                thir::PatternKind::Struct(id,generic_args,fields.into_iter().map(|field_pattern|{
                        thir::FieldPattern{
                            field : self.results().fields[&field_pattern.id],
                            pattern : self.lower_pattern(field_pattern.pattern)
                        }
                    }).collect())  
            },
            hir::PatternKind::Variant(_,fields) => {
                let id = match self.results().resolutions[&pattern.id]{
                    hir::Resolution::Definition(hir::DefKind::Variant,id) => id,
                    res => unreachable!("Unknown resolution {:?} found for pattern",res)
                };
                let type_id = self.lower_context.context.expect_owner_of(id);
                let generic_args = self.results().generic_args[&pattern.id].clone();
                thir::PatternKind::Variant(type_id,generic_args,self.type_context().get_variant_index(id).expect("There should be a variant index"),fields.into_iter().map(|field_pattern|{
                        self.lower_pattern(field_pattern)
                }).collect())  
            }
        };
        thir::Pattern { ty, span: pattern.span, kind }
    }
    fn lower_stmt(&mut self, stmt: hir::Stmt) -> Option<StmtId>{
        Some(match stmt.kind{
            hir::StmtKind::Expr(expr) => {
                let expr_id = self.lower_expr(expr);
                self.thir.stmts.push(Stmt{kind:StmtKind::Expr{expr:expr_id,drop:false}})
            },
            hir::StmtKind::Let(pattern,_,expr) => {
                let pattern = self.lower_pattern(pattern);
                let expr = self.lower_expr(expr);
                if !PatternChecker::new(self.type_context()).check_exhaustive(vec![lower_to_pattern(&pattern)], &pattern.ty).missing_patterns().is_empty(){
                    self.lower_context.error_reporter.emit(format!("Refutable pattern in 'let' statement."), stmt.span);
                }
                self.thir.stmts.push(Stmt{kind:StmtKind::Let(Box::new(pattern),expr)})
            },
            hir::StmtKind::Semi(expr) => {
                let expr = self.lower_expr(expr);
                self.thir.stmts.push(Stmt{kind:StmtKind::Expr{expr,drop:true}})
            },
            hir::StmtKind::Item(_) => return None
        })
    }
    fn lower_expr_as_path(&mut self, expr_id: hir::HirId) -> Option<thir::ExprKind>{
        let res = self.results().resolutions.get(&expr_id).copied()?;
        Some(match res{
            hir::Resolution::Variable(variable) => {
                thir::ExprKind::Variable(variable)
            },
            hir::Resolution::Definition(hir::DefKind::Function|hir::DefKind::Variant|hir::DefKind::Struct|hir::DefKind::Method, id) => {
                let generic_args = self.results().generic_args[&expr_id].clone();
                thir::ExprKind::Definition(id,generic_args)
            },
            hir::Resolution::Builtin(hir::BuiltinKind::Panic) => {
                thir::ExprKind::Builtin(GenericArgs::new_empty(),hir::BuiltinKind::Panic)

            },
            _ => unreachable!("Should all be simplified")
        })

    }
    fn lower_expr(&mut self, expr: hir::Expr) -> ExprId{
        let ty =  self.results().node_types[&expr.id].clone();
        let kind = match expr.kind{
            hir::ExprKind::Literal(literal) => {
                thir::ExprKind::Literal(literal)
            },
            hir::ExprKind::Array(elements) => {
                thir::ExprKind::Array(self.lower_exprs(elements.into_iter()))
            },
            hir::ExprKind::Call(callee,args) => {
                thir::ExprKind::Call(self.lower_expr(*callee),self.lower_exprs(args.into_iter()))
            },
            hir::ExprKind::Field(base,_) => thir::ExprKind::Field(self.lower_expr(*base),self.results().fields[&expr.id]),
            hir::ExprKind::Tuple(elements) => thir::ExprKind::Tuple(self.lower_exprs(elements.into_iter())),
            hir::ExprKind::Binary(op,left,right) => thir::ExprKind::Binary(op, self.lower_expr(*left), self.lower_expr(*right)),
            hir::ExprKind::Unary(op,operand) => thir::ExprKind::Unary(op,self.lower_expr(*operand)),
            hir::ExprKind::Assign(left,right) => thir::ExprKind::Assign(self.lower_expr(*left),self.lower_expr(*right)),
            hir::ExprKind::Logical(op,left,right) => thir::ExprKind::Logical(op,self.lower_expr(*left), self.lower_expr(*right)),
            hir::ExprKind::If(condition,then_branch,else_branch) => 
                thir::ExprKind::If(self.lower_expr(*condition),self.lower_expr(*then_branch),else_branch.map(|else_branch| self.lower_expr(*else_branch))),
            hir::ExprKind::Return(return_expr) => thir::ExprKind::Return(return_expr.map(|return_expr| self.lower_expr(*return_expr))),
            hir::ExprKind::Path(_) => {
                self.lower_expr_as_path(expr.id).expect(&format!("There should be a resolution for '{:?}'.",&expr))
            },
            hir::ExprKind::Block(stmts,result_expr) => {
                let stmts = self.lower_stmts(stmts.into_iter());
                let expr = result_expr.map(|result_expr| self.lower_expr(*result_expr));
                thir::ExprKind::Block(self.thir.blocks.push(Block{
                    stmts,
                    expr
                }))
            },
            hir::ExprKind::Print(args) => {
                let args = self.lower_exprs(args.into_iter());
                thir::ExprKind::Print(args)
            },
            hir::ExprKind::Index(left, right) => thir::ExprKind::Index(self.lower_expr(*left), self.lower_expr(*right)),
            hir::ExprKind::Match(scrutinee,arms) => {
                let scrutinee = self.lower_expr(*scrutinee);
                let arms: Box<[thir::ArmId]> = arms.into_iter().map(|arm|{
                    let arm = thir::Arm{
                        pat : Box::new(self.lower_pattern(arm.pat)),
                        body: self.lower_expr(arm.body)
                    };
                    self.thir.arms.push(arm)
                }).collect();
                
                let patterns = arms.iter().copied().map(|arm|  &self.thir.arms[arm].pat).map(|pattern|{
                    lower_to_pattern(pattern)
                });
                let missing_patterns =  PatternChecker::new(self.type_context()).check_exhaustive(patterns.collect(),&self.thir.exprs[scrutinee].ty).missing_patterns();
                if !missing_patterns.is_empty(){
                    let mut error_message = format!("Non exhaustive match \n Missing patterns:\n");
                    for (i,pattern) in missing_patterns.into_iter().enumerate(){
                        if i>0{
                            error_message.push('\n');
                        }
                        error_message.push(' ');
                        error_message.push(' ');
                        error_message.push_str(&pattern.format(self.type_context(), self.lower_context.interner));
                    }
                    self.lower_context.error_reporter.emit(error_message, expr.span);
                }

                thir::ExprKind::Match(scrutinee, arms)
            },
            hir::ExprKind::Function(function) => thir::ExprKind::Definition(function.id,GenericArgs::new_empty()),
            hir::ExprKind::MethodCall(receiver,method,args) =>{
                let expr_id = expr.id;
                let receiver = self.lower_expr(*receiver);
                let args = self.lower_exprs(args.into_iter());
                let callee = if let Some(kind) = self.lower_expr_as_path(expr_id){
                    self.thir.exprs.push(Expr { ty: self.results().signatures[&expr.id].as_type(), kind, span: method.ident.span })
                }
                else{
                    self.thir.exprs.push(Expr { ty: self.results().signatures[&expr.id].as_type(), kind : thir::ExprKind::Field(receiver, self.results().fields[&expr.id]), span: method.ident.span })

                };
                thir::ExprKind::Call(callee, args)
            },
            hir::ExprKind::While(condition,body) => thir::ExprKind::While(self.lower_expr(*condition), self.lower_expr(*body)),
            hir::ExprKind::StructLiteral(_,fields) => {
                let (kind,id,variant) = match self.results().resolutions[&expr.id]{
                    hir::Resolution::Definition(hir::DefKind::Struct,id) => (AdtKind::Struct,id,None),
                    hir::Resolution::Definition(hir::DefKind::Variant,id) => (AdtKind::Enum,self.type_context().expect_owner_of(id),self.type_context().get_variant_index(id)),
                    _ => unreachable!("Unknown constructor found")
                };
                thir::ExprKind::StructLiteral(Box::new(thir::StructLiteral{
                    kind,
                    id,
                    variant,
                    fields : fields.into_iter().map(|field|{
                        let field_index = self.results().fields[&field.id];
                        thir::FieldExpr{
                            field:field_index,
                            expr:self.lower_expr(field.expr)
                        }
                    }).collect()
                }))
            },
        };
        if let Some(coercion) = self.lower_context.results.coercions.get(&expr.id){
            let span = expr.span;
            let expr_id = self.thir.exprs.push(
                Expr{
                    kind,
                    span:expr.span,
                    ty
                }
            );
            self.thir.exprs.push(Expr { ty: coercion.clone(), kind: thir::ExprKind::Cast(expr_id), span })
            
        } else { 
            self.thir.exprs.push(Expr{
                kind,
                span:expr.span,
                ty
            })
        }
    }
}
pub struct ThirLower<'a>{
    results : TypeCheckResults,
    bodies : IndexVec<BodyIndex,ThirBody>,
    error_reporter : ErrorReporter,
    interner: &'a SymbolInterner,
    context: &'a TypeContext
}
impl<'a> ThirLower<'a>{
    pub fn new(results: TypeCheckResults,context:&'a TypeContext,interner:&'a SymbolInterner) -> Self{
        Self { results,interner, bodies : IndexVec::new(),context,error_reporter:ErrorReporter::new(false)}
    }
    pub fn lower_bodies(mut self,bodies: IndexVec<BodyIndex,hir::Body>,owners:DefIdMap<BodyIndex>) -> Result<Thir,ThirLoweringErr>{
        self.bodies = bodies.into_iter().map(|body|{
            BodyLower::lower(&self,body)
        }).collect();
        if self.error_reporter.error_occurred(){
            return Err(ThirLoweringErr);
        }
        Ok(Thir { body_owners:owners,bodies: self.bodies})
    }
}