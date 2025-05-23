use crate::{data_structures::IndexVec, identifiers::BodyIndex};

use super::{ast_lowering::hir, thir::{self, Block, Expr, ExprId, Stmt, StmtId, StmtKind, Thir, ThirBody}, typechecking::{checking::TypeCheckResults, context::TypeContext, types::{generics::GenericArgs, AdtKind}}};

pub struct ThirLoweringErr;
pub struct ThirLower<'a>{
    results : TypeCheckResults,
    bodies : IndexVec<BodyIndex,ThirBody>,
    thir : ThirBody,
    context: &'a TypeContext
}
impl<'a> ThirLower<'a>{
    pub fn new(results: TypeCheckResults,context:&'a TypeContext) -> Self{
        Self { results, bodies : IndexVec::new(), thir:ThirBody { exprs: IndexVec::new(), blocks: IndexVec::new(), stmts: IndexVec::new(), arms: IndexVec::new() },context}
    }
    fn lower_stmts<F>(&mut self, stmts: impl Iterator<Item = hir::Stmt>) -> F where F : FromIterator<StmtId>{
        stmts.filter_map(|stmt| self.lower_stmt(stmt)).collect()
    }
    fn lower_exprs<F>(&mut self, exprs: impl Iterator<Item = hir::Expr>) -> F where F : FromIterator<ExprId>{
        exprs.map(|expr| self.lower_expr(expr)).collect()
    }
    fn lower_pattern(&mut self, pattern: hir::Pattern) -> thir::Pattern{
        let ty = self.results.expr_types[&pattern.id].clone();
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
                let (id,variant) = match self.results.resolutions[&pattern.id]{
                    hir::Resolution::Definition(hir::DefKind::Struct,id) => (id,None),
                    hir::Resolution::Definition(hir::DefKind::Variant,id) => (self.context.expect_owner_of(id),self.context.get_variant_index(id)),
                    _ => unreachable!("Unknown constructor found for pattern")
                };
                let generic_args = self.results.generic_args[&pattern.id].clone();
                thir::PatternKind::Variant(generic_args,id,variant,fields.into_iter().map(|field_pattern|{
                    thir::FieldPattern{
                        field : self.results.fields[&field_pattern.id],
                        pattern : self.lower_pattern(field_pattern.pattern)
                    }
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
        let res = self.results.resolutions.get(&expr_id).copied()?;
        Some(match res{
            hir::Resolution::Variable(variable) => {
                thir::ExprKind::Variable(variable)
            },
            hir::Resolution::Definition(hir::DefKind::Function|hir::DefKind::Variant|hir::DefKind::Struct, id) => {
                let generic_args = self.results.generic_args[&expr_id].clone();
                thir::ExprKind::Definition(generic_args, id)
            },
            hir::Resolution::Builtin(hir::BuiltinKind::Panic) => {
                thir::ExprKind::Builtin(GenericArgs::new_empty(),hir::BuiltinKind::Panic)

            },
            _ => unreachable!("Should all be simplified")
        })

    }
    fn lower_expr(&mut self, expr: hir::Expr) -> ExprId{
        let ty = self.results.expr_types[&expr.id].clone();
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
            hir::ExprKind::Field(base,_) => thir::ExprKind::Field(self.lower_expr(*base),self.results.fields[&expr.id]),
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
                let arms = arms.into_iter().map(|arm|{
                    let arm = thir::Arm{
                        pat : Box::new(self.lower_pattern(arm.pat)),
                        body: self.lower_expr(arm.body)
                    };
                    self.thir.arms.push(arm)
                }).collect();
                thir::ExprKind::Match(scrutinee, arms)
            },
            hir::ExprKind::Function(function) => thir::ExprKind::Function(function.body),
            hir::ExprKind::MethodCall(receiver,method,args) =>{
                let expr_id = expr.id;
                let receiver = self.lower_expr(*receiver);
                let args = self.lower_exprs(args.into_iter());
                let callee = if let Some(kind) = self.lower_expr_as_path(expr_id){
                    self.thir.exprs.push(Expr { ty: self.results.signatures[&expr.id].as_type(), kind, span: method.ident.span })
                }
                else{
                    self.thir.exprs.push(Expr { ty: self.results.signatures[&expr.id].as_type(), kind : thir::ExprKind::Field(receiver, self.results.fields[&expr.id]), span: method.ident.span })

                };
                thir::ExprKind::Call(callee, args)
            },
            hir::ExprKind::While(condition,body) => thir::ExprKind::While(self.lower_expr(*condition), self.lower_expr(*body)),
            hir::ExprKind::StructLiteral(_,fields) => {
                let (kind,id,variant) = match self.results.resolutions[&expr.id]{
                    hir::Resolution::Definition(hir::DefKind::Struct,id) => (AdtKind::Struct,id,None),
                    hir::Resolution::Definition(hir::DefKind::Variant,id) => (AdtKind::Enum,self.context.expect_owner_of(id),self.context.get_variant_index(id)),
                    _ => unreachable!("Unknown constructor found")
                };
                thir::ExprKind::StructLiteral(Box::new(thir::StructLiteral{
                    kind,
                    id,
                    variant,
                    fields : fields.into_iter().map(|field|{
                        let field_index = self.results.fields[&field.id];
                        thir::FieldExpr{
                            field:field_index,
                            expr:self.lower_expr(field.expr)
                        }
                    }).collect()
                }))
            },
            hir::ExprKind::Typename(_, _) => {
                todo!("Type name")
            }
        };
        self.thir.exprs.push(Expr{
            kind,
            span:expr.span,
            ty
        })
    }
    pub fn lower_bodies(mut self,bodies: IndexVec<BodyIndex,hir::Expr>) -> Result<Thir,ThirLoweringErr>{
        for body in bodies.into_iter(){
            self.lower_expr(body);
            self.bodies.push(std::mem::replace(&mut self.thir, ThirBody{exprs:IndexVec::new(),blocks:IndexVec::new(),stmts:IndexVec::new(),arms:IndexVec::new()}));
        }
        Ok(Thir { bodies: self.bodies})
    }
}