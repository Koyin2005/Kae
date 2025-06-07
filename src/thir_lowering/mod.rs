use indexmap::IndexMap;

use crate::{data_structures::IndexVec, frontend::{ast_lowering::hir, thir::{Expr, ExprId, ExprKind, Pattern, PatternKind, StmtKind, Thir, ThirBody}}, identifiers::VariableIndex, middle::mir::{self, Block, Body, Constant, Local, LocalKind, Mir, Operand, Place, RValue, Stmt}};


pub struct MirBuild{
    thir : Thir
}

impl MirBuild{
    pub fn new(thir : Thir) -> Self{
        Self {  thir}
    }
    pub fn lower(self) -> Mir{
        let bodies = self.thir.bodies.into_iter().map(|body|{
            BodyBuild::new(&body).lower_body()
        }).collect();
        Mir { bodies:  bodies}
    }
}


struct BodyBuild<'a>{
    body: &'a ThirBody,
    result_body : Body,
    var_to_local : IndexMap<VariableIndex,Local>,
    current_stmts : Vec<Stmt>
}
impl<'a> BodyBuild<'a>{
    fn new(body:&'a ThirBody) -> Self{
        Self{body:&body, result_body:Body { locals: IndexVec::new(), blocks:IndexVec::new()},current_stmts:Vec::new(),var_to_local:IndexMap::new()}
    }
    fn lower_as_operand(&mut self,expr:&Expr) -> Operand{
        match &expr.kind{
            ExprKind::Literal(literal) => {
                Operand::Constant(match *literal {
                    hir::LiteralKind::Bool(bool) =>  Constant::Bool(bool),
                    hir::LiteralKind::Float(_) => todo!("Floats"),
                    hir::LiteralKind::Int(int) => Constant::Int(int),
                    hir::LiteralKind::String(string) => Constant::String(string)
                })
            },
            ExprKind::Tuple(elements) if elements.is_empty() => {
                Operand::Constant(mir::Constant::ZeroSized(expr.ty.clone()))
            },
            _ => todo!("The rest of operands")
        }
    }

    fn lower_as_rvalue(&mut self,expr:&Expr) -> RValue{
        match &expr.kind{
            ExprKind::Binary(op,left,right) => {
                let left = &self.body.exprs[*left];
                let right = &self.body.exprs[*right];
                let left = self.lower_as_operand(left);
                let right = self.lower_as_operand(right);
                RValue::Binary(*op, Box::new((left,right)))
            },
            ExprKind::Unary(op,operand) => {
                let operand = self.lower_as_operand(&self.body.exprs[*operand]);
                RValue::Unary(*op, operand)
            }
            _ => RValue::Use(self.lower_as_operand(expr))
        }
    }
    fn lower_let(&mut self,pattern:&Pattern,expr_id: ExprId){
        match pattern.kind{
            PatternKind::Binding(name,variable,None) => {
                let local = self.new_local_for_variable(variable);
                let value = self.lower_as_rvalue(&self.body.exprs[expr_id]);
                self.assign_stmt(Place{local,projections:Box::new([])}, value);
            },
            _ => todo!("The rest")
        }
    }
    fn new_temporary(&mut self) -> Local{
        self.new_local(LocalKind::Temporary)
    }
    fn new_local_for_variable(&mut self, variable : VariableIndex) -> Local{
        let local = self.new_local(LocalKind::Variable(variable));
        self.var_to_local.insert(variable, local);
        local
    }
    fn new_local(&mut self,kind: LocalKind) -> Local{
        self.result_body.locals.push(kind)
    }
    fn assign_stmt(&mut self,lvalue: Place, rvalue : RValue ){
        self.current_stmts.push(Stmt::Assign(lvalue,rvalue));
    }
    fn lower_body(mut self) -> Body{
        for stmt in self.body.stmts.iter(){
            match &stmt.kind{
                StmtKind::Expr (expr) => {
                },
                StmtKind::Let(pattern,expr) => {
                    self.lower_let(pattern, *expr);
                }
            }
        }
        self.result_body.blocks.push(Block { stmts: self.current_stmts, terminator: mir::Terminator::Return });
        self.result_body
    }
}