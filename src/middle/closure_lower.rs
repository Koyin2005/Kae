use crate::frontend::typechecking::typed_ast::{TypedExprNode, TypedStmtNode};

pub struct Local{
    pub name : String
}
pub struct Function{
    pub locals : Vec<Local>
}
#[derive(Default)]
pub struct ClosureLowerer{
    pub in_global_scope : bool,
    pub locals : Vec<Vec<Local>>
}

impl ClosureLowerer{
    fn lower_expr(&mut self,expr:&mut TypedExprNode){

    }
    fn lower_stmt(&mut self,stmt:&mut TypedStmtNode){
        match stmt{
            TypedStmtNode::Expr(expr) | TypedStmtNode::ExprWithSemi(expr) => {
                self.lower_expr(expr);
            },
            TypedStmtNode::GenericFunction { name, generic_params, function } => {

            },
            TypedStmtNode::Fun { name, function } => {

            },
            TypedStmtNode::Impl { ty, methods } => {
                todo!()
            },
            TypedStmtNode::Let { pattern, expr } => {
                self.lower_expr(expr);
            },
            TypedStmtNode::Enum { .. }|TypedStmtNode::Struct {..} => ()
        }
    }
    pub fn lower(mut self,stmts:&mut Vec<TypedStmtNode>){
        self.in_global_scope = true;
        for stmt in stmts{
            self.lower_stmt(stmt);
        }
    }
}