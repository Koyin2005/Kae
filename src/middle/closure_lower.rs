use crate::frontend::typechecking::typed_ast::{TypedAssignmentTarget, TypedAssignmentTargetKind, TypedExprNode, TypedExprNodeKind, TypedStmtNode};

pub struct Local{
    pub name : String,
    pub depth : usize
}
pub struct Function{
    pub locals : Vec<Local>
}
#[derive(Default)]
pub struct ClosureLowerer{
    pub scope_depth : usize,
    pub locals : Vec<Vec<Local>>
}

impl ClosureLowerer{
    fn declare_name(&mut self){}
    fn store_name(&mut self){}
    fn load_name(&mut self){}
    fn lower_assignment_target(&mut self,target:&mut TypedAssignmentTarget){
        match &mut target.kind{
            TypedAssignmentTargetKind::Name(name) => {

            },
            TypedAssignmentTargetKind::Field { lhs, .. } => {
                self.lower_expr(lhs);
            },
            TypedAssignmentTargetKind::Index { lhs, rhs } => {
                self.lower_expr(lhs);
                self.lower_expr(rhs);
            }
        }
    }
    fn lower_expr(&mut self,expr:&mut TypedExprNode){
        match &mut expr.kind{
            TypedExprNodeKind::Unit | TypedExprNodeKind::Number(_) | TypedExprNodeKind::String(_)|TypedExprNodeKind::Bool(_)|
            TypedExprNodeKind::TypenameOf(_)|TypedExprNodeKind::GetMethod { .. } => (),
            TypedExprNodeKind::Array(elements) | TypedExprNodeKind::Tuple(elements) => {
                elements.iter_mut().for_each(|element| self.lower_expr(element));
            },
            TypedExprNodeKind::Binary { left, right,.. } | TypedExprNodeKind::Logical { left, right,.. }|
            TypedExprNodeKind::Index { lhs:left, rhs:right } => {
                self.lower_expr(left);
                self.lower_expr(right);
            },
            TypedExprNodeKind::Unary { operand,.. } => {
                self.lower_expr(operand);
            },
            TypedExprNodeKind::Return { expr } => {
                if let Some(expr) = expr.as_mut(){
                    self.lower_expr(expr);
                }
            },
            TypedExprNodeKind::If { condition, then_branch, else_branch } => {
                self.lower_expr(condition);
                self.lower_expr(then_branch);
                if let Some(else_branch) = else_branch.as_mut(){
                    self.lower_expr(else_branch);
                }
            },
            TypedExprNodeKind::While { condition, body } => {
                self.lower_expr(condition);
                self.lower_expr(body);
            },
            TypedExprNodeKind::MethodCall { lhs:first,  args,.. }| TypedExprNodeKind::Call { callee:first, args } => {
                self.lower_expr(first);
                args.iter_mut().for_each(|arg| self.lower_expr(arg));
            },
            TypedExprNodeKind::Assign { lhs, rhs } => {
                self.lower_assignment_target(lhs);
                self.lower_expr(rhs);
            },
            TypedExprNodeKind::Match { matchee, arms } => {
                self.lower_expr(matchee);
                arms.iter_mut().for_each(|arm|{
                    self.lower_expr(&mut arm.expr);
                });
            },
            TypedExprNodeKind::Block { stmts, expr } => {

            },
            TypedExprNodeKind::Print(args) => {
                args.iter_mut().for_each(|arg| self.lower_expr(arg));
            },
            TypedExprNodeKind::StructInit { fields,.. } => {
                fields.iter_mut().for_each(|(_,arg)| self.lower_expr(arg));
            },
            TypedExprNodeKind::Field(lhs, _) => {
                self.lower_expr(lhs);
            },
            TypedExprNodeKind::Get(name)|TypedExprNodeKind::GetGeneric { name, .. } => {},
            TypedExprNodeKind::Function(function) => {

            }
        }
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
        for stmt in stmts{
            self.lower_stmt(stmt);
        }
    }
}