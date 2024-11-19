use crate::frontend::typechecking::typed_ast::{PatternNode, PatternNodeKind, TypedAssignmentTarget, TypedAssignmentTargetKind, TypedExprNode, TypedExprNodeKind, TypedFunction, TypedStmtNode};

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

    fn begin_scope(&mut self){}
    fn end_scope(&mut self){}

    fn visit_function(&mut self,function:&mut TypedFunction){
        
    }
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
    fn lower_pattern(&mut self,pattern:&mut PatternNode){
        match &mut pattern.kind{
            PatternNodeKind::Array(before,mid ,rest ) => {
                before.iter_mut().for_each(|before| self.lower_pattern(before));
                if let Some(mid) = mid.as_mut(){
                    self.lower_pattern(mid);
                }
                rest.iter_mut().for_each(|rest| self.lower_pattern(rest));
            },
            PatternNodeKind::Tuple(elements) => {
                elements.iter_mut().for_each(|element| self.lower_pattern(element));
            },
            PatternNodeKind::Struct { fields,.. } => {
                fields.iter_mut().for_each(|(_,pattern)|{
                    self.lower_pattern(pattern);
                });
            },
            PatternNodeKind::Name(name) => {
                
            },
            PatternNodeKind::Is(name,pattern ) => {
                
            }
            PatternNodeKind::Bool(_) | PatternNodeKind::Float(_) | PatternNodeKind::Int(_) | PatternNodeKind::Wildcard | PatternNodeKind::String(_) => ()
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
                    self.begin_scope();
                    self.lower_pattern(&mut arm.pattern);
                    self.lower_expr(&mut arm.expr);
                    self.end_scope();

                });
            },
            TypedExprNodeKind::Block { stmts, expr } => {
                self.begin_scope();
                for stmt in stmts{
                    self.lower_stmt(stmt);
                }
                if let Some(expr) = expr.as_mut(){
                    self.lower_expr(expr);
                }
                self.end_scope();

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
                self.lower_pattern(pattern);
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