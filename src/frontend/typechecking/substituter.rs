use super::{typed_ast::{Expr, ExprKind, FieldExpr, FieldPattern, Function, FunctionParam, FunctionSignature, Pattern, PatternKind, Stmt, StmtKind}, types::GenericArgs};


fn sub_stmt(stmt:&mut Stmt,generic_args : &GenericArgs){
    match &mut stmt.kind{
        StmtKind::Expr(expr)   => {
            sub_expr(expr, generic_args);
        },
        StmtKind::Let { pattern, expr } => {
            sub_pattern(pattern, generic_args);
            sub_expr(expr, generic_args);
        },
    }
}

fn sub_expr(expr:&mut Expr,generic_args : &GenericArgs){
    expr.ty = expr.ty.substitute(generic_args);
    match &mut expr.kind{
        ExprKind::Array(elements) => {
            elements.iter_mut().for_each(|element| sub_expr(element, generic_args))
        },
        ExprKind::Variable(..) | 
        ExprKind::Literal(..) | 
        ExprKind::Function(..) => {

        },
        ExprKind::GetGeneric { args,.. } => {
            args.iter_mut().for_each(|ty| *ty = ty.substitute(generic_args))
        },
        ExprKind::Return { expr } => {
            if let Some(expr) = expr.as_mut(){
                sub_expr(expr, generic_args);
            }
        },
        ExprKind::Tuple(elements) => {
            elements.iter_mut().for_each(|element| sub_expr(element, generic_args));
        },
        ExprKind::AnonFunction(function) => {
            sub_function(function, generic_args);
        },
        ExprKind::If { condition, then_branch, else_branch } => {
            sub_expr(condition, generic_args);
            sub_expr(then_branch, generic_args);
            if let Some(else_branch) = else_branch.as_mut(){
                sub_expr(else_branch, generic_args);
            }
        },
        ExprKind::Index { lhs, rhs } => {
            sub_expr(lhs, generic_args);
            sub_expr(rhs, generic_args);
        },
        ExprKind::Match { matchee, arms } => {
            sub_expr(matchee, generic_args);
            arms.iter_mut().for_each(|arm|{
                sub_pattern(&mut arm.pattern, generic_args);
                sub_expr(&mut arm.body, generic_args);
            });
        },
        ExprKind::Print(args) => {
            args.iter_mut().for_each(|arg| sub_expr(arg, generic_args));
        },
        ExprKind::Call { callee, args } => {
            sub_expr(callee, generic_args);
            args.iter_mut().for_each(|expr| sub_expr(expr, generic_args));
        },
        ExprKind::Binary {left, right,.. } | 
        ExprKind::Logical {  left, right,.. } =>  {
            sub_expr(left, generic_args);
            sub_expr(right, generic_args);
        },
        ExprKind::While { condition, body } => {
            sub_expr(condition, generic_args);
            sub_expr(body, generic_args);
        },
        ExprKind::Assign { lhs, rhs } => {
            sub_expr(lhs, generic_args);
            sub_expr(rhs, generic_args);
        },
        ExprKind::Block { stmts, expr } => {
            stmts.iter_mut().for_each(|stmt| sub_stmt(stmt,generic_args));
            if let Some(expr) = expr.as_mut(){
                sub_expr(expr, generic_args);
            }
        },
        ExprKind::Typename(ty) => {
            *ty  = ty.substitute(generic_args);
        },
        ExprKind::Field(lhs, ..) => {
            sub_expr(lhs, generic_args);
        },
        ExprKind::Unary { operand,.. } => {
            sub_expr(operand, generic_args);
        },
        ExprKind::Constructor { fields,.. } => {
            fields.iter_mut().for_each(|FieldExpr{index:_,expr}|{
                sub_expr(expr, generic_args);
            });
        },
    };
}
fn sub_pattern(pattern:&mut Pattern,generic_args : &GenericArgs){
    pattern.ty = pattern.ty.substitute(generic_args);
    match &mut pattern.kind{
        PatternKind::Constructor { kind:_,fields } => {
            fields.iter_mut().for_each(|FieldPattern{index:_,pattern}| sub_pattern(pattern, generic_args));
        },
        PatternKind::Tuple(elements) => {
            elements.iter_mut().for_each(|element| sub_pattern(element, generic_args));
        },
        _ => ()
    }
}
fn sub_signature(signature:&mut FunctionSignature,args : &GenericArgs){
    let return_type = signature.return_type.substitute(args);
    signature.params.iter_mut().for_each(|FunctionParam{pattern,ty}|{
        sub_pattern(pattern, args);
        *ty = ty.substitute(args);
    });
    signature.return_type = return_type;
}
pub fn sub_function(function:&mut Function,args : &GenericArgs){
    sub_signature(&mut function.signature,args);
    sub_expr(&mut function.body,args);
}