use super::{generics::substitute, typed_ast::{PatternNode, PatternNodeKind, TypedAssignmentTarget, TypedAssignmentTargetKind, TypedExprNode, TypedExprNodeKind, TypedFunction, TypedFunctionSignature, TypedStmtNode}, types::{GenericArgs, Type}};



pub fn sub_name(name:&str,args:&[Type])->String{
    let mut full_name = String::from(name);
    full_name.push_str(":[");
    for(i,arg) in args.iter().enumerate(){
        if i>0{
            full_name.push(',');
        }
        full_name.push_str(&format!("{}",arg));
    }
    full_name.push(']');
    full_name
}
fn sub_stmt(stmt:&mut TypedStmtNode,generic_args : &GenericArgs){
    match stmt{
        TypedStmtNode::Expr(expr) | TypedStmtNode::ExprWithSemi(expr)  => {
            sub_expr(expr, generic_args);
        },
        TypedStmtNode::Let { pattern, expr } => {
            sub_pattern(pattern, generic_args);
            sub_expr(expr, generic_args);
        },
        TypedStmtNode::Fun { function,.. } => {
            sub_function(function, generic_args) 
        },
        TypedStmtNode::Struct {  fields,.. } => {
            fields.iter_mut().for_each(|(_,field_type)| *field_type = substitute(field_type.clone(), generic_args));
        },
        TypedStmtNode::GenericFunction { function,.. } => {
            sub_function(function, generic_args);
        },
    }
}
fn sub_assignment_target(target:&mut TypedAssignmentTarget,generic_args : &GenericArgs){
    target.ty = substitute(target.ty.clone(),generic_args);
    match &mut target.kind{
        TypedAssignmentTargetKind::Index { lhs, rhs } => {
            sub_expr(lhs, generic_args);
            sub_expr(rhs, generic_args);
        },
        TypedAssignmentTargetKind::Field { lhs, .. } => {
            sub_expr(lhs, generic_args);
        }
        _ => ()
    };
}

fn sub_expr(expr:&mut TypedExprNode,generic_args : &GenericArgs){
    expr.ty = substitute(expr.ty.clone(), generic_args);
    match &mut expr.kind{
        TypedExprNodeKind::Array(elements) => {
            elements.iter_mut().for_each(|element| sub_expr(element, generic_args))
        },
        TypedExprNodeKind::Get(..) | 
        TypedExprNodeKind::Bool(..) | 
        TypedExprNodeKind::Number(..) | 
        TypedExprNodeKind::String(..) | 
        TypedExprNodeKind::Unit  => {

        },
        TypedExprNodeKind::GetGeneric { args,.. } => {
            args.iter_mut().for_each(|ty| *ty = substitute(ty.clone(), generic_args))
        },
        TypedExprNodeKind::Return { expr } => {
            if let Some(expr) = expr.as_mut(){
                sub_expr(expr, generic_args);
            }
        },
        TypedExprNodeKind::Tuple(elements) => {
            elements.iter_mut().for_each(|element| sub_expr(element, generic_args));
        },
        TypedExprNodeKind::Function(function) => {
            sub_function(function, generic_args);
        },
        TypedExprNodeKind::If { condition, then_branch, else_branch } => {
            sub_expr(condition, generic_args);
            sub_expr(then_branch, generic_args);
            if let Some(else_branch) = else_branch.as_mut(){
                sub_expr(else_branch, generic_args);
            }
        },
        TypedExprNodeKind::Index { lhs, rhs } => {
            sub_expr(lhs, generic_args);
            sub_expr(rhs, generic_args);
        },
        TypedExprNodeKind::Match { matchee, arms } => {
            sub_expr(matchee, generic_args);
            arms.iter_mut().for_each(|arm|{
                sub_pattern(&mut arm.pattern, generic_args);
                arm.ty = substitute(arm.ty.clone(), generic_args);
                sub_expr(&mut arm.expr, generic_args);
            });
        },
        TypedExprNodeKind::Print(args) => {
            args.iter_mut().for_each(|arg| sub_expr(arg, generic_args));
        },
        TypedExprNodeKind::Call { callee, args } => {
            sub_expr(callee, generic_args);
            args.iter_mut().for_each(|expr| sub_expr(expr, generic_args));
        },
        TypedExprNodeKind::Binary {left, right,.. } | 
        TypedExprNodeKind::Logical {  left, right,.. } =>  {
            sub_expr(left, generic_args);
            sub_expr(right, generic_args);
        },
        TypedExprNodeKind::While { condition, body } => {
            sub_expr(condition, generic_args);
            sub_expr(body, generic_args);
        },
        TypedExprNodeKind::Assign { lhs, rhs } => {
            sub_assignment_target(lhs,generic_args);
            sub_expr(rhs, generic_args);
        },
        TypedExprNodeKind::Block { stmts, expr } => {
            stmts.iter_mut().for_each(|stmt| sub_stmt(stmt,generic_args));
            if let Some(expr) = expr.as_mut(){
                sub_expr(expr, generic_args);
            }
        },
        TypedExprNodeKind::TypenameOf(ty) => {
            *ty  = substitute(ty.clone(), generic_args);
        },
        TypedExprNodeKind::Field(lhs, ..) => {
            sub_expr(lhs, generic_args);
        },
        TypedExprNodeKind::Unary { operand,.. } => {
            sub_expr(operand, generic_args);
        },
        TypedExprNodeKind::StructInit { fields } => {
            fields.iter_mut().for_each(|(_,expr)|{
                sub_expr(expr, generic_args);
            });
        }
    };
}
fn sub_pattern(pattern:&mut PatternNode,generic_args : &GenericArgs){
    match &mut pattern.kind{
        PatternNodeKind::Struct { ty, fields } => {
            *ty = substitute(ty.clone(), generic_args);
            fields.iter_mut().for_each(|(_,pattern)| sub_pattern(pattern, generic_args));
        },
        PatternNodeKind::Tuple(elements) => {
            elements.iter_mut().for_each(|element| sub_pattern(element, generic_args));
        },
        _ => ()
    }
}
fn sub_signature(signature:&mut TypedFunctionSignature,args : &GenericArgs){
    let return_type = substitute(signature.return_type.clone(),args);
    signature.params = signature.params.iter().map(|(pattern,ty)|{
        (pattern.clone(),substitute(ty.clone(), args))
    }).collect();
    signature.return_type = return_type;
}
pub fn sub_function(function:&mut TypedFunction,args : &GenericArgs){
    sub_signature(&mut function.signature,args);
    sub_expr(&mut function.body,args);
}