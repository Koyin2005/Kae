use super::{generics::substitute, typed_ast::{TypedAssignmentTarget, TypedAssignmentTargetKind, TypedExprNode, TypedExprNodeKind, TypedFunction, TypedFunctionSignature, TypedPatternMatchArm, TypedStmtNode}, types::{GenericArgs, Type}};



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
fn sub_stmt(stmt:&TypedStmtNode,generic_args : &GenericArgs)->TypedStmtNode{
    match stmt{
        TypedStmtNode::Expr(expr) => {
            TypedStmtNode::Expr(sub_expr(expr, generic_args))
        },
        TypedStmtNode::ExprWithSemi(expr) => {
            TypedStmtNode::ExprWithSemi(sub_expr(expr, generic_args))
        },
        TypedStmtNode::Fun { name, function } => {
            TypedStmtNode::Fun { name:name.clone(), function: sub_function(function, generic_args) }
        },
        TypedStmtNode::GenericFunction { name, generic_params, function } => {
            TypedStmtNode::GenericFunction { name:name.clone(), generic_params:generic_params.clone(), function:function.clone() }
        },
        TypedStmtNode::Let { pattern, expr } => {
            TypedStmtNode::Let { pattern: pattern.clone(), expr: sub_expr(expr, generic_args)}
        }
    }
}
fn sub_assignment_target(target:&TypedAssignmentTarget,generic_args : &GenericArgs)->TypedAssignmentTarget{
    let ty = substitute(target.ty.clone(),generic_args);
    let location = target.location;
    let kind = match &target.kind{
        TypedAssignmentTargetKind::Index { lhs, rhs } => {
            TypedAssignmentTargetKind::Index { lhs: Box::new(sub_expr(lhs, generic_args)), rhs: Box::new(sub_expr(rhs, generic_args)) }
        },
        TypedAssignmentTargetKind::Name(name) => {
            TypedAssignmentTargetKind::Name(name.clone())
        }
    };
    TypedAssignmentTarget{
        ty,
        location,
        kind
    }
}

fn sub_expr(expr:&TypedExprNode,generic_args : &GenericArgs)->TypedExprNode{
    let ty = substitute(expr.ty.clone(), generic_args);
    let kind = match &expr.kind{
        TypedExprNodeKind::Array(elements) => {
            TypedExprNodeKind::Array(elements.iter().map(|element| sub_expr(element, generic_args)).collect())
        },
        TypedExprNodeKind::Get(name) => {
            TypedExprNodeKind::Get(name.clone())
        },
        TypedExprNodeKind::GetGeneric { name, args } => {
            TypedExprNodeKind::GetGeneric { name: name.clone(), args: args.iter().map(|ty| substitute(ty.clone(), generic_args)).collect() }
        },
        &TypedExprNodeKind::Bool(bool) => TypedExprNodeKind::Bool(bool),
        &TypedExprNodeKind::Number(number) => TypedExprNodeKind::Number(number),
        TypedExprNodeKind::String(string) => TypedExprNodeKind::String(string.clone()),
        TypedExprNodeKind::Unit => TypedExprNodeKind::Unit,
        TypedExprNodeKind::Return { expr } => {
            TypedExprNodeKind::Return { expr: expr.as_ref().map(|expr| {
                    Box::new(sub_expr(expr, generic_args))
                }) 
            }
        },
        TypedExprNodeKind::Tuple(elements) => {
            TypedExprNodeKind::Tuple(elements.iter().map(|element| sub_expr(element, generic_args)).collect())
        },
        TypedExprNodeKind::Function(function) => {
            TypedExprNodeKind::Function(sub_function(function, generic_args))
        },
        TypedExprNodeKind::If { condition, then_branch, else_branch } => {
            TypedExprNodeKind::If { condition: Box::new(sub_expr(condition, generic_args)),
                     then_branch: Box::new(sub_expr(then_branch, generic_args)), 
                     else_branch: else_branch.as_ref().map(|else_branch| Box::new(sub_expr(else_branch, generic_args))) }
        },
        TypedExprNodeKind::Index { lhs, rhs } => {
            TypedExprNodeKind::Index { lhs: Box::new(sub_expr(lhs, generic_args)), rhs: Box::new(sub_expr(rhs, generic_args)) }
        },
        TypedExprNodeKind::Match { matchee, arms } => {
            TypedExprNodeKind::Match { matchee: Box::new(sub_expr(matchee, generic_args)), arms: arms.iter().map(|arm|{
                TypedPatternMatchArm{
                    pattern:arm.pattern.clone(),
                    location:arm.location,
                    ty:substitute(arm.ty.clone(), generic_args),
                    expr : sub_expr(&arm.expr, generic_args)
                }
            }).collect() }
        },
        TypedExprNodeKind::Print(args) => {
            TypedExprNodeKind::Print(args.iter().map(|arg| sub_expr(arg, generic_args)).collect())
        },
        TypedExprNodeKind::Call { callee, args } => {
            TypedExprNodeKind::Call { callee:Box::new(sub_expr(callee, generic_args)), args: args.iter().map(|arg| sub_expr(arg, generic_args)).collect() }
        },
        TypedExprNodeKind::Binary { op, left, right } => {
            TypedExprNodeKind::Binary { op: *op, left: Box::new(sub_expr(left, generic_args)), right: Box::new(sub_expr(right, generic_args)) }
        },
        TypedExprNodeKind::Logical { op, left, right } => {
            TypedExprNodeKind::Logical { op: *op, left: Box::new(sub_expr(left, generic_args)), right: Box::new(sub_expr(right, generic_args)) }
        },
        TypedExprNodeKind::While { condition, body } => {
            TypedExprNodeKind::While { condition: Box::new(sub_expr(condition, generic_args)), body: Box::new(sub_expr(body, generic_args)) }
        },
        TypedExprNodeKind::Assign { lhs, rhs } => {
            let lhs = sub_assignment_target(lhs,generic_args);
            let rhs = Box::new(sub_expr(rhs, generic_args));
            TypedExprNodeKind::Assign { lhs, rhs }
        },
        TypedExprNodeKind::Block { stmts, expr } => {
            let stmts =stmts.iter().map(|stmt| sub_stmt(stmt,generic_args)).collect();
            let expr = expr.as_ref().map(|expr| Box::new(sub_expr(expr, generic_args)));
            TypedExprNodeKind::Block { stmts, expr }
        },
        TypedExprNodeKind::TypenameOf(ty) => {
            TypedExprNodeKind::TypenameOf(substitute(ty.clone(), generic_args))
        },
        TypedExprNodeKind::Field(lhs, field) => {
            TypedExprNodeKind::Field(Box::new(sub_expr(lhs, generic_args)), field.clone())
        },
        TypedExprNodeKind::Unary { op,operand } => {
            TypedExprNodeKind::Unary { op:*op, operand: Box::new(sub_expr(operand, generic_args)) }
        }
    };
    TypedExprNode { location: expr.location, ty, kind }
}
fn sub_signature(signature:&TypedFunctionSignature,args : &GenericArgs)->TypedFunctionSignature{
    let params = signature.params.iter().map(|(pattern,ty)|{
        (pattern.clone(),substitute(ty.clone(), args))
    }).collect();
    let return_type = substitute(signature.return_type.clone(),args);
    TypedFunctionSignature { params, return_type }
}
pub fn sub_function(function:&TypedFunction,args : &GenericArgs)->TypedFunction{
    let signature = sub_signature(&function.signature,args);
    let body = sub_expr(&function.body,args);
    TypedFunction { signature, body:Box::new(body) }
}