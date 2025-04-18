use crate::frontend::{ast_lowering::hir, tokenizing::SourceLocation, typechecking::types::Type};

use super::{check::TypeChecker, Expectation};

impl TypeChecker<'_>{
    pub(super) fn check_binary_expr(&self,op:hir::BinaryOp,left:&hir::Expr,right:&hir::Expr,span:SourceLocation) -> Type{
        let left = self.check_expr(left, Expectation::None);
        let right = self.check_expr(right, Expectation::None);
        match (op,&left,&right){
            (hir::BinaryOp::Add|hir::BinaryOp::Subtract|hir::BinaryOp::Multiply|hir::BinaryOp::Divide,left,right) => {
                match (left,right) {
                    (Type::Float,Type::Float) => return Type::Float,
                    (Type::Int,Type::Int) => return Type::Int,
                    _ => ()
                }
            },
            (hir::BinaryOp::Lesser|hir::BinaryOp::LesserEquals|hir::BinaryOp::Greater|hir::BinaryOp::GreaterEquals,left,right) => {
                match (left,right) {
                    (Type::Float,Type::Float) | (Type::Int,Type::Int) => return Type::Bool,
                    _ => ()
                }

            },
            (hir::BinaryOp::Equals|hir::BinaryOp::NotEquals,left,right) => {
                if left == right{
                    return Type::Bool;
                }
                
            }
        };
        let left = self.format_type(&left);
        let right = self.format_type(&right);
        self.new_error(format!("Cannot apply '{}' to operands of type '{}' and '{}'.",op,left,right), span)
    }
    pub(super) fn check_logical_expr(&self,op:hir::LogicalOp,left:&hir::Expr,right:&hir::Expr,span:SourceLocation) -> Type{
        let left = self.check_expr(left, Expectation::CoercesTo(Type::Bool));
        let right = self.check_expr(right, Expectation::CoercesTo(Type::Bool));
        if left != right || left != Type::Bool || right != Type::Bool{
            let left = self.format_type(&left);
            let right = self.format_type(&right);
            self.new_error(format!("Cannot apply '{}' to operands of type '{}' and '{}'.",op,left,right), span)
        }
        else{
            Type::Bool
        }
    }
    pub(super) fn check_unary_expr(&self,op:hir::UnaryOp,operand:&hir::Expr,span:SourceLocation) -> Type{
        let operand = self.check_expr(operand, Expectation::None);
        if matches!(op,hir::UnaryOp::Negate) && (operand != Type::Float || operand != Type::Float){
            let operand = self.format_type(&operand);
            self.new_error(format!("Cannot apply '{}' to operand of type '{}'.",op,operand), span)
        }
        else{
            Type::Bool
        }
    }
}