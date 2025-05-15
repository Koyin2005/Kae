use crate::frontend::{ast_lowering::hir, tokenizing::SourceLocation, typechecking::types::Type};

use super::{check::TypeChecker, Expectation};

impl TypeChecker<'_>{
    pub(super) fn check_binary_expr(&mut self,op:hir::BinaryOp,left:&hir::Expr,right:&hir::Expr,span:SourceLocation) -> Type{
        let left = self.check_expr(left, Expectation::None);
        let right = self.check_expr(right, Expectation::None);
        fn operand_error(this:&TypeChecker,left:&Type,right:&Type,op:hir::BinaryOp,span: SourceLocation) -> Type{
            let left = this.format_type(left);
            let right = this.format_type(right);
            this.new_error(format!("Cannot apply '{}' to operands of type '{}' and '{}'.",op,left,right), span)
        }
        match (op,&left,&right){
            (hir::BinaryOp::Add|hir::BinaryOp::Subtract|hir::BinaryOp::Multiply|hir::BinaryOp::Divide,left,right) => {
                match (left,right) {
                    (Type::Float,Type::Float) => return Type::Float,
                    (Type::Int,Type::Int) => return Type::Int,
                    (Type::Float,Type::Error) |(Type::Error,Type::Float) => return Type::Float,
                    (Type::Int,Type::Error) |(Type::Error,Type::Int) => return Type::Int,
                    _ => operand_error(&self, left, right, op, span)
                }
            },
            (hir::BinaryOp::Lesser|hir::BinaryOp::LesserEquals|hir::BinaryOp::Greater|hir::BinaryOp::GreaterEquals,left,right) => {
                match (left,right) {
                    (Type::Float,Type::Float) | (Type::Int,Type::Int) => return Type::Bool,
                    (Type::Float,Type::Error) |(Type::Error,Type::Float) => return Type::Float,
                    (Type::Int,Type::Error) |(Type::Error,Type::Int) => return Type::Int,
                    _ => operand_error(&self, left, right, op, span)
                }

            },
            (hir::BinaryOp::Equals|hir::BinaryOp::NotEquals,left,right) if left == right => {
                Type::Bool
                
            },
            (_,left,right) => {
                operand_error(&self, left, right,op,span)
            }
        }
    }
    pub(super) fn check_logical_expr(&mut self,op:hir::LogicalOp,left:&hir::Expr,right:&hir::Expr,span:SourceLocation) -> Type{
        let left = self.check_expr(left, Expectation::CoercesTo(Type::Bool));
        let right = self.check_expr(right, Expectation::CoercesTo(Type::Bool));
        if (left != right || left != Type::Bool || right != Type::Bool) && (left != Type::Error || right != Type::Error){
            let left = self.format_type(&left);
            let right = self.format_type(&right);
            self.new_error(format!("Cannot apply '{}' to operands of type '{}' and '{}'.",op,left,right), span)
        }
        else{
            Type::Bool
        }
    }
    pub(super) fn check_unary_expr(&mut self,op:hir::UnaryOp,operand:&hir::Expr,span:SourceLocation) -> Type{
        let operand = self.check_expr(operand, Expectation::None);
        if (matches!(op,hir::UnaryOp::Negate) && (operand != Type::Float || operand != Type::Float ))|| operand != Type::Error{
            let operand = self.format_type(&operand);
            self.new_error(format!("Cannot apply '{}' to operand of type '{}'.",op,operand), span)
        }
        else{
            Type::Bool
        }
    }
}