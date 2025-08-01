use crate::frontend::{ast_lowering::hir, tokenizing::SourceLocation, typechecking::types::Type};

use super::{Expectation, check::TypeChecker};

impl TypeChecker<'_> {
    pub(super) fn check_binary_expr(
        &mut self,
        op: hir::BinaryOp,
        left: &hir::Expr,
        right: &hir::Expr,
        span: SourceLocation,
    ) -> Type {
        let left = self.check_expr(left, Expectation::None);
        let right = self.check_expr(right, Expectation::None);
        fn operand_error(
            this: &TypeChecker,
            left: &Type,
            right: &Type,
            op: hir::BinaryOp,
            span: SourceLocation,
        ) -> Type {
            let left = this.format_type(left);
            let right = this.format_type(right);
            this.new_error(
                format!("Cannot apply '{op}' to operands of type '{left}' and '{right}'."),
                span,
            )
        }
        match (op, &left, &right) {
            (
                hir::BinaryOp::Add
                | hir::BinaryOp::Subtract
                | hir::BinaryOp::Multiply
                | hir::BinaryOp::Divide,
                left,
                right,
            ) => match (left, right) {
                (Type::Float, Type::Float) => Type::Float,
                (Type::Int, Type::Int) => Type::Int,
                (Type::Float, Type::Error) | (Type::Error, Type::Float) => Type::Float,
                (Type::Int, Type::Error) | (Type::Error, Type::Int) => Type::Int,
                _ => operand_error(self, left, right, op, span),
            },
            (
                hir::BinaryOp::Lesser
                | hir::BinaryOp::LesserEquals
                | hir::BinaryOp::Greater
                | hir::BinaryOp::GreaterEquals,
                left,
                right,
            ) => match (left, right) {
                (Type::Float, Type::Float)
                | (Type::Int, Type::Int)
                | (Type::Float, Type::Error)
                | (Type::Error, Type::Float)
                | (Type::Int, Type::Error)
                | (Type::Error, Type::Int) => Type::Bool,
                _ => operand_error(self, left, right, op, span),
            },
            (hir::BinaryOp::Equals | hir::BinaryOp::NotEquals, left, right) if left == right => {
                Type::Bool
            }
            (_, left, right) => operand_error(self, left, right, op, span),
        }
    }
    pub(super) fn check_logical_expr(
        &mut self,
        op: hir::LogicalOp,
        left: &hir::Expr,
        right: &hir::Expr,
        span: SourceLocation,
    ) -> Type {
        let left = self.check_expr(left, Expectation::CoercesTo(Type::Bool));
        let right = self.check_expr(right, Expectation::CoercesTo(Type::Bool));
        if (left != right || left != Type::Bool || right != Type::Bool)
            && (left != Type::Error || right != Type::Error)
        {
            let left = self.format_type(&left);
            let right = self.format_type(&right);
            self.new_error(
                format!("Cannot apply '{op}' to operands of type '{left}' and '{right}'."),
                span,
            )
        } else {
            Type::Bool
        }
    }
    pub(super) fn check_unary_expr(
        &mut self,
        op: hir::UnaryOp,
        operand: &hir::Expr,
        span: SourceLocation,
    ) -> Type {
        let operand = self.check_expr(operand, Expectation::None);

        let result_type = match (op, operand) {
            (hir::UnaryOp::Negate, ty @ (Type::Int | Type::Float)) => Ok(ty),
            (_, Type::Error) => return Type::Error,
            (_, ty) => Err(ty),
        };
        match result_type {
            Ok(ty) => ty,
            Err(operand) => {
                let operand = self.format_type(&operand);
                self.new_error(
                    format!("Cannot apply '{op}' to operand of type '{operand}'."),
                    span,
                )
            }
        }
    }
}
