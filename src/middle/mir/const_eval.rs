use crate::{
    data_structures::IntoIndex, frontend::ast_lowering::hir::{BinaryOp, UnaryOp}, identifiers::FieldIndex, middle::mir::{AggregrateConstant, Constant, ConstantNumber}
};
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ConstEvalError {
    DivisionByZero,
    InvalidTypes,
    IndexOutofBounds{
        len:u64,
        index:u64
    }
}
pub fn eval_field(value: &Constant, index: FieldIndex) -> Result<Constant,ConstEvalError>{
    let Some(AggregrateConstant::Adt(_,_,_,fields)) = value.as_aggregrate() else{
        return Err(ConstEvalError::InvalidTypes);
    };
    fields.get(index.as_index()).ok_or_else(||{
        ConstEvalError::InvalidTypes
    }).cloned()
}
pub fn eval_index(value: &Constant, index: u64) -> Result<Constant,ConstEvalError>{
    let Some(AggregrateConstant::Array(elements)) = value.as_aggregrate() else{
        return Err(ConstEvalError::InvalidTypes);
    };
    elements.get(index as usize).ok_or_else(||{
        ConstEvalError::IndexOutofBounds { len: elements.len() as u64, index }
    }).cloned()
}
pub fn eval_unary_op(op: UnaryOp, operand: Constant) -> Result<Constant, ConstEvalError> {
    operand
        .as_number()
        .and_then(|number| match number {
            ConstantNumber::Int(val) => Some(val),
            _ => None,
        })
        .and_then(|val| match op {
            UnaryOp::Negate => val.checked_neg().map(|val| ConstantNumber::Int(val).into()),
        })
        .ok_or(ConstEvalError::InvalidTypes)
}
pub fn eval_binary_op(
    op: BinaryOp,
    left: Constant,
    right: Constant,
) -> Result<Constant, ConstEvalError> {
    match op {
        BinaryOp::Add => {
            let ConstantNumber::Int(left) = left.as_number().ok_or(ConstEvalError::InvalidTypes)?
            else {
                return Err(ConstEvalError::InvalidTypes);
            };
            let ConstantNumber::Int(right) =
                right.as_number().ok_or(ConstEvalError::InvalidTypes)?
            else {
                return Err(ConstEvalError::InvalidTypes);
            };
            Ok(ConstantNumber::Int(left.wrapping_add(right)).into())
        }
        BinaryOp::Subtract => {
            let ConstantNumber::Int(left) = left.as_number().ok_or(ConstEvalError::InvalidTypes)?
            else {
                return Err(ConstEvalError::InvalidTypes);
            };
            let ConstantNumber::Int(right) =
                right.as_number().ok_or(ConstEvalError::InvalidTypes)?
            else {
                return Err(ConstEvalError::InvalidTypes);
            };
            Ok(ConstantNumber::Int(left.wrapping_sub(right)).into())
        }
        BinaryOp::Multiply => {
            let ConstantNumber::Int(left) = left.as_number().ok_or(ConstEvalError::InvalidTypes)?
            else {
                return Err(ConstEvalError::InvalidTypes);
            };
            let ConstantNumber::Int(right) =
                right.as_number().ok_or(ConstEvalError::InvalidTypes)?
            else {
                return Err(ConstEvalError::InvalidTypes);
            };
            Ok(ConstantNumber::Int(left.wrapping_mul(right)).into())
        }
        BinaryOp::Divide => {
            let ConstantNumber::Int(left) = left.as_number().ok_or(ConstEvalError::InvalidTypes)?
            else {
                return Err(ConstEvalError::InvalidTypes);
            };
            let ConstantNumber::Int(right) =
                right.as_number().ok_or(ConstEvalError::InvalidTypes)?
            else {
                return Err(ConstEvalError::InvalidTypes);
            };
            if right == 0 {
                return Err(ConstEvalError::DivisionByZero);
            }
            Ok(ConstantNumber::Int(left.wrapping_div(right)).into())
        }
        BinaryOp::Lesser => {
            let ConstantNumber::Int(left) = left.as_number().ok_or(ConstEvalError::InvalidTypes)?
            else {
                return Err(ConstEvalError::InvalidTypes);
            };
            let ConstantNumber::Int(right) =
                right.as_number().ok_or(ConstEvalError::InvalidTypes)?
            else {
                return Err(ConstEvalError::InvalidTypes);
            };
            Ok((left < right).into())
        }
        BinaryOp::Greater => {
            let ConstantNumber::Int(left) = left.as_number().ok_or(ConstEvalError::InvalidTypes)?
            else {
                return Err(ConstEvalError::InvalidTypes);
            };
            let ConstantNumber::Int(right) =
                right.as_number().ok_or(ConstEvalError::InvalidTypes)?
            else {
                return Err(ConstEvalError::InvalidTypes);
            };
            Ok((left > right).into())
        }
        BinaryOp::LesserEquals => {
            let ConstantNumber::Int(left) = left.as_number().ok_or(ConstEvalError::InvalidTypes)?
            else {
                return Err(ConstEvalError::InvalidTypes);
            };
            let ConstantNumber::Int(right) =
                right.as_number().ok_or(ConstEvalError::InvalidTypes)?
            else {
                return Err(ConstEvalError::InvalidTypes);
            };
            Ok((left <= right).into())
        }
        BinaryOp::GreaterEquals => {
            let ConstantNumber::Int(left) = left.as_number().ok_or(ConstEvalError::InvalidTypes)?
            else {
                return Err(ConstEvalError::InvalidTypes);
            };
            let ConstantNumber::Int(right) =
                right.as_number().ok_or(ConstEvalError::InvalidTypes)?
            else {
                return Err(ConstEvalError::InvalidTypes);
            };
            Ok((left >= right).into())
        }
        BinaryOp::Equals => Ok((left == right).into()),
        BinaryOp::NotEquals => Ok((left != right).into()),
    }
}
