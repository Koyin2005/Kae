use crate::frontend::{ast_lowering::hir::LiteralKind, thir};

use super::{Constructor, Pattern};

fn lower_constructor_and_fields(pattern: &thir::Pattern) -> (Constructor, Vec<Pattern>) {
    match &pattern.kind {
        &thir::PatternKind::Constant(literal) => (
            match literal {
                LiteralKind::Int(value) => Constructor::Int(value),
                LiteralKind::Bool(value) => Constructor::Bool(value),
                LiteralKind::Float(value) => Constructor::Float(value),
                LiteralKind::String(value) => Constructor::String(value),
            },
            vec![],
        ),
        thir::PatternKind::Binding(_, _, sub_pattern) => {
            if let Some(pattern) = sub_pattern {
                lower_constructor_and_fields(pattern)
            } else {
                (Constructor::Wildcard, vec![])
            }
        }
        thir::PatternKind::Tuple(fields) => (
            Constructor::Struct,
            fields.iter().map(lower_to_pattern).collect(),
        ),
        &thir::PatternKind::Variant(_, _, variant, ref fields) => (
            Constructor::Variant(variant),
            fields.iter().map(lower_to_pattern).collect(),
        ),
        thir::PatternKind::Struct(_, _, fields) => {
            let mut fields = fields.iter().collect::<Box<[_]>>();
            fields.sort_by_key(|field_pattern| field_pattern.field);
            (
                Constructor::Struct,
                fields
                    .iter()
                    .map(|field| lower_to_pattern(&field.pattern))
                    .collect::<Vec<Pattern>>(),
            )
        }
        thir::PatternKind::Wildcard => (Constructor::Wildcard, vec![]),
    }
}
pub fn lower_to_pattern(pattern: &thir::Pattern) -> Pattern {
    let (constructor, fields) = lower_constructor_and_fields(pattern);
    Pattern {
        ty: pattern.ty.clone(),
        constructor,
        fields,
    }
}
