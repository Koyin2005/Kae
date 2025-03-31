use std::collections::HashSet;

use crate::frontend::ast_lowering::hir::LiteralKind;

use super::{ typed_ast::{ConstructorKind, FieldPattern, Pattern, PatternKind}, types::Type, TypeContext};


fn is_irrefutable(pattern:&Pattern)->bool{
        match &pattern.kind{
            PatternKind::Binding(..,pattern)  => pattern.is_none() || pattern.as_ref().is_some_and(|pattern| is_irrefutable(&pattern)), 
            PatternKind::Tuple(elements) => elements.iter().all(|element| is_irrefutable(&element)),
            PatternKind::Constructor { kind:ConstructorKind::Struct(_),fields} => 
                fields.iter().all(|FieldPattern{index:_,pattern}| is_irrefutable(&pattern)),
            PatternKind::Wildcard => true,
            _  => false
        }

}


pub fn is_exhaustive(patterns:&[&Pattern],pattern_ty:&Type,type_context:&TypeContext)->bool{
    match pattern_ty{
        &Type::Enum(_,index) => {
            let mut seen_variants = HashSet::new();
            for pattern in patterns{
                if is_irrefutable(pattern){
                    return true;
                }
                if let &PatternKind::Constructor { kind:ConstructorKind::Variant(enum_index, variant), ref fields } = &pattern.kind{
                    if enum_index == index && fields.iter().all(|field|{
                        is_irrefutable(&field.pattern)
                    }){
                        seen_variants.insert(variant);
                    }
                }
            }
            return seen_variants.len() == type_context.enums[index].variants.len();
        },
        Type::Bool => {
            let mut found_true = false;
            let mut found_false = false;
            for pattern in patterns.iter(){
                if let PatternKind::Literal(LiteralKind::Bool(value)) = pattern.kind{
                    if is_irrefutable(&pattern){
                        return true;
                    }
                    if value{
                        found_true = true;
                    }
                    else{
                        found_false = true;
                    }
                }
            }
            found_true && found_false
        },
        Type::Never => true,
        _ => patterns.iter().any(|pattern| is_irrefutable(pattern))
    }
}
    
