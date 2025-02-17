use std::{alloc::Layout, collections::HashSet};
use super::{names::VariableId, typed_ast::{PatternNode, PatternNodeKind, ResolvedSymbol}, types::{Type,TypeContext}};


fn is_irrefutable(pattern:&PatternNode)->bool{
        match &pattern.kind{
            PatternNodeKind::Name(..)| PatternNodeKind::Wildcard => true,
            PatternNodeKind::Tuple(elements) => elements.is_empty() || elements.iter().all(|element| is_irrefutable(&element)),
            PatternNodeKind::Struct { fields} => 
                fields.iter().all(|(_,field)| is_irrefutable(&field)) && !matches!(pattern.ty,Type::EnumVariant {.. }),
            PatternNodeKind::Array(before, ignore, after) => ignore.is_some() && before.is_empty() && after.is_empty(),
            PatternNodeKind::Is(.., pattern) => is_irrefutable(&pattern),
            _  => {
                false
            },
        }
}

pub fn collect_bindings(pattern:&PatternNode,bindings:&mut Vec<ResolvedSymbol<VariableId>>){
    match &pattern.kind{
        &PatternNodeKind::Name(name) => bindings.push(ResolvedSymbol { id: name.clone(), location: pattern.location}),
        PatternNodeKind::Tuple(elements)=>  elements.iter().for_each(|element| collect_bindings(element, bindings)),
        PatternNodeKind::Struct { fields}=> {
            fields.iter().for_each(|(_,pattern)|{
                collect_bindings(pattern, bindings);
            });
        },
        PatternNodeKind::Array(before, _, after) => {
            before.iter().for_each(|pattern| collect_bindings(pattern, bindings));
            after.iter().for_each(|pattern| collect_bindings(pattern, bindings));
        },
        PatternNodeKind::Is(name, pattern) => {
            bindings.push(name.clone());
            collect_bindings(pattern, bindings);
        },
        PatternNodeKind::Float(_)|PatternNodeKind::Bool(_)|PatternNodeKind::Int(_)|PatternNodeKind::String(_)|PatternNodeKind::Wildcard => {
        }
    }
}


pub fn is_exhaustive(patterns:&[&PatternNode],pattern_ty:&Type,type_context:&TypeContext)->bool{
    if patterns.iter().any(|pattern| is_irrefutable(&pattern)){
        return true;
    }
    match pattern_ty{
        &Type::Enum { id,.. } => {
            let mut seen_variants = HashSet::new();
            for pattern in patterns{
                if let (PatternNodeKind::Struct { fields }, &Type::EnumVariant{variant_index,id:variant_id,..}) = (&pattern.kind,&pattern.ty){
                    if variant_id == id && fields.iter().all(|(_,pattern)| is_irrefutable(&pattern)){
                        seen_variants.insert(variant_index);
                    }
                }
            }
            return seen_variants.len() == type_context.enums.get_enum(todo!("Use correct ids")).variants.len();
        },
        &Type::EnumVariant { id, variant_index,.. } => {
            patterns.iter().any(|pattern|{
                if let (PatternNodeKind::Struct {  fields },&Type::EnumVariant{variant_index:found_variant,id:variant_id,..}) = (&pattern.kind,&pattern.ty){
                    if variant_id == id && fields.iter().all(|(_,pattern)| is_irrefutable(&pattern)) && found_variant == variant_index{
                        return true;
                    }
                }
                false
            })
        },
        Type::Bool => {
            let mut found_true = false;
            let mut found_false = false;
            for pattern in patterns.iter(){
                if let PatternNodeKind::Bool(bool) = pattern.kind{
                    if bool{
                        found_true = true;
                    }
                    else{
                        found_false = true;
                    }
                }
            }
            found_true && found_false
        }
        _ => false
    }
}
    
