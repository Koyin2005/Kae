use crate::frontend::parsing::ast::Symbol;

use super::{typed_ast::{PatternNode, PatternNodeKind}, types::{Type,TypeContext}};


fn is_irrefutable(pattern:&PatternNodeKind)->bool{
        match &pattern{
            PatternNodeKind::Name(..)| PatternNodeKind::Wildcard => true,
            PatternNodeKind::Tuple(elements) => elements.is_empty() || elements.iter().all(|element| is_irrefutable(&element.kind)),
            PatternNodeKind::Struct { fields,ty } => 
                fields.iter().all(|(_,field)| is_irrefutable(&field.kind)) && !matches!(ty,Type::EnumVariant {.. }),
            PatternNodeKind::Array(before, ignore, after) => ignore.is_some() && before.is_empty() && after.is_empty(),
            PatternNodeKind::Is(.., pattern) => is_irrefutable(&pattern.kind),
            _  => {
                false
            },
        }
}
pub struct PatternChecker;
impl PatternChecker{
    fn error(&self,message:String,line:u32){
        eprintln!("Error on line {} : {}",line,message);
    }
    
    pub fn collect_variables_in_pattern(pattern:&PatternNode,ty : &Type,variables:&mut Vec<(Symbol,Type)>,type_context:&TypeContext){
        match (&pattern.kind,ty){
            (PatternNodeKind::Name(name),ty) => variables.push((Symbol { content: name.clone(), location: pattern.location},ty.clone())),
            (PatternNodeKind::Tuple(elements),Type::Tuple(element_types)) =>  elements.iter().zip(element_types.iter()).for_each(|(element,ty)| Self::collect_variables_in_pattern(element,ty, variables,type_context)),
            (PatternNodeKind::Struct { fields,ty },_) => {
                fields.iter().map(|(field_name,pattern)| (pattern,ty.get_field(field_name, type_context).expect("Struct patterns have already been checked")))
                .for_each(|(pattern,ty)|{
                    Self::collect_variables_in_pattern(pattern, &ty, variables, type_context);
                });
            },
            (PatternNodeKind::Array(before, _, after),Type::Array(element_type)) => {
                before.iter().for_each(|pattern| Self::collect_variables_in_pattern(pattern, element_type, variables, type_context));
                after.iter().for_each(|pattern| Self::collect_variables_in_pattern(pattern, element_type, variables, type_context));
            },
            (PatternNodeKind::Is(name, pattern),ty) => {
                variables.push((name.clone(),Self::check_pattern_type(&pattern, ty, type_context).unwrap()));
                Self::collect_variables_in_pattern(&pattern, ty, variables, type_context);
            }
            _ => ()
        }
    }


    pub fn is_exhaustive(&self,patterns:&[&PatternNode],pattern_ty:&Type,type_context:&TypeContext)->bool{
        if patterns.iter().any(|pattern| is_irrefutable(&pattern.kind)){
            return true;
        }
        if let Type::Enum { id, .. }  = pattern_ty{
            let mut seen_variants =Vec::new();
            for pattern in patterns{
                if let PatternNodeKind::Struct { ty:Type::EnumVariant{variant_index,id:variant_id,..}, fields } = &pattern.kind{
                    if variant_id == id && fields.iter().all(|(_,pattern)| is_irrefutable(&pattern.kind)){
                        seen_variants.push(*variant_index);
                    }
                }
            }
            return seen_variants.len() == type_context.enums.get_enum(*id).variants.len();
        }
        false
    }
    
    pub fn check_irrefutable(pattern:&PatternNode) -> Result<(),&PatternNode>{
        if is_irrefutable(&pattern.kind){
            Ok(())
        }
        else{
            Err(pattern)
        }

    }
    pub fn check_pattern_type(pattern:&PatternNode,expected_type:&Type,type_context:&TypeContext)->Result<Type,Type>{
        fn unwrap<T>(result:Result<T,T>) -> T{
            match result {
                Ok(value) => value,
                Err(value) => value
            }
        }
        let ty = match &pattern.kind{
            PatternNodeKind::Int(_) => Type::Int,
            PatternNodeKind::Float(_) => Type::Float,
            PatternNodeKind::Bool(_) => Type::Bool,
            PatternNodeKind::String(_) => Type::String,
            PatternNodeKind::Name(_) | PatternNodeKind::Wildcard => expected_type.clone(),
            PatternNodeKind::Is(_, pattern) => {
                Self::check_pattern_type(&pattern, expected_type, type_context)?
            },
            PatternNodeKind::Array(before,_ ,after) => {
                if let Type::Array(element_type) = expected_type{
                    if before.iter().all(|pattern| Self::check_pattern_type(pattern, element_type, type_context).is_ok()) &&
                        after.iter().all(|after| Self::check_pattern_type(after, element_type, type_context).is_ok()){
                            expected_type.clone()
                    }
                    else{
                       return Err(expected_type.clone());
                    }
                }
                else{
                    return Err(Type::Array(Box::new(Type::Unknown)));
                }
            }
            PatternNodeKind::Tuple(elements) => {
                if let Type::Tuple(element_types) = expected_type{
                    if element_types.len() == elements.len() && element_types.iter().zip(elements.iter()).all(|(ty,pattern)|Self::check_pattern_type(pattern, ty,type_context).is_ok()){
                        expected_type.clone() 
                    }
                    else{
                        return Err(Type::Tuple(elements.iter().map(|pattern| unwrap(Self::check_pattern_type(pattern, &Type::Unknown,type_context))).collect()))
                    }
                }
                else if let Type::Unit = expected_type{
                    if elements.is_empty(){
                        Type::Unit
                    }
                    else{
                        return Err(Type::Unit);
                    }
                }
                else{
                    return Err(Type::Tuple(elements.iter().map(|pattern| unwrap(Self::check_pattern_type(pattern, &Type::Unknown,type_context))).collect()));
                }
            },
            PatternNodeKind::Struct { ty, fields } => {
                if fields.iter().all(|(field_name,field_pattern)| {
                    Self::check_pattern_type(field_pattern, &ty.get_field(field_name, type_context).expect("Can't construct struct pattern with invalid fields"), type_context).is_ok()
                }){
                    ty.clone()
                }
                else{
                    return Err(ty.clone());
                }
            }

        };
        if &ty != expected_type && !expected_type.is_unknown() &&  !matches!((expected_type,&ty),(Type::Enum { id, .. },Type::EnumVariant { id:variant_id, .. }) if *id == *variant_id){
            Self.error(format!("Expected \"{}\" got \"{}\"",expected_type,ty), pattern.location.start_line);
            return Err(ty);
            
        }
        Ok(ty)
    }
}
