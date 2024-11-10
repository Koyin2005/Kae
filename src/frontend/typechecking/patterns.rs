use crate::frontend::parsing::ast::Symbol;

use super::{names::Structs, typed_ast::{PatternNode, PatternNodeKind}, types::Type};


fn is_irrefutable(pattern:&PatternNodeKind)->bool{
        match &pattern{
            PatternNodeKind::Name(..)| PatternNodeKind::Wildcard => true,
            PatternNodeKind::Tuple(elements) => elements.is_empty() || elements.iter().all(|element| is_irrefutable(&element.kind)),
            PatternNodeKind::Struct { fields,.. } => fields.iter().all(|(_,field)| is_irrefutable(&field.kind)),
            PatternNodeKind::Array(before, ignore, after) => ignore.is_some() && before.is_empty() && after.is_empty(),
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
    
    pub fn collect_variables_in_pattern(pattern:&PatternNode,ty : &Type,variables:&mut Vec<(Symbol,Type)>,structs:&Structs){
        match (&pattern.kind,ty){
            (PatternNodeKind::Name(name),ty) => variables.push((Symbol { content: name.clone(), location: pattern.location},ty.clone())),
            (PatternNodeKind::Tuple(elements),Type::Tuple(element_types)) =>  elements.iter().zip(element_types.iter()).for_each(|(element,ty)| Self::collect_variables_in_pattern(element,ty, variables,structs)),
            (PatternNodeKind::Struct { fields,ty },_) => {
                fields.iter().map(|(field_name,pattern)| (pattern,ty.get_field(field_name, structs).expect("Struct patterns have already been checked")))
                .for_each(|(pattern,ty)|{
                    Self::collect_variables_in_pattern(pattern, &ty, variables, structs);
                });
            },
            (PatternNodeKind::Array(before, _, after),Type::Array(element_type)) => {
                before.iter().for_each(|pattern| Self::collect_variables_in_pattern(pattern, element_type, variables, structs));
                after.iter().for_each(|pattern| Self::collect_variables_in_pattern(pattern, element_type, variables, structs));
            }
            _ => ()
        }
    }


    pub fn is_exhaustive(&self,patterns:&[&PatternNode])->bool{
        patterns.iter().any(|pattern| is_irrefutable(&pattern.kind))
    }
    
    pub fn check_irrefutable(pattern:&PatternNode) -> Result<(),&PatternNode>{
        if is_irrefutable(&pattern.kind){
            Ok(())
        }
        else{
            Err(pattern)
        }

    }
    pub fn check_pattern_type(pattern:&PatternNode,expected_type:&Type,structs:&Structs)->Result<Type,Type>{
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
            PatternNodeKind::Array(before,_ ,after) => {
                if let Type::Array(element_type) = expected_type{
                    if before.iter().all(|pattern| Self::check_pattern_type(pattern, element_type, structs).is_ok()) &&
                        after.iter().all(|after| Self::check_pattern_type(after, &element_type, structs).is_ok()){
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
                    if element_types.len() == elements.len() && element_types.iter().zip(elements.iter()).all(|(ty,pattern)|Self::check_pattern_type(pattern, ty,structs).is_ok()){
                        expected_type.clone() 
                    }
                    else{
                        return Err(Type::Tuple(elements.iter().map(|pattern| unwrap(Self::check_pattern_type(pattern, &Type::Unknown,structs))).collect()))
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
                    return Err(Type::Tuple(elements.iter().map(|pattern| unwrap(Self::check_pattern_type(pattern, &Type::Unknown,structs))).collect()));
                }
            },
            PatternNodeKind::Struct { ty, fields } => {
                if fields.iter().all(|(field_name,field_pattern)| {
                    Self::check_pattern_type(field_pattern, &ty.get_field(&field_name, structs).expect("Can't construct struct pattern with invalid fields"), structs).is_ok()
                }){
                    ty.clone()
                }
                else{
                    return Err(ty.clone());
                }
            }

        };
        if &ty != expected_type && !expected_type.is_unknown(){
            Self.error(format!("Expected \"{}\" got \"{}\"",expected_type,ty), pattern.location.start_line);
            return Err(ty);
            
        }
        Ok(ty)
    }
}
