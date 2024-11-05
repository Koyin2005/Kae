use std::collections::HashSet;

use crate::frontend::parsing::ast::{LiteralKind, ParsedPatternNode, ParsedPatternNodeKind, Symbol};

use super::{typechecker::TypeCheckFailed, typed_ast::{PatternNode, PatternNodeKind}, types::Type};


fn is_irrefutable(pattern:&PatternNodeKind)->bool{
        match &pattern{
            PatternNodeKind::Name(..) => true,

            PatternNodeKind::Tuple(elements) =>elements.is_empty() || elements.iter().all(|element| is_irrefutable(&element.kind)),
            _  => {
                false
            },
        }
}
#[derive(Hash,PartialEq,Eq,Clone)]
enum PatternConstructor{
    Unit,
    True,
    False,
    Tuple(Vec<PatternConstructor>),
    Incomplete
}

impl PatternConstructor{
    fn generate_constructors_for(ty:&Type)->HashSet<Self>{
        match ty{
            Type::Tuple(element_types) => {
                let element_constructors : Vec<_> = element_types.iter().map(Self::generate_constructors_for).collect();
                let mut result = vec![vec![]];
                for constructors in element_constructors{
                    let mut new_result = Vec::new();
                    for combination in result{
                        for constructor in &constructors{
                            let mut new_combination = combination.clone();
                            new_combination.push(constructor.clone());
                            new_result.push(new_combination);
                        }
                    }
                    result = new_result;

                }
                result.into_iter().map(PatternConstructor::Tuple).collect()
            },
            Type::Unit => {
                vec![PatternConstructor::Unit].into_iter().collect()
            },
            Type::Bool => {
                vec![PatternConstructor::True,PatternConstructor::False].into_iter().collect()
            },
            Type::Never => HashSet::new(),
            _ => vec![PatternConstructor::Incomplete].into_iter().collect()
        }
    }
}

pub struct PatternChecker;
impl PatternChecker{
    fn error(&self,message:String,line:u32){
        eprintln!("Error on line {} : {}",line,message);
    }
    
    pub fn collect_variables_in_pattern(pattern:&PatternNode,ty : &Type,variables:&mut Vec<(Symbol,Type)>){
        match (&pattern.kind,ty){
            (PatternNodeKind::Name(name),ty) => variables.push((Symbol { content: name.clone(), location: pattern.location},ty.clone())),
            (PatternNodeKind::Tuple(elements),Type::Tuple(element_types)) =>  elements.iter().zip(element_types.iter()).for_each(|(element,ty)| Self::collect_variables_in_pattern(element,ty, variables)),
            _ => ()
        }
    }


    pub fn is_exhaustive(&self,match_type : &Type,patterns:&[&PatternNode])->bool{
        if patterns.iter().any(|pattern| is_irrefutable(&pattern.kind)){
            return true;
        }

        let mut constructors = PatternConstructor::generate_constructors_for(match_type);
        println!("{}",constructors.len());
        for pattern in patterns{
            fn match_pattern(constructor:&PatternConstructor,pattern_kind:&PatternNodeKind)->bool{
                match(constructor,&pattern_kind){
                    (_,PatternNodeKind::Name(..)) => true,
                    (PatternConstructor::True,PatternNodeKind::Bool(true)) => true,
                    (PatternConstructor::False,PatternNodeKind::Bool(false)) => true,
                    (PatternConstructor::Unit,PatternNodeKind::Tuple(elements)) if elements.is_empty() => true,
                    (PatternConstructor::Tuple(element_constructors),PatternNodeKind::Tuple(elements)) => {
                        element_constructors.iter().zip(elements.iter()).all(|(constructor,pattern)|
                            match_pattern(constructor, &pattern.kind)
                        )
                    },
                   _ => false 
                }
            }
            constructors.retain(|constructor| !match_pattern(constructor, &pattern.kind));
        }
        constructors.is_empty()
    }
    pub fn get_pattern(pattern:&ParsedPatternNode) -> Result<PatternNode,TypeCheckFailed>{
        let kind = match &pattern.kind{
            ParsedPatternNodeKind::Name(name) => {
                PatternNodeKind::Name(name.clone())
            },
            ParsedPatternNodeKind::Tuple(patterns) => {
                let patterns = patterns.iter().map(Self::get_pattern).collect::<Result<_,_>>()?;
                PatternNodeKind::Tuple(patterns)
            },
            ParsedPatternNodeKind::Literal(literal) => {
                match literal{
                    LiteralKind::Int(int) => {
                        PatternNodeKind::Int(*int)
                    },
                    LiteralKind::Float(float) => {
                        PatternNodeKind::Float(*float)
                    },
                    LiteralKind::Bool(bool) => {
                        PatternNodeKind::Bool(*bool)
                    },
                    LiteralKind::String(string) => {
                        PatternNodeKind::String(string.clone())
                    }
                }
            }
        };
        Ok(PatternNode { location:pattern.location,kind })
    }
    pub fn check_irrefutable(pattern:&PatternNode) -> Result<(),&PatternNode>{
        match &pattern.kind{
            PatternNodeKind::Name(..) => Ok(()),
            PatternNodeKind::Tuple(elements) => elements.iter().try_for_each(|element| Self::check_irrefutable(element)),
            _  => {
                Err(pattern)
            },
        }

    }
    pub fn check_pattern_type(pattern:&PatternNode,expected_type:&Type)->Result<Type,Type>{
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
            PatternNodeKind::Name(_) => expected_type.clone(),
            PatternNodeKind::Tuple(elements) => {
                if let Type::Tuple(element_types) = expected_type{
                    if element_types.len() == elements.len() && element_types.iter().zip(elements.iter()).all(|(ty,pattern)| Self::check_pattern_type(pattern, ty).is_ok()){
                        expected_type.clone() 
                    }
                    else{
                        return Err(Type::Tuple(elements.iter().map(|pattern| unwrap(Self::check_pattern_type(pattern, &Type::Unknown))).collect()))
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
                    return Err(Type::Tuple(elements.iter().map(|pattern| unwrap(Self::check_pattern_type(pattern, &Type::Unknown))).collect()));
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
