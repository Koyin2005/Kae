use super::types::Type;

pub mod check;
pub mod env;
mod ops;


#[derive(Clone, Copy)]
pub(super) enum Expectation<'a>{
    HasType(&'a Type),
    CoercesTo(&'a Type),
    None
}

pub struct InferError;
pub struct TypeInfer(Vec<Option<Type>>);

impl TypeInfer{
    pub fn new(count:usize) -> Self{
        Self(vec![None;count])
    }

    pub fn infer(&mut self,ty1:&Type,ty2:&Type) -> Result<(),InferError>{

        match (ty1,ty2){
            (ty1,ty2) if ty1 == ty2 => Ok(()),
            (Type::Param(_,_),Type::Param(_,_)) => {
                Err(InferError)
            },
            (&Type::Param(index, _),ty2) => {
                self.0[index as usize] = Some(ty2.clone());
                Ok(())
            },
            _ => {
                Ok(())
            }
        }
    }

}