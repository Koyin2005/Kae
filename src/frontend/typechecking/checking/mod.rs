use super::types::Type;

pub mod check;
pub mod env;
mod ops;


#[derive(Clone,Debug)]
pub(super) enum Expectation{
    HasType(Type),
    CoercesTo(Type),
    None
}
impl Expectation{
    pub fn as_type(&self) -> Option<&Type>{
        if let Expectation::HasType(ty) | Expectation::CoercesTo(ty) = self{
            Some(ty)
        }
        else {
            None
        }
    }
}
#[derive(Debug)]
pub enum InferError{
    TypesNotEqual(Type,Type),

}
