use crate::define_id;
mod lowering;
define_id!(TypeVar);
#[derive(Clone)]
pub enum Primitive {
    Int,
    String,
    Float,
    Bool,
    Never,
}
#[derive(Clone)]
pub enum Type {
    Infer(TypeVar),
    Primitive(Primitive),
    Array(Box<Type>),

}