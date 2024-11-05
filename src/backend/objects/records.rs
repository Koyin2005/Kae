use crate::backend::values::Value;
#[derive(Debug,Clone)]
pub struct Record{
    pub fields : Box<[Value]>
}
