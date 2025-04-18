use crate::frontend::tokenizing::SourceLocation;
#[derive(Debug)]
pub struct TypeError;
impl TypeError{
    pub fn emit(&self,error:String,span:SourceLocation){
        eprintln!("Error on line '{}': {}",span.start_line,error);
    }
}