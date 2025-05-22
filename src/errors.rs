use std::cell::{Cell, RefCell};

use crate::frontend::tokenizing::SourceLocation;



pub fn emit_error(msg:String,span:SourceLocation) {
    eprintln!("Error on line '{}': {}",span.start_line,msg);
}

pub struct ErrorReporter{
    had_error : Cell<bool>,
    buffer_errors : bool,
    errors : RefCell<Vec<(String,SourceLocation)>>
}
impl ErrorReporter{
    pub fn new(buffer_errors:bool) -> Self{
        Self { had_error: Cell::new(false),buffer_errors,errors:RefCell::new(Vec::new())}
    }
    pub fn error_occurred(&self) -> bool{
        self.had_error.get()
    }
    pub fn emit(&self,msg:String,span:SourceLocation){
        self.had_error.set(true);
        if self.buffer_errors{
            self.errors.borrow_mut().push((msg,span));
        }
        else{
            emit_error(msg, span);
        }
    }
    pub fn emit_all(&self){
        let mut errors = self.errors.take();
        errors.sort_by_key(|(_,span)| span.start_line);
        for (msg,span) in errors{
            emit_error(msg, span);
        }
    }
}