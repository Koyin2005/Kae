use crate::{data_structures::IndexVec, frontend::thir::Thir, middle::mir::{self, Mir}};


pub struct ThirLower{
    thir : Thir
}

impl ThirLower{
    pub fn new(thir : Thir) -> Self{
        Self {  thir}
    }
    
    pub fn lower(mut self) -> Mir{
        Mir { bodies:  IndexVec::new()}
    }
}