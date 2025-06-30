use crate::middle::mir::Mir;

pub struct Codegen {
    _mir: Mir,
}

impl Codegen {
    pub fn new(mir: Mir) -> Self {
        Self { _mir: mir }
    }
    pub fn generate(self) {}
}
