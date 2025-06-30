use crate::{
    SymbolInterner,
    frontend::typechecking::context::TypeContext,
    middle::mir::{self, debug::DebugMir, passes::MirPass},
};

pub struct PassManager<'a> {
    interner: Option<&'a SymbolInterner>,
}

impl<'a> PassManager<'a> {
    pub fn new() -> Self {
        Self { interner: None }
    }
    pub fn new_debug(interner: &'a SymbolInterner) -> Self {
        Self {
            interner: Some(interner),
        }
    }
    pub fn run_single_pass(&self, pass: &dyn MirPass, ctxt: &TypeContext, body: &mut mir::Body) {
        if let Some(interner) = self.interner {
            println!(
                "Before running {}\n{}",
                pass.name(),
                DebugMir::new(ctxt, interner).debug_body(&body)
            );
            pass.run_pass(ctxt, body);
            println!(
                "After running {}\n{}",
                pass.name(),
                DebugMir::new(ctxt, interner).debug_body(&body)
            );
        } else {
            pass.run_pass(ctxt, body);
        }
    }
    pub fn run_passes(&self, passes: &[&dyn MirPass], ctxt: &TypeContext, body: &mut mir::Body) {
        for pass in passes {
            self.run_single_pass(*pass, ctxt, body);
        }
    }
}
