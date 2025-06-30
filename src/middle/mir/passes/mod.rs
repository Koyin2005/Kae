use fxhash::FxHashMap;

use crate::{
    frontend::typechecking::context::TypeContext,
    middle::mir::{BlockId, Body, Terminator},
};
pub mod const_branch;
pub mod const_prop;
pub mod data_flow_analysis;
pub mod pass_manager;
pub mod remove_unreachable_branches;
pub mod simplify_cfg;
pub trait MirPass {
    fn name(&self) -> &str;
    fn run_pass(&self, ctxt: &TypeContext, body: &mut Body);
}
#[derive(Default)]
pub struct Patch {
    new_terminators: FxHashMap<BlockId, Terminator>,
}
impl Patch {
    pub fn new() -> Self {
        Patch {
            new_terminators: Default::default(),
        }
    }
    pub fn add_terminator(&mut self, block_id: BlockId, terminator: Terminator) {
        self.new_terminators.insert(block_id, terminator);
    }
    pub fn apply(mut self, body: &mut Body) {
        for (block_id, block) in body.blocks.index_value_iter_mut() {
            let terminator = block.expect_terminator_mut();
            if let Some(new_terminator) = self.new_terminators.remove(&block_id) {
                *terminator = new_terminator;
            }
        }
    }
}
