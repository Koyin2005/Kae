use fxhash::FxHashMap;

use crate::{data_structures::IndexVec, frontend::typechecking::context::TypeContext, middle::mir::{self, Block, BlockId, Body, Terminator}};
pub mod simplify_cfg;
pub mod const_branch;
pub mod remove_unreachable_branches;
pub mod const_prop;
pub trait MirPass {
    fn run_pass(&self, ctxt: &TypeContext, body:&mut Body);
}
pub struct Patch{
    ///Maps the extra basic blocks to the new basic blocks
    extra_block_map : FxHashMap<BlockId,BlockId>,
    new_blocks : IndexVec<BlockId,Block>,
    new_terminators : FxHashMap<BlockId,Terminator>,

}
impl Patch{
    pub fn new() -> Self{
        Patch { extra_block_map: Default::default(), new_blocks: Default::default(),
        new_terminators:Default::default() }
    }

    pub fn add_block(&mut self, new_block: Block)  -> BlockId{
        self.new_blocks.push(new_block)
    }
    pub fn add_terminator(&mut self, block_id: BlockId, terminator: Terminator){
        self.new_terminators.insert(block_id, terminator);
    }
    pub fn apply(mut self, body: &mut Body){
        let mut next_block_id:u32 = 0;
        let extra_block_start = BlockId(next_block_id);
        for (block_id,block) in self.new_blocks.into_iter().enumerate().map(|(block_index,block)| (BlockId(block_index as u32),block)){
            self.extra_block_map.insert(block_id, BlockId(next_block_id));
            body.blocks.push(block);
            next_block_id += 1;
        }

        for (block_id,block) in body.blocks.index_value_iter_mut(){
            let block_map = if block_id < extra_block_start{
                continue;
            }
            else{
                &mut self.extra_block_map
            };
            let terminator = block.expect_terminator_mut();
            if let Some(new_terminator) = self.new_terminators.remove(&block_id){
                *terminator = new_terminator;
            }
            match terminator{
                mir::Terminator::Assert(_,_,block_id) | mir::Terminator::Goto(block_id) => {
                    if let Some(&new_block_id) = block_map.get(block_id){
                        *block_id = new_block_id;
                    }
                },
                mir::Terminator::Switch(_,targets,otherwise) => {
                    for (_,target) in targets{
                        if let Some(&new_block_id) = block_map.get(target){
                            *target = new_block_id;
                        }
                    }
                    if let Some(&new_block_id) = block_map.get(otherwise){
                        *otherwise = new_block_id;
                    }

                }
                mir::Terminator::Return | mir::Terminator::Unreachable => ()
            }
        }


    }
}
