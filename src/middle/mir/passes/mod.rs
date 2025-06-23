use fxhash::{FxHashMap, FxHashSet};

use crate::{data_structures::IndexVec, middle::mir::{self, Block, BlockId, Body, Terminator}};
pub mod remove_unreachable;
pub mod simplify_cfg;
pub struct Patch{
    ///Maps the extra basic blocks to the new basic blocks
    extra_block_map : FxHashMap<BlockId,BlockId>,
    ///Maps the old basic blocks to the new basic blocks
    old_block_map : FxHashMap<BlockId,BlockId>,
    new_blocks : IndexVec<BlockId,Block>,
    blocks_to_remove : FxHashSet<BlockId>,
    new_terminators : FxHashMap<BlockId,Terminator>,

}
impl Patch{
    pub fn new() -> Self{
        Patch { extra_block_map: Default::default(), old_block_map: Default::default(), new_blocks: Default::default(), blocks_to_remove:Default::default(),
        new_terminators:Default::default() }
    }

    pub fn remove_block(&mut self, block_id: BlockId){
        self.blocks_to_remove.insert(block_id);
    }
    pub fn add_block(&mut self, new_block: Block)  -> BlockId{
        self.new_blocks.push(new_block)
    }
    pub fn add_terminator(&mut self, block_id: BlockId, terminator: Terminator){
        self.new_terminators.insert(block_id, terminator);
    }
    pub fn apply(mut self, body: &mut Body){
        let mut next_block_id:u32 = 0;
        body.blocks.retain_mut(|block_id,block| {
            if self.blocks_to_remove.contains(&block_id){
                false
            }
            else{
                self.old_block_map.insert(block_id, BlockId(next_block_id));
                if let Some(terminator) = self.new_terminators.remove(&block_id){
                    block.terminator = Some(terminator);
                }
                next_block_id += 1;
                true
            }
        });
        let extra_block_start = BlockId(next_block_id);
        for (block_id,block) in self.new_blocks.into_iter().enumerate().map(|(block_index,block)| (BlockId(block_index as u32),block)){
            self.extra_block_map.insert(block_id, BlockId(next_block_id));
            body.blocks.push(block);
            next_block_id += 1;
        }

        for (block_id,block) in body.blocks.index_value_iter_mut(){
            let block_map = if block_id < extra_block_start{
                &mut self.old_block_map
            }
            else{
                &mut self.extra_block_map
            };
            match block.expect_terminator_mut(){
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
