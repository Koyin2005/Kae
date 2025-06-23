use std::collections::VecDeque;

use fxhash::FxHashSet;

use crate::middle::mir::{basic_blocks::BasicBlockInfo, passes::Patch, BlockId, Body};


pub struct RemoveUnreachable;


impl RemoveUnreachable{
    pub fn name(&self) -> &str{
        "Remove Unreachable"
    }
    pub fn run_pass(&mut self, body: &mut Body){
        let basic_block_info = BasicBlockInfo::new(body);
        let mut patch = Patch::new();

        let mut blocks = VecDeque::new();
        blocks.push_back(BlockId(0));
        let mut visited = FxHashSet::default();
        while let Some(next_block) = blocks.pop_front(){    
            if !visited.insert(next_block){
                continue;
            }
            for &succ in basic_block_info.successors(next_block){
                blocks.push_back(succ);
            }
        }
        for (block,_) in body.blocks.index_value_iter(){
            if !visited.contains(&block){
                patch.remove_block(block);
            }
        }
        patch.apply(body);
    }
}
