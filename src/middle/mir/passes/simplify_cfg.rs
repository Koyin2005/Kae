use fxhash::FxHashMap;

use crate::middle::mir::{passes::Patch, Body, Terminator};

pub struct SimplifyCfg;
impl SimplifyCfg{
    pub fn run_pass(&mut self, body:&mut Body){
        let mut patch = Patch::new();
        let mut block_map = FxHashMap::default();
        for (block_id,body) in body.blocks.index_value_iter(){
            if let &Terminator::Goto(target_block) = body.expect_terminator(){
                if body.stmts.is_empty(){
                    block_map.insert(block_id, target_block);
                }
            }
        }
        for mut block_id in body.blocks.indices(){
            let start_id = block_id;
            while let Some(&next_block) = block_map.get(&block_id){
                block_id = next_block;
            }
            if start_id != block_id{
                block_map.insert(start_id, block_id);
            }
        }
        for (_,body) in body.blocks.iter(){
            for block_id in body.expect_terminator_mut().blocks_mut(){
                if let Some(&new_block_id) = block_map.get(&block_id){
                    *block_id = new_block_id;
                }
            }
        }
        for (block_id,_) in block_map{
            patch.remove_block(block_id);
        }
        patch.apply(body);

    }
}