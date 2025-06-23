use fxhash::FxHashMap;

use crate::middle::mir::{BlockId, Body, Terminator};

fn find_successors(basic_block: BlockId, body:&Body) -> Box<[BlockId]>{
    match body.blocks[basic_block].expect_terminator(){
        Terminator::Assert(_,_, next)|Terminator::Goto(next) => 
            Box::new([*next]),
        Terminator::Return | Terminator::Unreachable => Box::new([]),
        Terminator::Switch(_,targets,otherwise) => {
            targets.iter().map(|&(_,target)| target ).chain(std::iter::once(*otherwise)).collect()
        }
    }
}

pub struct BasicBlockInfo{
    successors : FxHashMap<BlockId,Box<[BlockId]>>,
    predecessors : FxHashMap<BlockId,Box<[BlockId]>>
}

impl BasicBlockInfo{
    pub fn new(body:&Body) -> Self{
        let mut successors = FxHashMap::default();
        for (block_id,_) in body.blocks.index_value_iter(){
            successors.insert(block_id, find_successors(block_id, body));
        }
        let mut predecessors = FxHashMap::default();
        for (&predecessor,successors) in successors.iter(){
            for &successor in successors{
                predecessors.entry(successor).or_insert(Vec::new()).push(predecessor);
            }
        }
        Self { successors, predecessors:predecessors.into_iter().map(|(predecessor,successors)| (predecessor,successors.into_boxed_slice())).collect() }
    }

    pub fn successors(&self, block: BlockId) -> &[BlockId]{
        self.successors.get(&block).as_ref().map(|succs| &succs as &[_]).unwrap_or(&[] as &[_])
    }
    pub fn predecessors(&self, block: BlockId) -> &[BlockId]{
        self.predecessors.get(&block).as_ref().map(|preds| &preds as &[_]).unwrap_or(&[] as &[_])
    }
}