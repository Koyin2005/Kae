use fxhash::FxHashSet;
use indexmap::IndexSet;

use crate::middle::mir::{BlockId, basic_blocks::BasicBlockInfo};

pub struct Preorder<'a> {
    blocks: &'a BasicBlockInfo,
    visited: FxHashSet<BlockId>,
    worklist: Vec<BlockId>,
}
impl<'a> Preorder<'a> {
    pub fn new(blocks: &'a BasicBlockInfo) -> Self {
        Self {
            blocks,
            visited: FxHashSet::default(),
            worklist: vec![BlockId(0)],
        }
    }
}

impl<'a> Iterator for Preorder<'a> {
    type Item = BlockId;
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(block) = self.worklist.pop() {
            if !self.visited.insert(block) {
                continue;
            }
            self.worklist.extend(self.blocks.successors(block));
            return Some(block);
        }
        None
    }
}

pub struct Postorder<'a> {
    blocks: &'a BasicBlockInfo,
    visited: FxHashSet<BlockId>,
    visit_stack: Vec<(BlockId, Vec<BlockId>)>,
}
impl<'a> Postorder<'a> {
    pub fn new(blocks: &'a BasicBlockInfo) -> Self {
        let mut postorder = Self {
            blocks,
            visited: FxHashSet::default(),
            visit_stack: Vec::new(),
        };
        postorder.visit(BlockId::START_BLOCK);
        postorder.traverse_succesor();
        postorder
    }

    fn visit(&mut self, block: BlockId) {
        if !self.visited.insert(block) {
            return;
        }
        self.visit_stack
            .push((block, self.blocks.successors(block).to_vec()));
    }

    fn traverse_succesor(&mut self) {
        while let Some(bb) = self
            .visit_stack
            .last_mut()
            .and_then(|(_, succs)| succs.pop())
        {
            self.visit(bb);
        }
    }
}
impl<'a> Iterator for Postorder<'a> {
    type Item = BlockId;
    fn next(&mut self) -> Option<Self::Item> {
        let (bb, _) = self.visit_stack.pop()?;
        self.traverse_succesor();
        Some(bb)
    }
}
pub fn postorder(blocks: &BasicBlockInfo) -> IndexSet<BlockId> {
    Postorder::new(blocks).collect::<IndexSet<_>>()
}
pub fn reversed_postorder(blocks: &BasicBlockInfo) -> IndexSet<BlockId> {
    let mut traversed = Postorder::new(blocks).collect::<IndexSet<_>>();
    traversed.reverse();
    traversed
}
pub fn reachable(blocks: &BasicBlockInfo) -> IndexSet<BlockId> {
    Preorder::new(blocks).collect()
}
