use fxhash::FxHashMap;

use crate::{
    data_structures::IndexVec,
    frontend::typechecking::context::TypeContext,
    middle::mir::{
        Block, BlockId, Body, Terminator,
        basic_blocks::BasicBlockInfo,
        passes::MirPass,
        traversal::{self, Preorder},
    },
};

struct CfgSimplifier<'a> {
    basic_blocks: &'a mut IndexVec<BlockId, Block>,
    predecessors: IndexVec<BlockId, u32>,
}
impl<'a> CfgSimplifier<'a> {
    pub fn new(body: &'a mut Body) -> Self {
        let mut predecessors = IndexVec::from(0u32, body.blocks.len());
        predecessors[BlockId(0)] = 1;
        let basic_block_info = BasicBlockInfo::new(body);
        for block in Preorder::new(&basic_block_info) {
            for &succ in basic_block_info.successors(block) {
                predecessors[succ] += 1;
            }
        }
        Self {
            basic_blocks: &mut body.blocks,
            predecessors,
        }
    }
    fn take_if_simple_goto(&mut self, block: BlockId) -> Option<Terminator> {
        if self.basic_blocks[block].stmts.is_empty() {
            if let Some(Terminator::Goto(_)) = self.basic_blocks[block].terminator {
                self.basic_blocks[block].terminator.take()
            } else {
                None
            }
        } else {
            None
        }
    }
    fn simplify_goto(&mut self, start_block: &mut BlockId) -> bool {
        let mut terminators = Vec::new();
        let mut current_block = *start_block;
        while let Some(terminator) = self.take_if_simple_goto(current_block) {
            let Terminator::Goto(target) = terminator else {
                unreachable!("It should be a goto")
            };
            terminators.push((current_block, terminator));
            current_block = target;
        }
        let last = current_block;
        *start_block = last;
        let mut changed = false;
        while let Some((current_block, mut terminator)) = terminators.pop() {
            let Terminator::Goto(ref mut target) = terminator else {
                unreachable!()
            };
            changed |= *target != last;
            *target = last;
            if self.predecessors[current_block] == 1 {
                self.predecessors[current_block] = 0;
            } else {
                self.predecessors[*target] += 1;
                self.predecessors[current_block] -= 1;
            }
            self.basic_blocks[current_block].terminator = Some(terminator);
        }
        changed
    }
    fn merge_successor(
        &mut self,
        merged_blocks: &mut Vec<BlockId>,
        terminator: &mut Terminator,
    ) -> bool {
        let target = match terminator {
            Terminator::Goto(target) if self.predecessors[*target] == 1 => *target,
            _ => return false,
        };

        *terminator = match self.basic_blocks[target].terminator.take() {
            Some(terminator) => terminator,
            None => return false,
        };

        merged_blocks.push(target);
        self.predecessors[target] = 0;
        true
    }
    fn simplify(&mut self) {
        loop {
            let mut changed = false;
            for block_id in self.basic_blocks.indices() {
                if self.predecessors[block_id] == 0 {
                    continue;
                }
                let mut terminator = self.basic_blocks[block_id]
                    .terminator
                    .take()
                    .expect("There should be a terminator");
                for succ in terminator.successors_mut() {
                    changed |= self.simplify_goto(succ);
                }

                let mut inner_changed = true;
                let mut merged_blocks = Vec::new();
                while inner_changed {
                    inner_changed = false;
                    inner_changed |= self.merge_successor(&mut merged_blocks, &mut terminator);
                    changed |= inner_changed;
                }
                let statements_to_merge: usize = merged_blocks
                    .iter()
                    .map(|&block| self.basic_blocks[block].stmts.len())
                    .sum();
                if statements_to_merge > 0 {
                    let mut statements = std::mem::take(&mut self.basic_blocks[block_id].stmts);
                    statements.reserve(statements_to_merge);
                    for block in merged_blocks {
                        statements.append(&mut self.basic_blocks[block].stmts);
                    }
                    self.basic_blocks[block_id].stmts = statements;
                }

                self.basic_blocks[block_id].terminator = Some(terminator);
            }
            if !changed {
                break;
            }
        }
    }
}

pub struct SimplifyCfg;
impl MirPass for SimplifyCfg {
    fn name(&self) -> &str {
        "Simplify-Cfg"
    }
    fn run_pass(&self, _: &TypeContext, body: &mut Body) {
        CfgSimplifier::new(body).simplify();
        let reachable = traversal::reachable_as_set(&BasicBlockInfo::new(body));
        let mut replacements = FxHashMap::default();
        let mut new_id = 0u32;
        body.blocks.retain_mut(|old_block_id, _| {
            if reachable.contains(&old_block_id) {
                replacements.insert(old_block_id, BlockId(new_id));
                new_id += 1;
                true
            } else {
                false
            }
        });
        for block in body.blocks.iter_mut() {
            for succ in block.expect_terminator_mut().successors_mut() {
                *succ = replacements.get(succ).copied().unwrap_or(*succ);
            }
        }
    }
}
