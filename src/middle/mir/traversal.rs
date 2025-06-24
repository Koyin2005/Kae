use fxhash::FxHashSet;
use indexmap::IndexSet;

use crate::middle::mir::{BlockId, Body};

pub struct Preorder<'a>{
    body: &'a Body,
    visited : FxHashSet<BlockId>,
    worklist : Vec<BlockId>
}
impl<'a> Preorder<'a>{
    pub fn new(body:&'a Body) -> Self{
        Self { body,visited: FxHashSet::default(), worklist: vec![BlockId(0)] }
    } 


}

impl<'a> Iterator for Preorder<'a>{
    type Item = BlockId;
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(block) = self.worklist.pop() {
            if !self.visited.insert(block){
                continue;
            }
            if let Some(terminator) = self.body.blocks[block].terminator.as_ref(){
                self.worklist.extend(terminator.successors());
            }
            return Some(block);
        }
        None
    }
}

pub fn reachable(body:&Body) -> IndexSet<BlockId>{
    let mut visited = IndexSet::default();
    let mut preorder = Preorder::new(body);
    while let Some(block) = preorder.next(){
        visited.insert(block);
    }
    visited

}