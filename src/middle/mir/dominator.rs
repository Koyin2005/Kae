use crate::{data_structures::{IndexVec, IntoIndex}, define_id, middle::mir::{basic_blocks::BasicBlockInfo, BlockId}};

define_id!(PreorderIndex);
pub struct Dominators{
    immediate_dominators : IndexVec<BlockId,Option<BlockId>>,
}

impl Dominators{
    ///Determines wether a dominates b
    pub fn dominates(&self,a: BlockId, mut b: BlockId) -> bool{
        loop{
            if a == BlockId::START_BLOCK{
                return true;
            }
            if b == BlockId::START_BLOCK{
                return false;
            }
            if a == b{
                return true;
            }
            else{
                let Some(idom) = self.immediate_dominators[b] else {
                    return false;
                };
                b = idom;
            }
        }
    }
}
pub fn dominators(bb_count: usize, blocks: &BasicBlockInfo) -> Dominators{  
    let mut preorder_to_real: IndexVec<PreorderIndex, BlockId> = IndexVec::new();
    let mut real_to_preorder: IndexVec<BlockId, Option<PreorderIndex>> = IndexVec::from(None, bb_count);
    let mut stack = Vec::new();
    let mut parent : IndexVec<PreorderIndex,PreorderIndex> = IndexVec::new();
    parent.push(PreorderIndex(0));
    real_to_preorder[BlockId::START_BLOCK] = Some(PreorderIndex(0));
    preorder_to_real.push(BlockId::START_BLOCK);
    stack.push((PreorderIndex(0),blocks.successors(BlockId::START_BLOCK)));
    'recurse: while let Some(&mut (node,succesors)) = stack.last_mut(){
        for &succ in succesors{
            if real_to_preorder[succ].is_none(){
                let preorder_index = preorder_to_real.push(succ);
                real_to_preorder[succ] = Some(preorder_index);
                parent.push(node);
                stack.push((preorder_index,blocks.successors(succ)));
                continue 'recurse;
            }
        }
        stack.pop();
    }
    let reachable_vertices = preorder_to_real.len();
    let mut sdom = IndexVec::from_fn(|i:PreorderIndex| i, reachable_vertices);
    let mut idom = IndexVec::<PreorderIndex,_>::from(PreorderIndex(0), reachable_vertices);
    let mut ancestor : IndexVec<PreorderIndex,Option<PreorderIndex>> = IndexVec::from(None,reachable_vertices);
    let mut buckets : IndexVec<PreorderIndex,Vec<PreorderIndex>> = IndexVec::from(vec![], reachable_vertices);
    for w in (1..reachable_vertices).map(|i| PreorderIndex::new(i)).rev(){
        for &pred in blocks.predecessors(preorder_to_real[w]){
            let Some(v) = real_to_preorder[pred] else {
                continue;
            };
            let u = eval(&mut ancestor, &sdom, v);
            if sdom[u] < sdom[w]{
                sdom[w] = sdom[u];
            }
        }
        buckets[sdom[w]].push(w);
        link(&mut ancestor, parent[w], w);
        buckets[parent[w]].retain(|&v|{
            let u = eval(&mut ancestor, &sdom, v);
            idom[v] = if sdom[u] < sdom[v]{
                u
            }
            else{
                parent[w]
            };
            false
        });
    }

    for w in (1..reachable_vertices).map(|i| PreorderIndex::new(i)){
        if idom[w] != sdom[w]{
            idom[w] = idom[idom[w]];
        }
    }
    idom[PreorderIndex(0)] = PreorderIndex(0);
    
    let mut block_idoms = IndexVec::<BlockId,_>::from(None, bb_count);
    for (index,&block) in preorder_to_real.index_value_iter(){
        block_idoms[block] = Some(preorder_to_real[idom[index]]);
    }
    Dominators { immediate_dominators: block_idoms }

}

///Finds the ancestor with the smallest sdom
fn eval(ancestor: &mut IndexVec<PreorderIndex,Option<PreorderIndex>>, sdom: &IndexVec<PreorderIndex,PreorderIndex>,mut v: PreorderIndex) -> PreorderIndex{
    let mut u = v;
    while let Some(ancestor_of_v) = ancestor[v] {
        if sdom[v] < sdom[u]{
            u = v;
        }   
        v = ancestor_of_v;
    }
    u
}

fn link(ancestor: &mut IndexVec<PreorderIndex,Option<PreorderIndex>>, v: PreorderIndex, w: PreorderIndex){
    ancestor[w] = Some(v);
}