use std::collections::VecDeque;

use fxhash::{FxHashMap, FxHashSet};
use indexmap::{map::Entry, IndexMap};

use crate::{backend::values, data_structures::{IndexVec, IntoIndex}, frontend::{ast_lowering::hir::BinaryOp, typechecking::types::Type}, middle::mir::{self, basic_blocks::BasicBlockInfo, passes::MirPass, traversal::{self, reversed_postorder}, visitor::MutVisitor, AggregrateConstant, BlockId, Constant, ConstantKind, ConstantNumber, Local, Location, Operand, Place, PlaceProjection, RValue, Stmt, Terminator}};

pub struct ConstProp;

impl MirPass for ConstProp{
    fn name(&self) -> &str {
        "Constant-Propagation"
    }
    fn run_pass(&self, _: &crate::frontend::typechecking::context::TypeContext, body:&mut crate::middle::mir::Body) {
        let mut analysis = Analysis;
        let results= iterate_to_fixed_point(body,&mut analysis);
        for (block,mut state) in results.into_iter_enumerated(){
            for (i,stmt) in body.blocks[block].stmts.iter().enumerate(){
                analysis.handle_statement(stmt, &mut state);
                
            }
        }
        let mut patch = ConstPatch::new();
        patch.visit_body(body);
    }
}
fn iterate_to_fixed_point(body:&mir::Body,mut analysis: &mut Analysis) -> (IndexVec<BlockId,IndexMap<Local,Option<Constant>>>){
    let mut queue = VecDeque::new();
    let mut visited = FxHashSet::default();
    let basic_blocks = BasicBlockInfo::new(&body);
    let mut results: IndexVec<BlockId, _> = IndexVec::from(IndexMap::new(),body.blocks.len());
    for block in traversal::reversed_postorder(&basic_blocks){
        queue.push_back(block);
        visited.insert(block);
    }
    fn join(state: &mut IndexMap<Local,Option<Constant>>, next_state: &IndexMap<Local,Option<Constant>>) -> bool{
        let mut changed = false;
        for (local,val) in next_state.iter(){
            match state.entry(*local){
                Entry::Occupied(mut occupied) => {
                    let joined = match (occupied.get_mut(),val.as_ref()){
                        (None,None) | (Some(_),None)  => false,
                        (Some(old_val),Some(new_val)) if old_val == new_val => {
                            false
                        },
                        (occupied,_) => {
                            *occupied = None;
                            true
                        }
                    };
                    changed |= joined;
                },
                Entry::Vacant(vacant) => {
                    vacant.insert(val.clone());
                    changed |= true;
                }
            }
        }
        changed
    }
    let mut state = IndexMap::new();
    while let Some(block) = queue.pop_front() {
        visited.remove(&block);
        state.clone_from(&results[block]);
        for (_,stmt) in body.blocks[block].stmts.iter().enumerate(){
            analysis.handle_statement(stmt, &mut state);
        }
        for &succ in basic_blocks.successors(block){
            if join(&mut results[succ], &state){
                if visited.insert(succ){
                    queue.push_back(succ);
                }
            }
        }
    }
    results
}
struct Analysis;
impl Analysis{
    
    fn try_constant<'a>(&self,local:Local,state:&'a IndexMap<Local,Option<Constant>>) -> Option<&'a Constant>{
        state.get(&local).and_then(|val| val.as_ref())
    }
    fn operand_as_constant<'a>(&'a self, operand:&'a Operand, state:&'a IndexMap<Local,Option<Constant>>)->Option<&'a Constant>{
        operand.as_constant().or_else(|| operand.as_place().and_then(|place| place.as_local().and_then(|local|{
            state.get(&local).and_then(|val| val.as_ref())
        })))
    }
    fn handle_rvalue(&mut self,rvalue:&RValue,state:&mut IndexMap<Local,Option<Constant>>) -> Option<Constant>{
        match rvalue{
            RValue::Use(Operand::Load(place)) => {
                match place.projections.as_ref(){
                    [] => {
                        self.try_constant(place.local, state).cloned()
                    },
                    projections => {
                        let mut val = self.try_constant(place.local, state).cloned();
                        for proj in projections{
                            match proj{
                                PlaceProjection::ConstantIndex(index) => {
                                    match val{
                                        Some(const_val) => {
                                            match const_val.kind{
                                                ConstantKind::Aggregrate(AggregrateConstant::Array(ref elements)) => {
                                                    if let Some(element) = elements.get(*index as usize){
                                                        val =  Some(element.clone());
                                                        continue;
                                                    }
                                                },
                                                _ => ()
                                            }
                                        },
                                        None => ()
                                    }
                                },
                                PlaceProjection::Field(field_index) => {
                                    match val{
                                        Some(const_val) => {
                                            match const_val.kind{
                                                ConstantKind::Aggregrate(AggregrateConstant::Tuple(ref elements)) => {
                                                    if let Some(element) = elements.get(field_index.as_index()){
                                                        val =  Some(element.clone());
                                                        continue;
                                                    }
                                                },
                                                _ => ()
                                            }
                                        },
                                        None => ()
                                    }
                                },
                                _ => ()
                            }
                            val = None;
                            break;
                        }
                        val
                    }
                }
            },
            RValue::Use(Operand::Constant(constant)) => {
                Some(constant.clone())
            },
            RValue::Array(ty,elements) => {
                elements.iter().map(|element|{
                    match element{
                        Operand::Load(place) => place.as_local().and_then(|local|{
                            self.try_constant(local, state).cloned()
                        }),
                        Operand::Constant(val) => Some(val.clone())
                    }
                }).collect::<Option<Box<[_]>>>().map(|elements|{
                    Constant{ty:Type::new_array(ty.clone()),kind:ConstantKind::Aggregrate(AggregrateConstant::Array(elements))}
                })
            },
            RValue::Len(place) => {
                place.as_local().and_then(|local|{
                    self.try_constant(local, state).and_then(|const_val|{
                        match const_val.kind{
                            ConstantKind::Aggregrate(AggregrateConstant::Array(ref elements)) => {
                                Some(ConstantNumber::Int(elements.len() as i64).into())
                            },
                            _ => None
                        }
                    })
                })
            },
            RValue::Binary(op,left_and_right) => {
                let (left,right) = left_and_right.as_ref();
                self.operand_as_constant(left,&state).and_then(|left|{
                    self.operand_as_constant(right,&state).map(|right|{
                        (left,right)
                    }).and_then(|(left,right)|{
                        match op{
                            BinaryOp::Add => {
                                let (ConstantNumber::Int(left),ConstantNumber::Int(right)) = (left.as_number()?,right.as_number()?) else {
                                    return None;
                                };
                                Some(ConstantNumber::Int(left.wrapping_add(right)).into())
                            },
                            BinaryOp::Subtract => {
                                let (ConstantNumber::Int(left),ConstantNumber::Int(right)) = (left.as_number()?,right.as_number()?) else {
                                    return None;
                                };
                                Some(ConstantNumber::Int(left.wrapping_sub(right)).into())
                            },
                            BinaryOp::Multiply => {
                                let (ConstantNumber::Int(left),ConstantNumber::Int(right)) = (left.as_number()?,right.as_number()?) else {
                                    return None;
                                };
                                Some(ConstantNumber::Int(left.wrapping_mul(right)).into())
                            },
                            BinaryOp::Divide => {
                                let (ConstantNumber::Int(left),ConstantNumber::Int(right @ ((..-1)|(1..)))) = (left.as_number()?,right.as_number()?) else {
                                    return None;
                                };
                                Some(ConstantNumber::Int(left.wrapping_div(right)).into())
                            },
                            BinaryOp::Lesser => {
                                let (ConstantNumber::Int(left),ConstantNumber::Int(right)) = (left.as_number()?,right.as_number()?) else {
                                    return None;
                                };
                                Some((left < right).into())
                            },
                            BinaryOp::Greater => {
                                let (ConstantNumber::Int(left),ConstantNumber::Int(right)) = (left.as_number()?,right.as_number()?) else {
                                    return None;
                                };
                                Some((left > right).into())
                            },
                            BinaryOp::LesserEquals => {
                                let (ConstantNumber::Int(left),ConstantNumber::Int(right)) = (left.as_number()?,right.as_number()?) else {
                                    return None;
                                };
                                Some((left <= right).into())
                            },
                            BinaryOp::GreaterEquals => {
                                let (ConstantNumber::Int(left),ConstantNumber::Int(right)) = (left.as_number()?,right.as_number()?) else {
                                    return None;
                                };
                                Some((left >= right).into())
                            },
                            BinaryOp::Equals => {
                                Some((left == right).into())
                            },
                            BinaryOp::NotEquals => {
                                Some((left != right).into())
                            }
                        }
                    })
                })
            },
            RValue::Tuple(element_types,elements) => {
                elements.iter().map(|element|{
                    match element{
                        Operand::Load(place) => place.as_local().and_then(|local|{
                            self.try_constant(local, state).cloned()
                        }),
                        Operand::Constant(val) => Some(val.clone())
                    }
                }).collect::<Option<Box<[_]>>>().map(|elements|{
                    Constant{ty:Type::new_tuple(element_types.to_vec()),kind:ConstantKind::Aggregrate(AggregrateConstant::Tuple(elements))}
                })
            }
            _ => None
        }
    }
    fn handle_statement(&mut self,stmt:&Stmt,state:&mut IndexMap<Local,Option<Constant>>){
        match stmt{
            Stmt::Assign(place,rvalue) => {
                let Some(local) = place.as_local() else {
                    return;
                };
                let const_val = self.handle_rvalue(rvalue,state);
                if let Some(const_val) = const_val{
                    state.insert(local, Some(const_val));
                }

            },
            Stmt::Print(_) | Stmt::Nop => {}
        }
    }
    fn handle_terminator(&mut self,block: BlockId, basic_blocks:&BasicBlockInfo, terminator: &Terminator, state:&mut IndexMap<Local,Option<Constant>>) -> Box<[BlockId]>{
        match terminator{
            Terminator::Switch(operand,targets,otherwise) => {
                if 
                let Some(constant) = self.operand_as_constant(operand, state) && true
                {
                }
            },
            _ => ()
        }
        basic_blocks.successors(block).to_vec().into_boxed_slice()
    }
}
#[derive(Debug)]
struct ConstPatch{
    assignments : FxHashMap<Location,(Local,Constant)>,
    values_in_current_block : FxHashMap<Local,Constant>
}
impl ConstPatch{
    fn new() -> Self{
        Self {  assignments: FxHashMap::default(), values_in_current_block: FxHashMap::default()}
    }
}

impl MutVisitor for ConstPatch{
    fn visit_block(&mut self, block_id: BlockId, block: &mut mir::Block) {
        self.values_in_current_block.clear();
        self.super_visit_block(block_id, block);
    }
    
    fn visit_assign(&mut self, lvalue: &mut Place, rvalue: &mut RValue, location: Location) {
        self.super_visit_assign(lvalue, rvalue, location);
    }
    fn visit_operand(&mut self, operand: &mut Operand, _: Location) {
        match operand{
            Operand::Constant(_) => (),
            Operand::Load(place) => {
                let Some(local) = place.as_local() else {
                    return;
                };
                if let Some(value) = self.values_in_current_block.get(&local){
                    *operand = Operand::Constant(value.clone());
                }
            }
        }
    }
    fn visit_stmt(&mut self, stmt: &mut Stmt, location: Location) {
        if let Some((local,val)) = self.assignments.get(&location){
            self.values_in_current_block.insert(*local, val.clone());
        }
        self.super_visit_stmt(stmt, location);   
    }
    fn visit_terminator(&mut self, terminator: &mut mir::Terminator, location: Location) {
        if let Some((local,val)) = self.assignments.get(&location){
            self.values_in_current_block.insert(*local, val.clone());
        }
        self.super_visit_terminator(terminator, location);
        match terminator{
            mir::Terminator::Switch(Operand::Constant(const_val),targets,otherwise) => {
                if let Some((_,target)) = targets.iter().copied().find(|&(target_val,_)| const_val.eval_to_scalar().is_some_and(|val| val == target_val)){
                    *terminator = mir::Terminator::Goto(target);
                }
                else{
                    *terminator = mir::Terminator::Goto(*otherwise);
                }
            },
            mir::Terminator::Assert(Operand::Constant(const_val),_,false_branch) => {
                if let Some(val) = const_val.eval_to_scalar(){
                    if val != 0{
                        *terminator = mir::Terminator::Goto(*false_branch);
                    }
                }
            }
            _ => ()
        }
    }
}