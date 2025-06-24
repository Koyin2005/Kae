use fxhash::FxHashMap;

use crate::{backend::values, data_structures::{IndexVec, IntoIndex}, frontend::{ast_lowering::hir::BinaryOp, typechecking::{context::TypeContext, types::Type}}, middle::mir::{self, basic_blocks::BasicBlockInfo, passes::MirPass, visitor::{MutVisitor, PlaceContext}, AggregrateConstant, BlockId, Constant, ConstantKind, ConstantNumber, Local, Operand, Place, PlaceProjection, RValue, Stmt}};

pub struct ConstProp;

impl MirPass for ConstProp{
    fn run_pass(&self, _: &crate::frontend::typechecking::context::TypeContext, body:&mut crate::middle::mir::Body) {

        struct ConstPropPerBlock{
            const_values : IndexVec<Local,Option<Constant>>,
            blocks_to_locals : FxHashMap<BlockId,IndexVec<Local,Option<Constant>>>,
            block_info : BasicBlockInfo,
            locals : usize
        }
        impl ConstPropPerBlock{
            
            fn constant_for(&self, local: Local) -> Option<&Constant>{
                self.const_values.get(local).and_then(|const_value| const_value.as_ref())
            }
            fn as_constant<'a>(&'a self, operand: &'a Operand) -> Option<Constant>{
                match operand{
                    Operand::Load(place) => {
                        self.try_eval_place(place)
                    },
                    Operand::Constant(constant_value) => Some(constant_value.clone()),
                }
            }
            fn try_eval_place(&self, place : &Place) -> Option<Constant>{
                let mut constant_value = self.constant_for(place.local)?.clone();
                for projection in place.projections.iter(){
                    let new_value = match projection {
                        PlaceProjection::Field(field_index) => {
                            if let Constant { ty:_, kind:ConstantKind::Aggregrate(AggregrateConstant::Tuple(fields)) } = &constant_value{
                                fields.get(field_index.as_index() as usize).cloned()
                            }
                            else{
                                None
                            }
                        },
                        PlaceProjection::Index(index_local) => {
                            self.constant_for(*index_local).and_then(|constant|{
                                constant.as_number()
                            }).and_then(|constant|{
                                match constant{
                                    ConstantNumber::Int(value) => u64::try_from(value).ok(),
                                    _ => None
                                }
                            }).and_then(|constant_index|{
                                if let Constant { ty:_, kind:ConstantKind::Aggregrate(AggregrateConstant::Array(elements)) } = &constant_value{
                                    elements.get(constant_index as usize).cloned()
                                }
                                else{
                                    None
                                }
                            })

                        },
                        PlaceProjection::ConstantIndex(index) => {
                            if let Constant { ty:_, kind:ConstantKind::Aggregrate(AggregrateConstant::Array(elements)) } = &constant_value{
                                elements.get(*index as usize).cloned()
                            }
                            else{
                                None
                            }
                        },
                        PlaceProjection::Variant(_,_) => None
                    };

                    constant_value =  new_value?;
                }
                Some(constant_value)
            }
            fn try_eval_binary(&mut self,op : BinaryOp,left: &mut Operand, right: &mut Operand) -> Option<Constant>{
                if let (Some(left),Some(right)) = (self.as_constant(&left),self.as_constant(&right)){
                    if left.is_float() || right.is_float(){
                        return None;
                    }
                    match op{
                        BinaryOp::Add => {
                            let (left,right) = (left.as_number().unwrap(),right.as_number().unwrap());
                            match (left,right){
                                (ConstantNumber::Int(left),ConstantNumber::Int(right)) => {
                                    let number = ConstantNumber::Int(left.wrapping_add(right));
                                    Some(Constant::from(number))
                                },
                                (_,_) => None
                            }
                        },
                        BinaryOp::Subtract => {
                            let (left,right) = (left.as_number().unwrap(),right.as_number().unwrap());
                            match (left,right){
                                (ConstantNumber::Int(left),ConstantNumber::Int(right)) => {
                                    let number = ConstantNumber::Int(left.wrapping_sub(right));
                                    Some(number.into())
                                },
                                (_,_) => None
                            }

                        },
                        BinaryOp::Multiply => {
                            let (left,right) = (left.as_number().unwrap(),right.as_number().unwrap());
                            match (left,right){
                                (ConstantNumber::Int(left),ConstantNumber::Int(right))  => {
                                    let number = ConstantNumber::Int(left.wrapping_mul(right));
                                    Some(number.into())
                                },
                                (_,_) => None
                            }
                        },
                        BinaryOp::Divide => {
                            let (left,right) = (left.as_number().unwrap(),right.as_number().unwrap());
                            match (left,right){
                                (ConstantNumber::Int(left),ConstantNumber::Int(right)) if right != 0 => {
                                    let number = ConstantNumber::Int(left.wrapping_div(right));
                                    Some(number.into())
                                },
                                (_,_) => None
                            }

                        },
                        BinaryOp::NotEquals => {
                            let is_not_equal = left != right;
                            Some(is_not_equal.into())
                        },
                        BinaryOp::Equals => {
                            let is_equal = left == right;
                            Some(is_equal.into())
                        },
                        BinaryOp::GreaterEquals => {
                            let (left,right) = (left.as_number().unwrap(),right.as_number().unwrap());
                            let is_greater_equal = left >= right;
                            Some(is_greater_equal.into())
                        },
                        BinaryOp::LesserEquals => {
                            let (left,right) = (left.as_number().unwrap(),right.as_number().unwrap());
                            let is_lesser_equal = left <= right;
                            Some(is_lesser_equal.into())
                        },
                        BinaryOp::Lesser => {
                            let (left,right) = (left.as_number().unwrap(),right.as_number().unwrap());
                            let is_lesser = left < right;
                            Some(is_lesser.into())
                        },
                        BinaryOp::Greater => {
                            let (left,right) = (left.as_number().unwrap(),right.as_number().unwrap());
                            let is_greater = left > right;
                            Some(is_greater.into())
                        }
                    }
                }
                else{
                    None
                }

            }
        }
        impl MutVisitor for ConstPropPerBlock{
            fn visit_block(&mut self, id: BlockId, block: &mut crate::middle::mir::Block) {
                let const_values = if self.block_info.predecessors(id).len() <= 1{
                    self.blocks_to_locals.remove(&id)
                } else {
                    None
                };
                let old_values = std::mem::replace(&mut self.const_values, const_values.unwrap_or_else(|| IndexVec::from(None, self.locals)));
                self.blocks_to_locals.insert(id, old_values);
                self.super_visit_block(block);

            }
            fn visit_projection(&mut self, projection: &mut crate::middle::mir::PlaceProjection) {
                match projection{
                    PlaceProjection::Index(index) => {
                        if let Some(constant_value) = self.constant_for(*index){
                            let Some(ConstantNumber::Int(value)) = constant_value.as_number() else {
                                unreachable!("Got a non int value for a index local")
                            };
                            if value >= 0{
                                *projection = PlaceProjection::ConstantIndex(value as u64);
                            }

                        }
                    },
                    _ => self.super_visit_projection(projection),
                }
            }
            fn visit_operand(&mut self, operand: &mut Operand) {
                match operand{
                    Operand::Load(place) if place.projections.is_empty() => {
                        if let Some(const_value) = self.constant_for(place.local){
                            *operand = Operand::Constant(const_value.clone());
                            return;
                        }
                    },
                    _ => (),
                }
                self.super_visit_operand(operand)
            }
            fn visit_assign(&mut self, lvalue: &mut crate::middle::mir::Place, rvalue: &mut RValue) {
                if lvalue.projections.is_empty(){
                    let const_value = match rvalue{
                        RValue::Use(operand) => {
                            match operand{
                                Operand::Constant(constant) => {
                                    Some(constant.clone())
                                },
                                Operand::Load(place) if place.projections.is_empty() => {
                                    if let Some(const_value) = self.constant_for(place.local){
                                        Some(const_value.clone())
                                    }
                                    else{
                                        None
                                    }
                                }
                                Operand::Load(place) => {
                                    self.try_eval_place(place)
                                }
                            }
                        },
                        RValue::Binary(op,left_and_right) => {
                            let (left,right) = left_and_right.as_mut();
                            self.try_eval_binary(*op, left, right)
                        },
                        RValue::Array(ty,operands) => {
                            let const_operands = operands.iter().map(|operand|{
                                self.as_constant(operand)
                            }).collect::<Option<Box<[_]>>>();
                            const_operands.map(|operands|{
                                Constant { ty:ty.clone(), kind: mir::ConstantKind::Aggregrate(mir::AggregrateConstant::Array(operands)) }
                            })
                        },
                        RValue::Len(place) => {
                            place.as_local().and_then(|local|{
                                self.constant_for(local).and_then(|constant|{
                                    match &constant.kind{
                                        mir::ConstantKind::Aggregrate(mir::AggregrateConstant::Array(elements)) => {
                                            Some(ConstantNumber::Int(elements.len() as i64).into())
                                        },
                                        _ => unreachable!("Can't take the lenth of non array")
                                    }

                                })
                            })
                        }
                        _ => None
                    };
                    if let Some(const_value) = const_value{
                        *rvalue = RValue::Use(Operand::Constant(const_value.clone()));
                        self.const_values[lvalue.local] = Some(const_value);
                        return;
                    }
                }

                self.super_visit_assign(lvalue, rvalue);
                self.const_values[lvalue.local] = None;
            }
        }

        ConstPropPerBlock{const_values: IndexVec::from(None, body.locals.len()), locals:body.locals.len(),block_info:BasicBlockInfo::new(&body),blocks_to_locals:FxHashMap::default()}.visit_body(body);
    }
}