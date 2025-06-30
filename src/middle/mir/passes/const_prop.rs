
use fxhash::FxHashMap;

use crate::{
    data_structures::IntoIndex,
    frontend::{ast_lowering::hir::BinaryOp, typechecking::types::{AdtKind, Type}},
    identifiers::FieldIndex,
    middle::mir::{
        self, const_eval::{eval_binary_op, eval_unary_op}, passes::{data_flow_analysis::{visit_reachable_results, Analysis, CompleteSet, Map, PlaceIndex, Projection, ResultVisitor, State}, MirPass}, visitor::{MutVisitor, Visitor}, AggregrateConstant, BlockId, Constant, ConstantKind, ConstantNumber, Location, Operand, Place, PlaceProjection, RValue, Stmt, Terminator
    },
};

pub struct ConstProp;
impl MirPass for ConstProp {
    fn name(&self) -> &str {
        "Constant-Propagation"
    }
    fn run_pass(
        &self,
        context: &crate::frontend::typechecking::context::TypeContext,
        body: &mut crate::middle::mir::Body,
    ) {
        let map = Map::new(body,context);
        let mut analysis = ConstAnalysis { map: &map };

        let mut patch = ConstPatch::new(&map);
        
        let results = analysis.iterate_to_fixed_point(body);
        visit_reachable_results(&mut ConstVisitor{patch:&mut patch,map:&map}, body, body.blocks.indices(), &mut analysis, results);
        patch.visit_body(body);
    }
}
struct ConstAnalysis<'a> {
    map: &'a Map,
}
impl ConstAnalysis<'_> {
    fn try_constant<'a>(&self, place: PlaceIndex, state: &'a State<CompleteSet<Constant>>) -> CompleteSet<Constant>{
        state.get(place)
    }
    fn operand_as_constant(
        &self,
        operand: &Operand,
        state: &State<CompleteSet<Constant>>,
    ) -> CompleteSet<Constant> {
        match operand{
            Operand::Constant(constant) => CompleteSet::Elem(constant.clone()),
            Operand::Load(place) => {
                self.map.get(place).map_or(CompleteSet::Top, |place|{
                    state.get(place)
                })
            }
        }
    }
    fn handle_rvalue(&mut self, rvalue: &RValue, state: &State<CompleteSet<Constant>>) -> CompleteSet<Constant> {
        match rvalue {
            RValue::Use(operand) => self.operand_as_constant(operand, state),
            RValue::Array(ty, elements) => {
                let mut const_elements = Vec::new();
                for element in elements{
                    let operand = self.operand_as_constant(element, state);
                    let CompleteSet::Elem(element) = operand else {
                        return operand;
                    };
                    const_elements.push(element);
                }
                CompleteSet::Elem(Constant { ty: Type::new_array(ty.clone()), kind: ConstantKind::Aggregrate(Box::new(AggregrateConstant::Array(const_elements.into_boxed_slice()))) })
            }
            RValue::Len(place) => {
                let Some(place) = self.map.get(place) else {
                    return CompleteSet::Top;
                };
                match self.try_constant(place, state){
                    CompleteSet::Elem(val) => {
                        let Some(AggregrateConstant::Array(elements)) = val.as_aggregrate() else {
                            return CompleteSet::Top;
                        };
                        CompleteSet::Elem(ConstantNumber::Int(elements.len() as i64).into())
                    },
                    val => val
                }
            },
            RValue::Unary(op, operand) => {
                let operand = self.operand_as_constant(operand, state);
                let CompleteSet::Elem(constant) = operand else {
                    return operand;
                };
                eval_unary_op(*op, constant).map_or(CompleteSet::Top,CompleteSet::Elem)
            },
            RValue::Binary(op, left_and_right) => {
                let (left, right) = left_and_right.as_ref();
                let left = self.operand_as_constant(left, state);
                let right = self.operand_as_constant(right, state);
                match (left,right){
                    (CompleteSet::Elem(left),CompleteSet::Elem(right)) => {
                        eval_binary_op(*op, left, right).ok().map_or(CompleteSet::Top,CompleteSet::Elem)
                    },
                    (CompleteSet::Elem(const_val),other) | (other,CompleteSet::Elem(const_val)) => {
                        let Some(ConstantNumber::Int(val)) = const_val.as_number() else {
                            return CompleteSet::Top;
                        };
                        match(op,val){
                            (BinaryOp::Multiply,0) => CompleteSet::Elem(ConstantNumber::Int(0).into()),
                            (BinaryOp::Multiply,1) => other,
                            _ => CompleteSet::Top
                        }
                    },
                    (CompleteSet::Bottom,_) | (_, CompleteSet::Bottom) => CompleteSet::Bottom,
                    (CompleteSet::Top,CompleteSet::Top) => CompleteSet::Top
                }
            }
            RValue::Tuple(element_types, elements) => {
                let mut const_fields = Vec::new();
                for operand in elements.iter().map(|operand| self.operand_as_constant(operand, state)){
                    let CompleteSet::Elem(constant) = operand else {
                        return operand;
                    };
                    const_fields.push(constant);
                }
                CompleteSet::Elem(Constant {
                    ty: Type::new_tuple(element_types.to_vec()),
                    kind: ConstantKind::Aggregrate(Box::new(AggregrateConstant::Tuple(const_fields.into_boxed_slice()))),
                })
            },
            
            RValue::Adt(adt_info, fields) => {
                let (id,generic_args,variant) = adt_info.as_ref();
                let mut const_fields = Vec::new();
                for operand in fields.iter().map(|operand| self.operand_as_constant(operand, state)){
                    let CompleteSet::Elem(constant) = operand else {
                        return operand;
                    };
                    const_fields.push(constant);
                }
                CompleteSet::Elem(Constant {
                    ty: Type::new_adt(generic_args.clone(), *id, if let Some(_) = variant { AdtKind::Enum } else { AdtKind::Struct }),
                    kind: ConstantKind::Aggregrate(Box::new(AggregrateConstant::Adt(*id, generic_args.clone(), *variant, const_fields.into_boxed_slice()))),
                })
            },
            RValue::Tag(place) => {
                let Some(place) = self.map.get(place) else {
                    return CompleteSet::Top;
                };
                let Some(tag_place) = self.map.get_projection_for(place, Projection::Tag) else {
                    return CompleteSet::Top;
                };
                state.get(tag_place)
            },
            RValue::Call(_, _) => CompleteSet::Top,
        }
    }
    fn handle_assign(&mut self, place: &Place, rvalue: &RValue, state: &mut State<CompleteSet<Constant>>){
        let Some(place_index) = self.map.get(place) else {
            return;
        };
        let flood = match rvalue{
            RValue::Adt(adt_info,fields) => {
                let (_,_,variant) = adt_info.as_ref();
                let base_place = variant.and_then(|variant| self.map.get_projection_for(place_index, Projection::Variant(variant))).unwrap_or(place_index);
                for (field,operand) in fields.index_value_iter(){
                    let Some(projection_place) = self.map.get_projection_for(base_place, Projection::Field(field)) else {
                        continue;
                    };
                    self.assign_val(state, projection_place, self.operand_as_constant(operand, state));
                }
                if let Some(variant) = variant.as_ref().copied()
                && let Some(tag) = self.map.get_projection_for(place_index, Projection::Tag){
                    self.assign_to_place(state,tag, CompleteSet::Elem(ConstantNumber::Int(variant.as_index() as i64).into()));
                }
                false
            },
            RValue::Tuple(_,fields) => {
                for (field,operand) in fields.iter().enumerate().map(|(field_index,field_operand)| (FieldIndex::new(field_index),field_operand)){
                    let Some(projection_place) = self.map.get_projection_for(place_index, Projection::Field(field)) else {
                        continue;
                    };
                    self.assign_val(state, projection_place, self.operand_as_constant(operand, state));
                }
                false
            },
            _ => true
        };
        
        let const_val = self.handle_rvalue(rvalue, state);
        if flood{
            self.assign_val(state, place_index, const_val);
        }
        else{
            self.assign_to_place(state, place_index, const_val);
        }
        

    }
    fn handle_statement(&mut self, stmt: &Stmt, state: &mut State<CompleteSet<Constant>>) {
        match stmt {
            Stmt::Assign(place, rvalue) => {
                self.handle_assign(place, rvalue,state);
            }
            Stmt::Print(_) | Stmt::Nop => {}
        }
    }
    fn assign_to_place(&mut self, state: &mut State<CompleteSet<Constant>>, place: PlaceIndex, value: CompleteSet<Constant>){
        state.insert(place, value);
    }
    fn assign_val(&mut self, state: &mut State<CompleteSet<Constant>>, place: PlaceIndex, value: CompleteSet<Constant>) {
        self.map.for_each_place_in(place, value,&mut |_,projection,value|{
            let value = match value{
                CompleteSet::Elem(value) => {
                    value
                },
                CompleteSet::Bottom => return CompleteSet::Bottom,
                CompleteSet::Top => return CompleteSet::Top
            };
            CompleteSet::Elem(match projection{
                Projection::Field(field) => {
                    let Some(AggregrateConstant::Adt(_,_,_,fields)| AggregrateConstant::Tuple(fields)) = value.as_aggregrate() else {
                        return CompleteSet::Top;
                    };
                    let Some(field) = fields.get(field.as_index()) else {
                        return CompleteSet::Top;
                    };
                    field.clone()
                },
                Projection::Tag => {
                    let Some(AggregrateConstant::Adt(_,_,Some(variant),_)) = value.as_aggregrate() else {
                        return CompleteSet::Top;
                    };
                    ConstantNumber::Int(variant.as_index() as i64).into()
                }
                Projection::Variant(_) => { 
                      value.clone()
                }
            })
        },
        &mut |place,val|{
            self.assign_to_place(state, place, val);
        }
        );
    }
    fn handle_terminator(&mut self, state: &mut State<CompleteSet<Constant>>, terminator: &Terminator) -> Box<[BlockId]>{
        match terminator{
            &Terminator::Switch(ref operand,ref targets,otherwise) => {
                if let CompleteSet::Elem(value) = self.operand_as_constant(operand, state)
                && let Some(value) = value.eval_to_scalar(){
                    for &(target_value,target) in targets{
                        if value == target_value{
                            return Box::new([target]);
                        }
                    }
                    return Box::new([otherwise]);
                }
                else{ }
            },
            Terminator::Goto(_) | Terminator::Assert(_,_,_) | Terminator::Return(_) | Terminator::Unreachable => (),
        }
        terminator.successors()
    }
}
impl<'a> Analysis for ConstAnalysis<'a>{
    type Domain = State<CompleteSet<Constant>>;
    fn bottom_value(&self) -> Self::Domain {
        State::Unreachable
    }
    fn initialize_entry_block(&mut self, state: &mut Self::Domain, body: &mir::Body){
        *state = State::new();
        for arg in body.args(){
            state.insert(self.map.get(&arg.into()).expect("Every arg should have a place"),CompleteSet::Top);
        }
    }
    fn perform_statement_effect(&mut self, stmt: &Stmt, state: &mut Self::Domain) {
        self.handle_statement(stmt, state);
    }
    fn perform_terminator_effect(&mut self, terminator: &Terminator, state: &mut Self::Domain) -> Box<[BlockId]> {
        self.handle_terminator(state, terminator)
    }

}


struct ConstVisitor<'a,'b>{
    patch : &'a mut ConstPatch<'b>,
    map: &'a Map,

}
impl<'a,'b,'c> ResultVisitor<ConstAnalysis<'a>> for ConstVisitor<'b,'c>{
    fn before_statement_effect(&mut self,location:Location,stmt:&Stmt,state:&<ConstAnalysis<'a> as Analysis>::Domain) {
        Collector{patch:self.patch,before_stmt:true,state,map:self.map}.visit_stmt(stmt, location);
    }
    fn after_statement_effect(&mut self,location:Location,stmt:&Stmt,state:&<ConstAnalysis<'a> as Analysis>::Domain) {
        Collector{patch:self.patch,before_stmt:false,state,map:self.map}.visit_stmt(stmt, location);
    }
    fn after_terminator_effect(&mut self,location:Location,terminator:&Terminator,state:&<ConstAnalysis<'a> as Analysis>::Domain) {
        Collector{patch:self.patch,before_stmt:true,state,map:self.map}.visit_terminator(terminator, location);
    }
}
struct Collector<'a, 'b> {
    patch: &'a mut ConstPatch<'b>,
    state: &'a State<CompleteSet<Constant>>,
    before_stmt: bool,
    map: &'a Map,
}

impl Visitor for Collector<'_, '_> {
    fn visit_projection(
        &mut self,
        projection: &PlaceProjection,
        _: mir::visitor::PlaceContext,
        location: Location,
    ) {
        if !self.before_stmt {
            return;
        }
        if let PlaceProjection::Index(index) = *projection
            && let Some(index) = self.map.get(&index.into())
            && let CompleteSet::Elem(value) = self.state.get(index)
        {
            self.patch.values.insert((location, index), value);
        }
    }
    fn visit_operand(&mut self, operand: &Operand, location: Location) {
        if !self.before_stmt {
            return;
        }
        match operand {
            Operand::Constant(_) => (),
            Operand::Load(place) => {
                let Some(place) = self.map.get(place) else {
                    self.super_visit_operand(operand, location);
                    return;
                };
                if let CompleteSet::Elem(value) = self.state.get(place)
                {
                    self.patch.values.insert((location, place), value.clone());
                }
            }
        }
    }
    fn visit_assign(&mut self, lvalue: &Place, rvalue: &RValue, location: Location) {
        if !self.before_stmt {
            if let Some(place) = self.map.get(lvalue)
                && let CompleteSet::Elem(value) = self.state.get(place)
            {
                self.patch.assignments.insert(location, value);
            }
        }
        self.super_visit_assign(lvalue, rvalue, location);
    }
}
#[derive(Debug)]
struct ConstPatch<'a> {
    map: &'a Map,
    values: FxHashMap<(Location, PlaceIndex), Constant>,
    assignments: FxHashMap<Location, Constant>,
}
impl<'a> ConstPatch<'a> {
    fn new(map: &'a Map) -> Self {
        Self {
            map,
            values: FxHashMap::default(),
            assignments: FxHashMap::default(),
        }
    }
}

impl MutVisitor for ConstPatch<'_> {
    fn visit_block(&mut self, block_id: BlockId, block: &mut mir::Block) {
        self.super_visit_block(block_id, block);
    }

    fn visit_stmt(&mut self, stmt: &mut Stmt, location: Location) {
        match stmt {
            Stmt::Assign(place, rvalue) => {
                if let Some(place) = self.map.get(&place)
                    && let Some(value) = self.values.get(&(location, place))
                {
                    *rvalue = RValue::Use(Operand::Constant(value.clone()));
                }
            }
            _ => (),
        }
        self.super_visit_stmt(stmt, location);
    }
    fn visit_assign(&mut self, lvalue: &mut Place, rvalue: &mut RValue, location: Location) {
        if let Some(value) = self.assignments.get(&location) {
            *rvalue = RValue::Use(Operand::Constant(value.clone()));
        }
        self.super_visit_assign(lvalue, rvalue, location);
    }
    fn visit_projection(
        &mut self,
        projection: &mut PlaceProjection,
        context: mir::visitor::PlaceContext,
        location: Location,
    ) {
        if let PlaceProjection::Index(index) = *projection {
            if let Some(index) = self.map.get(&index.into()) {
                if let Some(value) = self.values.get(&(location, index)) {
                    if let Some(ConstantNumber::Int(val)) = value.as_number()
                        && let Ok(val) = val.try_into()
                    {
                        *projection = PlaceProjection::ConstantIndex(val);
                        return;
                    }
                }
            }
        }
        self.super_visit_projection(projection, context, location);
    }
    fn visit_operand(&mut self, operand: &mut Operand, location: Location) {
        match operand {
            Operand::Constant(_) => (),
            Operand::Load(place) => {
                let Some(place) = self.map.get(place) else {
                    self.super_visit_operand(operand, location);
                    return;
                };
                if let Some(value) = self.values.get(&(location, place)) {
                    *operand = Operand::Constant(value.clone());
                }
            }
        }
    }
    fn visit_terminator(&mut self, terminator: &mut mir::Terminator, location: Location) {
        self.super_visit_terminator(terminator, location);
        match terminator {
            mir::Terminator::Switch(Operand::Constant(const_val), targets, otherwise) => {
                if let Some((_, target)) = targets.iter().copied().find(|&(target_val, _)| {
                    const_val
                        .eval_to_scalar()
                        .is_some_and(|val| val == target_val)
                }) {
                    *terminator = mir::Terminator::Goto(target);
                } else {
                    *terminator = mir::Terminator::Goto(*otherwise);
                }
            }
            mir::Terminator::Assert(Operand::Constant(const_val), _, false_branch) => {
                if let Some(val) = const_val.eval_to_scalar() {
                    if val != 0 {
                        *terminator = mir::Terminator::Goto(*false_branch);
                    }
                }
            }
            _ => (),
        }
    }
}
