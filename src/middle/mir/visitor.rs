use crate::{frontend::ast_lowering::hir::{BinaryOp, UnaryOp}, middle::mir::{Block, BlockId, Body, Constant, Local, Location, Operand, Place, PlaceProjection, RValue, Stmt, Terminator}};
#[derive(Clone,Copy,PartialEq, Eq)]
pub enum PlaceContext {
    Write,
    Read
}
pub trait MutVisitor {
    fn super_visit_operand(&mut self, operand: &mut Operand, _: Location){
        match operand{
            Operand::Load(place) => {
                self.visit_place(place, PlaceContext::Read);
            },
            Operand::Constant(constant) => {
                self.visit_constant(constant);
            }
        }

    }
    fn visit_constant(&mut self, constant: &mut Constant){

    }
    fn visit_operand(&mut self, operand: &mut Operand, location: Location){
        self.super_visit_operand(operand,location);
    }
    fn super_visit_rvalue(&mut self, rvalue: &mut RValue, location: Location){
        match rvalue{
            RValue::Adt(_,operands)  => {
                operands.iter_mut().for_each(|operand| self.visit_operand(operand,location))
            },
            RValue::Array(_,operands) | 
            RValue::Tuple(_,operands) => operands.iter_mut().for_each(|operand| self.visit_operand(operand,location)),
            RValue::Binary(op,operands) => {
                let (left,right) = operands.as_mut();
                self.super_visit_binary(op, left,right,location);
            },
            RValue::Call(callee,operands) => {
                self.visit_operand(callee,location);
                operands.iter_mut().for_each(|operand| self.visit_operand(operand,location))
            },
            RValue::Use(operand) => self.visit_operand(operand,location),
            RValue::Unary(op,operand) => self.super_visit_unary(op,operand,location),
            RValue::Len(place) | RValue::Tag(place) => self.visit_place(place, PlaceContext::Read),
        }
    }
    fn visit_rvalue(&mut self, rvalue: &mut RValue, location: Location){
        self.super_visit_rvalue(rvalue,location);
    }
    fn super_visit_unary(&mut self, _: &mut UnaryOp, operand: &mut Operand, location: Location){
        self.visit_operand(operand,location);
    }
    fn visit_binary(&mut self, rvalue: &mut RValue, binary_op : &mut BinaryOp, left: &mut Operand, right: &mut Operand, location: Location){
        self.super_visit_binary(binary_op, left, right,location);
    }
    fn super_visit_binary(&mut self, _: &mut BinaryOp, left: &mut Operand, right: &mut Operand, location: Location){
        self.visit_operand(left,location);
        self.visit_operand(right,location);
    }
    fn visit_place(&mut self, place: &mut Place, context: PlaceContext){
        self.super_visit_place(place, context);
    }
    fn super_visit_projection(&mut self, projection: &mut PlaceProjection){
        match projection{
            PlaceProjection::Field(_) | PlaceProjection::Variant(_,_) => {

            },
            PlaceProjection::ConstantIndex(_) => (),
            PlaceProjection::Index(local) => {
                self.super_visit_local(local, PlaceContext::Read);
            }
        }

    }
    fn visit_projection(&mut self, projection: &mut PlaceProjection){
        self.super_visit_projection(projection);
    }
    fn super_visit_place(&mut self, place: &mut Place, context: PlaceContext){
        self.visit_local(&mut place.local, context);
        for projection in place.projections.iter_mut(){
            self.visit_projection(projection);
        }
    }
    fn visit_local(&mut self, local: &mut Local, context: PlaceContext){
        self.super_visit_local(local, context);
        
    }
    fn super_visit_assign(&mut self, lvalue: &mut Place, rvalue: &mut RValue, location: Location){
        self.visit_place(lvalue, PlaceContext::Write);
        self.visit_rvalue(rvalue,location);

    }
    fn visit_assign(&mut self, lvalue: &mut Place, rvalue: &mut RValue, location: Location){
        self.super_visit_assign(lvalue, rvalue,location);
    }
    fn super_visit_local(&mut self, _: &mut Local, _: PlaceContext) {}
    fn super_visit_stmt(&mut self, stmt: &mut Stmt, location: Location){
        match stmt{
            Stmt::Assign(lvalue,rvalue) => {
                self.visit_assign(lvalue, rvalue,location);
            },
            Stmt::Nop => (),
            Stmt::Print(operands) => {
                for operand in operands{
                    self.visit_operand(operand,location);
                }
            }
        }
    }   
    fn visit_stmt(&mut self, stmt: &mut Stmt, location: Location){
        self.super_visit_stmt(stmt,location);
    }  
    fn super_visit_terminator(&mut self, terminator: &mut Terminator, location: Location){
        match terminator{
            Terminator::Assert(condition,_,_) => {
                self.visit_operand(condition,location);
            },
            Terminator::Goto(_) | Terminator::Return | Terminator::Unreachable => (),
            Terminator::Switch(condition,_,_) => {
                self.visit_operand(condition,location);
            }
        }
    }
    fn visit_terminator(&mut self, terminator: &mut Terminator, location: Location){
        self.super_visit_terminator(terminator, location);
    }
    fn visit_block(&mut self, block_id: BlockId, block: &mut Block){
        self.super_visit_block(block_id,block);
    } 
    fn super_visit_block(&mut self, block_id: BlockId, block: &mut Block){
        for (i,stmt) in block.stmts.iter_mut().enumerate(){
            self.visit_stmt(stmt,Location { basic_block:block_id, statement_index: i });
        }
        let terminator_location = Location { basic_block: block_id, statement_index: block.stmts.len() };
        self.visit_terminator(block.expect_terminator_mut(),terminator_location);
    }
    fn super_visit_body(&mut self, body: &mut Body){
        for (id,block) in body.blocks.index_value_iter_mut(){
            self.visit_block(id,block);
        }
    }
    fn visit_body(&mut self, body: &mut Body){
        self.super_visit_body(body);
    }
}