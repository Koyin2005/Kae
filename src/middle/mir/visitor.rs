use crate::{frontend::ast_lowering::hir::{BinaryOp, UnaryOp}, middle::mir::{Block, BlockId, Body, Constant, Local, Operand, Place, PlaceProjection, RValue, Stmt, Terminator}};
#[derive(Clone,Copy,PartialEq, Eq)]
pub enum PlaceContext {
    Write,
    Read
}
pub trait MutVisitor {
    fn super_visit_operand(&mut self, operand: &mut Operand){
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
    fn visit_operand(&mut self, operand: &mut Operand){
        self.super_visit_operand(operand);
    }
    fn super_visit_rvalue(&mut self, rvalue: &mut RValue){
        match rvalue{
            RValue::Adt(_,operands)  => {
                operands.iter_mut().for_each(|operand| self.visit_operand(operand))
            },
            RValue::Array(_,operands) | 
            RValue::Tuple(operands) => operands.iter_mut().for_each(|operand| self.visit_operand(operand)),
            RValue::Binary(op,operands) => {
                let (left,right) = operands.as_mut();
                self.super_visit_binary(op, left,right);
            },
            RValue::Call(callee,operands) => {
                self.visit_operand(callee);
                operands.iter_mut().for_each(|operand| self.visit_operand(operand))
            },
            RValue::Use(operand) => self.visit_operand(operand),
            RValue::Unary(op,operand) => self.super_visit_unary(op,operand),
            RValue::Len(place) | RValue::Tag(place) => self.visit_place(place, PlaceContext::Read),
        }
    }
    fn visit_rvalue(&mut self, rvalue: &mut RValue){
        self.super_visit_rvalue(rvalue);
    }
    fn super_visit_unary(&mut self, _: &mut UnaryOp, operand: &mut Operand){
        self.visit_operand(operand);
    }
    fn visit_binary(&mut self, rvalue: &mut RValue, binary_op : &mut BinaryOp, left: &mut Operand, right: &mut Operand){
        self.super_visit_binary(binary_op, left, right);
    }
    fn super_visit_binary(&mut self, _: &mut BinaryOp, left: &mut Operand, right: &mut Operand){
        self.visit_operand(left);
        self.visit_operand(right);
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
    fn super_visit_assign(&mut self, lvalue: &mut Place, rvalue: &mut RValue){
        self.visit_place(lvalue, PlaceContext::Write);
        self.visit_rvalue(rvalue);

    }
    fn visit_assign(&mut self, lvalue: &mut Place, rvalue: &mut RValue){
        self.super_visit_assign(lvalue, rvalue);
    }
    fn super_visit_local(&mut self, _: &mut Local, _: PlaceContext) {}
    fn super_visit_stmt(&mut self, stmt: &mut Stmt){
        match stmt{
            Stmt::Assign(lvalue,rvalue) => {
                self.visit_assign(lvalue, rvalue);
            },
            Stmt::Nop => (),
            Stmt::Print(operands) => {
                for operand in operands{
                    self.visit_operand(operand);
                }
            }
        }
    }   
    fn visit_stmt(&mut self, stmt: &mut Stmt){
        self.super_visit_stmt(stmt);
    }  
    fn visit_terminator(&mut self, terminator: &mut Terminator){
        match terminator{
            Terminator::Assert(condition,_,_) => {
                self.visit_operand(condition);
            },
            Terminator::Goto(_) | Terminator::Return | Terminator::Unreachable => (),
            Terminator::Switch(condition,_,_) => {
                self.visit_operand(condition);
            }
        }
    }
    fn visit_block(&mut self,_: BlockId, block: &mut Block){
        self.super_visit_block(block);
    } 
    fn super_visit_block(&mut self, block: &mut Block){
        for stmt in block.stmts.iter_mut(){
            self.visit_stmt(stmt);
        }
        self.visit_terminator(block.expect_terminator_mut());
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