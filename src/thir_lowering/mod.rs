use fxhash::FxHashMap;
use indexmap::IndexMap;

use crate::{data_structures::{IndexVec, IntoIndex}, frontend::{ast_lowering::hir, thir::{self, Expr, ExprId, ExprKind, Pattern, PatternKind, StmtKind, Thir, ThirBody}, typechecking::{context::TypeContext, types::Type}}, identifiers::{FieldIndex, VariableIndex}, middle::mir::{self, Block, Body, Constant, Local, LocalKind, Mir, Operand, Place, PlaceProjection, RValue, Stmt}};


pub struct MirBuild<'a>{
    thir : Thir,
    context:&'a TypeContext
}

impl<'a> MirBuild<'a>{
    pub fn new(thir : Thir, context: &'a TypeContext) -> Self{
        Self {  thir, context}
    }
    pub fn lower(self) -> Mir{
        let bodies = self.thir.bodies.into_iter().map(|(body,expr)|{
            BodyBuild::new(self.context,&body).lower_body(expr)
        }).collect();
        Mir { bodies:  bodies}
    }
}


struct BodyBuild<'a>{
    context:&'a TypeContext,
    body: &'a ThirBody,
    result_body : Body,
    var_to_local : IndexMap<VariableIndex,Local>,
    current_stmts : Vec<Stmt>
}
impl<'a> BodyBuild<'a>{
    fn new(context:&'a TypeContext,body:&'a ThirBody) -> Self{
        Self{body:&body,context, result_body:Body { locals: IndexVec::new(), blocks:IndexVec::new()},current_stmts:Vec::new(),var_to_local:IndexMap::new()}
    }
    fn lower_as_place(&mut self,expr:&Expr) -> Place{
        match &expr.kind{
            ExprKind::Variable(variable) => self.var_to_local[variable].into(),
            &ExprKind::Field(base,field) => {
                let base = &self.body.exprs[base];
                let place = self.lower_as_place(base);
                place.project(PlaceProjection::Field(field))
            },
            ExprKind::Index(array,index) => {
                let array = self.lower_as_place(&self.body.exprs[*array]);
                let index = self.lower_as_place(&self.body.exprs[*index]);
                let index = if index.projections.is_empty(){
                    index.local
                } else {
                    let temp = self.new_temporary();
                    self.assign_stmt(temp.into(), RValue::Use(Operand::Load(index)));
                    temp
                };
                array.project(PlaceProjection::Index(index))
            }   
            _ => {
                let temp: Place = self.new_temporary().into();
                self.lower_into_place(temp.clone(), expr);
                temp
            }
        }
    }
    fn lower_as_operand(&mut self,expr:&Expr) -> Operand{
        match &expr.kind{
            ExprKind::Literal(literal) => {
                Operand::Constant(match *literal {
                    hir::LiteralKind::Bool(bool) =>  Constant::Bool(bool),
                    hir::LiteralKind::Float(_) => todo!("Floats"),
                    hir::LiteralKind::Int(int) => Constant::Int(int),
                    hir::LiteralKind::String(string) => Constant::String(string)
                })
            },
            ExprKind::Tuple(elements) if elements.is_empty() => {
                Operand::Constant(mir::Constant::ZeroSized(expr.ty.clone()))
            },
            ExprKind::Block(id) => {
                self.lower_block(&self.body.blocks[*id]).unwrap_or_else(|| Operand::Constant(mir::Constant::ZeroSized(Type::new_unit())))
            },
            ExprKind::Function(function) => {
                let kind = match function.kind{
                    thir::FunctionKind::Anon => mir::FunctionKind::Anon,
                    _ => mir::FunctionKind::Normal 
                };
                Operand::Constant(Constant::Function(function.id, kind,function.generic_args.clone()))
            },
            ExprKind::Assign(lvalue,rvalue) => {
                
                let lvalue = &self.body.exprs[*lvalue];
                let rvalue = &self.body.exprs[*rvalue];
                let lvaule = self.lower_as_place(lvalue);
                self.lower_into_place(lvaule.clone(), rvalue);
                Operand::Constant(mir::Constant::ZeroSized(expr.ty.clone()))
            }
            _ => Operand::Load(self.lower_as_place(expr)),
        }
    }
    fn lower_block(&mut self,block:&thir::Block) -> Option<Operand>{
        for &stmt in &block.stmts{
            self.lower_stmt(&self.body.stmts[stmt]);
        }
        block.expr.map(|expr| &self.body.exprs[expr]).map(|expr|{
            self.lower_as_operand(expr)
        })
    }
    fn lower_as_rvalue(&mut self,expr:&Expr) -> RValue{
        match &expr.kind{
            ExprKind::Binary(op,left,right) => {
                let left = &self.body.exprs[*left];
                let right = &self.body.exprs[*right];
                let left = self.lower_as_operand(left);
                let right = self.lower_as_operand(right);
                RValue::Binary(*op, Box::new((left,right)))
            },
            ExprKind::Unary(op,operand) => {
                let operand = self.lower_as_operand(&self.body.exprs[*operand]);
                RValue::Unary(*op, operand)
            },
            ExprKind::Tuple(elements) if !elements.is_empty() => {
                let operands = elements.iter().copied().map(|element| self.lower_as_operand(&self.body.exprs[element])).collect();
                RValue::Tuple(operands)
            },
            ExprKind::Call(callee,args) => {
                let callee = self.lower_as_operand(&self.body.exprs[*callee]);
                let args = args.iter().map(|arg| self.lower_as_operand(&self.body.exprs[*arg])).collect();
                RValue::Call(callee, args)
            },
            ExprKind::Array(elements) => {
                let elements = elements.iter().copied().map(|element| self.lower_as_operand(&self.body.exprs[element])).collect();
                RValue::Array(elements)
            },
            ExprKind::StructLiteral(struct_literal) => {
                let field_map = struct_literal.fields.iter().map(|field_expr| (field_expr.field,field_expr.expr)).collect::<FxHashMap<_,_>>();
                let fields = (0..struct_literal.fields.len() as u32).map(|field|{
                    let expr = field_map[&FieldIndex::new(field)];
                    let expr = &self.body.exprs[expr];
                    self.lower_as_operand(expr)
                }).collect();
                RValue::Adt(Box::new((struct_literal.id,struct_literal.generic_args.clone(),struct_literal.variant)), fields)
            },
            ExprKind::Block(_) | ExprKind::Field(_,_) | 
            ExprKind::Variable(_) | ExprKind::Index(_,_) | 
            ExprKind::Literal(_) | ExprKind::Assign(_,_) |
            ExprKind::Function(_)
            => RValue::Use(self.lower_as_operand(expr)),
            _ => todo!("The rest {:?}",expr)
        }
    }
    fn lower_let(&mut self,pattern:&Pattern, place: Place){
        match &pattern.kind{
            &PatternKind::Binding(_,variable,ref sub_pattern) => {
                let local = self.new_local_for_variable(variable);
                self.assign_stmt(local.into(), RValue::Use(Operand::Load(place)));
                if let Some(sub_pattern) = sub_pattern.as_ref(){
                    self.lower_let(&sub_pattern, local.into());
                }
            },
            PatternKind::Tuple(fields) => {
                for (i,field) in fields.iter().enumerate(){
                    self.lower_let(field, place.clone().project(PlaceProjection::Field(FieldIndex::new(i as u32))));
                }
            },
            PatternKind::Wildcard => {
                let local = self.new_temporary();
                self.assign_stmt(local.into(), RValue::Use(Operand::Load(place)));
            },
            PatternKind::Constant(_) => unreachable!("Can't be used here"),
            _ => todo!("{:?}",pattern),
        }
    }
    fn new_temporary(&mut self) -> Local{
        self.new_local(LocalKind::Temporary)
    }
    fn new_local_for_variable(&mut self, variable : VariableIndex) -> Local{
        let local = self.new_local(LocalKind::Variable(variable));
        self.var_to_local.insert(variable, local);
        local
    }
    fn new_local(&mut self,kind: LocalKind) -> Local{
        self.result_body.locals.push(kind)
    }
    fn assign_stmt(&mut self,lvalue: Place, rvalue : RValue ){
        self.current_stmts.push(Stmt::Assign(lvalue,rvalue));
    }
    fn lower_stmt(&mut self,stmt:&thir::Stmt){
        match &stmt.kind{
            StmtKind::Expr (expr) => {
                let expr = &self.body.exprs[*expr];
                match &expr.kind{
                    ExprKind::Assign(lvalue,rvalue) => {
                        let lvalue = &self.body.exprs[*lvalue];
                        let rvalue = &self.body.exprs[*rvalue];
                        let lvaule = self.lower_as_place(lvalue);
                        self.lower_into_place(lvaule, rvalue);
                    },
                    _ => {
                        let temp = self.new_temporary();
                        self.lower_into_place(temp.into(),expr);
                    }
                }
            },
            StmtKind::Let(pattern,expr) => {
                match &pattern.kind{
                    &PatternKind::Binding(_,variable, None) => {
                        let local = self.new_local_for_variable(variable);
                        let rvalue = self.lower_as_rvalue(&self.body.exprs[*expr]);
                        self.assign_stmt(local.into(),rvalue);
                    },
                    _ => {
                        let place = self.lower_as_place(&self.body.exprs[*expr]);
                        self.lower_let(pattern, place);
                    }
                }
            }
        }

    }
    fn lower_into_place(&mut self, place: Place, expr: &Expr){
        let rvalue = self.lower_as_rvalue(expr);
        self.assign_stmt(place, rvalue);
    }
    fn lower_body(mut self, expr: ExprId) -> Body{
        let return_local = self.new_local(LocalKind::Return);
        self.lower_into_place(return_local.into(),&self.body.exprs[expr]);
        self.result_body.blocks.push(Block { stmts: self.current_stmts, terminator: mir::Terminator::Return });
        self.result_body
    }
}