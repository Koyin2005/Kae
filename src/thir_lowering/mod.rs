use fxhash::FxHashMap;
use indexmap::IndexMap;

use crate::{data_structures::{IndexVec, IntoIndex}, frontend::{ast_lowering::hir::{self, BodyOwner}, thir::{self, ExprId, ExprKind, FieldPattern, Pattern, PatternKind, StmtKind, Thir, ThirBody}, 
typechecking::{context::TypeContext, types::Type}}, identifiers::{BodyIndex, FieldIndex, VariableIndex}, middle::mir::{self, Block, BlockId, Body, BodyKind, BodySource, Constant, Local, LocalInfo, Mir, Operand, Place, PlaceProjection, RValue, Stmt, Terminator}};


pub struct MirBuild<'a>{
    thir : Thir,
    context:&'a TypeContext
}

impl<'a> MirBuild<'a>{
    pub fn new(thir : Thir, context: &'a TypeContext) -> Self{
        Self {  thir, context}
    }
    pub fn lower(self,body_owners : IndexVec<BodyIndex,BodyOwner>) -> Mir{
        let bodies = self.thir.bodies.into_iter().zip(body_owners.into_iter()).map(|((body,expr),owner)|{
            let (id,kind) = match owner{
                BodyOwner::AnonFunction(id) => {
                    (id,BodyKind::Anonymous)
                },
                BodyOwner::Function(id) => {

                    (id,BodyKind::Function)
                }
            };
            let params = body.params.iter().map(|param| &param.ty).cloned().collect();
            let return_type = body.exprs[expr].ty.clone();
            let source = BodySource { id, kind, params, return_type };
            BodyBuild::new(self.context,&body,source).lower_body(expr)
        }).collect();
        Mir { bodies:  bodies}
    }
}


struct BodyBuild<'a>{
    context:&'a TypeContext,
    body: &'a ThirBody,
    current_block : BlockId,
    result_body : Body,
    var_to_local : IndexMap<VariableIndex,Local>,
}
impl<'a> BodyBuild<'a>{
    fn new(context:&'a TypeContext,body:&'a ThirBody,source:BodySource) -> Self{
        Self{body:&body,context,current_block:BlockId::new(0), result_body:Body { 
                locals: IndexVec::new(),
                blocks:IndexVec::new(),
                source
            },var_to_local:IndexMap::new()
        }
    }
    fn new_block(&mut self) -> BlockId{
        self.result_body.blocks.push(Block { stmts: Vec::new(), terminator: None })
    }
    fn terminate(&mut self, terminator: Terminator) {
        self.result_body.blocks[self.current_block].terminator = Some(terminator);
    }
    fn lower_as_place(&mut self,expr:ExprId) -> Place{
        match &self.body.exprs[expr].kind{
            ExprKind::Variable(variable) => self.var_to_local[variable].into(),
            &ExprKind::Field(base,field) => {
                let place = self.lower_as_place(base);
                place.project(PlaceProjection::Field(field))
            },
            ExprKind::Index(array,index) => {
                let array = self.lower_as_place(*array);
                let index_place = self.lower_as_place(*index);
                let index = if index_place.projections.is_empty(){
                    index_place.local
                } else {
                    let temp = self.new_temporary(self.body.exprs[*index].ty.clone());
                    self.assign_stmt(temp.into(), RValue::Use(Operand::Load(index_place)));
                    temp
                };
                array.project(PlaceProjection::Index(index))
            }   
            _ => {
                self.lower_as_temp(expr).into()
            }
        }
    }
    
    fn lower_as_operand(&mut self,expr:ExprId) -> Operand{
        match &self.body.exprs[expr].kind{
            ExprKind::Literal(literal) => {
                let ty = self.body.exprs[expr].ty.clone();
                Operand::Constant(mir::Constant{
                    ty,
                    kind:match *literal {
                        hir::LiteralKind::Bool(bool) =>  mir::ConstantKind::Bool(bool),
                        hir::LiteralKind::Float(_) => todo!("Floats"),
                        hir::LiteralKind::Int(int) => mir::ConstantKind::Int(int),
                        hir::LiteralKind::String(string) => mir::ConstantKind::String(string)
                    }
                })
            },
            ExprKind::Tuple(elements) if elements.is_empty() => {
                let ty = self.body.exprs[expr].ty.clone();
                Operand::Constant(mir::Constant{
                    ty,
                    kind : mir::ConstantKind::ZeroSized
                })
            },
            ExprKind::Function(function) => {
                let ty = self.body.exprs[expr].ty.clone();
                let kind = match function.kind{
                    thir::FunctionKind::Anon => mir::FunctionKind::Anon(function.id),
                    thir::FunctionKind::Variant => mir::FunctionKind::Variant(function.id),
                    _ => mir::FunctionKind::Normal(function.id) 
                };
                Operand::Constant(mir::Constant{
                    ty,
                    kind : mir::ConstantKind::Function(kind, function.generic_args.clone())
                })
            },
            ExprKind::Builtin(generic_args,kind) => {
                let ty = self.body.exprs[expr].ty.clone();
                let kind = mir::FunctionKind::Builtin(*kind);
                Operand::Constant(mir::Constant{
                    ty,
                    kind : mir::ConstantKind::Function(kind, generic_args.clone())
                })
            },
            _ => Operand::Load(self.lower_as_place(expr)),
        }
    }
    fn lower_as_rvalue(&mut self,expr_id:ExprId) -> RValue{
        let expr = &self.body.exprs[expr_id];
        match &expr.kind{
            &ExprKind::Binary(op,left,right) => {
                let left = self.lower_as_operand(left);
                let right = self.lower_as_operand(right);
                RValue::Binary(op, Box::new((left,right)))
            },
            &ExprKind::Unary(op,operand) => {
                let operand = self.lower_as_operand(operand);
                RValue::Unary(op, operand)
            },
            ExprKind::Tuple(elements) if !elements.is_empty() => {
                let operands = elements.iter().copied().map(|element| self.lower_as_operand(element)).collect();
                RValue::Tuple(operands)
            },
            ExprKind::Call(callee,args) => {
                let callee = self.lower_as_operand(*callee);
                let args = args.iter().map(|arg| self.lower_as_operand(*arg)).collect();
                RValue::Call(callee, args)
            },
            ExprKind::Array(elements) => {
                let elements = elements.iter().copied().map(|element| self.lower_as_operand(element)).collect();
                RValue::Array(elements)
            },
            ExprKind::StructLiteral(struct_literal) => {
                let field_map = struct_literal.fields.iter().map(|field_expr| (field_expr.field,field_expr.expr)).collect::<FxHashMap<_,_>>();
                let fields = (0..struct_literal.fields.len() as u32).map(|field|{
                    let expr = field_map[&FieldIndex::new(field)];
                    self.lower_as_operand(expr)
                }).collect();
                RValue::Adt(Box::new((struct_literal.id,struct_literal.generic_args.clone(),struct_literal.variant)), fields)
            },
            ExprKind::Literal(_) | ExprKind::Block(_) | ExprKind::If(_, _, _)|
            ExprKind::Field(_,_) | 
            ExprKind::Variable(_) | ExprKind::Index(_,_) | 
            ExprKind::Assign(_,_) |
            ExprKind::Function(_)
            => RValue::Use(self.lower_as_operand(expr_id)),
            _ => todo!("The rest {:?}",expr)
        }
    }
    fn lower_let(&mut self,pattern:&Pattern, place: Place){
        match &pattern.kind{
            &PatternKind::Binding(_,variable,ref sub_pattern) => {
                let local = *self.var_to_local.get(&variable).expect("There should be a variable");
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
            PatternKind::Struct(_,_,fields) => {
                for &FieldPattern { field,ref pattern } in fields.iter(){
                    self.lower_let(pattern, place.clone().project(PlaceProjection::Field(field)));
                }
            },
            PatternKind::Wildcard => {
                let local = self.new_temporary(pattern.ty.clone());
                self.assign_stmt(local.into(), RValue::Use(Operand::Load(place)));
            },
            PatternKind::Constant(_) => (),
            PatternKind::Variant(enum_id,_,variant,fields) => {
                let id = self.context.get_variant_by_index(*enum_id, *variant).id;
                let place = place.project(PlaceProjection::Variant(self.context.ident(id).index, *variant));
                for (i,field) in fields.iter().enumerate(){
                    self.lower_let(field, place.clone().project(PlaceProjection::Field(FieldIndex::new(i as u32))));
                }
            },
        }
    }
    fn new_temporary(&mut self,ty:Type) -> Local{
        self.new_local(LocalInfo { ty })
    }
    fn new_local(&mut self,info: LocalInfo) -> Local{
        self.result_body.locals.push(info)
    }
    fn push_stmt(&mut self, stmt: Stmt){
        self.result_body.blocks[self.current_block].stmts.push(stmt);
    }
    fn assign_stmt(&mut self,lvalue: Place, rvalue : RValue ){
        self.push_stmt(Stmt::Assign(lvalue,rvalue));
    }
    fn assign_constant(&mut self, place: Place, constant: Constant){
        self.assign_stmt(place, RValue::Use(Operand::Constant(constant)));
    }
    fn assign_unit(&mut self, place: Place){
        self.assign_constant(place, Constant { ty: Type::new_unit(), kind: mir::ConstantKind::ZeroSized });
    }
    fn lower_stmt_expr(&mut self, expr: ExprId){
        match &self.body.exprs[expr].kind{
            &ExprKind::Assign(lvalue,rvalue) => {
                let lvaule = self.lower_as_place(lvalue);
                self.lower_into_place(lvaule, rvalue);
            },
            &ExprKind::Return(expr) => {
                if let Some(expr) = expr{
                    self.lower_into_place(Local::RETURN_PLACE.into(), expr);
                }
                else{
                    self.assign_unit(Local::RETURN_PLACE.into());
                }
                self.terminate(Terminator::Return);
                let next_block = self.new_block();
                self.current_block = next_block;
            },
            ExprKind::Print(args) => {
                let operands = args.iter().map(|arg| self.lower_as_operand(*arg)).collect();
                self.push_stmt(Stmt::Print(operands));
            },
            &ExprKind::While(condition,body) => {
                let condition_block = self.new_block();
                self.terminate(Terminator::Goto(condition_block));
                self.current_block = condition_block;
                let condition = self.lower_as_operand(condition);
                let body_block = self.new_block();
                let rest_block = self.new_block();
                self.terminate(Terminator::Switch(condition, Box::new([(0,rest_block)]), body_block));
                self.current_block = body_block;
                self.lower_as_temp(body);
                self.terminate(Terminator::Goto(condition_block));
                self.current_block = rest_block;
            },
            _ => {
                let temp = self.new_temporary(self.body.exprs[expr].ty.clone());
                self.lower_into_place(temp.into(),expr);
            }
        }
    }
    fn lower_stmt(&mut self,stmt:&thir::Stmt){
        match &stmt.kind{
            &StmtKind::Expr (expr) => {
                self.lower_stmt_expr(expr);
            },
            &StmtKind::Let(ref pattern,expr) => {
                self.declare_bindings(&pattern);
                match &pattern.kind{
                    &PatternKind::Binding(_,variable, None) => {
                        let local = self.var_to_local[&variable];
                        self.lower_into_place(local.into(), expr);
                    },
                    _ => {
                        let place = self.lower_as_place(expr);
                        self.lower_let(pattern, place);
                    }
                }
            }
        }

    }
    fn lower_as_temp(&mut self, expr: ExprId) -> Local{
        let local = self.new_temporary(self.body.exprs[expr].ty.clone());
        self.lower_into_place(local.into(), expr);
        local
    }
    fn lower_into_place(&mut self, place: Place, expr: ExprId){
        let ref kind = self.body.exprs[expr].kind;
        match kind{
            ExprKind::Block(id) => {
                let block = &self.body.blocks[*id];   
                for &stmt in &block.stmts{
                    self.lower_stmt(&self.body.stmts[stmt]);
                }
                if let Some(expr) = block.expr{
                    self.lower_into_place(place, expr);
                }
                else{
                    self.assign_unit(place);
                }
            },
            &ExprKind::If(condition,then_branch,else_branch) => {
                let condition = self.lower_as_operand(condition);
                let then_block = self.new_block();
                let else_block = self.new_block();
                let merge_block = self.new_block();
                self.terminate(Terminator::Switch(condition, Box::new([(0,else_block)]), then_block));
                self.current_block = then_block;
                self.lower_into_place(place.clone(), then_branch);
                self.terminate(Terminator::Goto(merge_block));
                self.current_block = else_block;
                if let Some(else_branch) = else_branch{
                    self.lower_into_place(place, else_branch);
                }
                else{
                    self.assign_unit(place);
                }
                self.terminate(Terminator::Goto(merge_block));
                self.current_block = merge_block;

            },
            &ExprKind::Logical(op,left,right) => {
                let left = self.lower_as_operand(left);
                let then_block = self.new_block();
                let else_block = self.new_block();
                let merge_block = self.new_block();

                self.terminate(Terminator::Switch(left, Box::new([(0,else_block)]), then_block));
                let (right_block,const_block,constant) = match op{
                    hir::LogicalOp::And => (then_block,else_block,false),
                    hir::LogicalOp::Or => (else_block,then_block,true)
                };
                self.current_block = right_block;
                self.lower_into_place(place.clone(), right);
                self.terminate(Terminator::Goto(merge_block));
                self.current_block = const_block;
                self.assign_constant(place, Constant::from(constant));
                self.terminate(Terminator::Goto(merge_block));
                self.current_block = merge_block;
            },
            &ExprKind::Return(_) => {
                self.lower_stmt_expr(expr);
            }, 
            &ExprKind::While(_,_)| ExprKind::Print(_) | ExprKind::Assign(_,_) =>{
                self.lower_stmt_expr(expr);
                self.assign_unit(place);
            }
            &ExprKind::NeverCast(expr) => {
                self.lower_as_temp(expr);
                if !matches!(self.body.exprs[expr].kind,ExprKind::Call{..}) {
                    self.terminate(Terminator::Unreachable);
                    let next_block = self.new_block();
                    self.current_block = next_block;
                }
            },
            ExprKind::Call(_, _) if !self.context.is_type_inhabited(&self.body.exprs[expr].ty) => {
                //Can't use lower_as_temp as that causes a stack overflow
                let rvalue = self.lower_as_rvalue(expr);
                self.assign_stmt(place, rvalue);
                self.terminate(Terminator::Unreachable);
                let next_block = self.new_block();
                self.current_block = next_block;
            },
            ExprKind::Binary(_,_,_) | 
            ExprKind::Array(_) | 
            ExprKind::StructLiteral(_) | 
            ExprKind::Unary(_,_) |
            ExprKind::Literal(_) |
            ExprKind::Tuple(_) |
            ExprKind::Variable(_) |
            ExprKind::Function(_) |
            ExprKind::Call(_,_) |
            ExprKind::Index(_, _) |
            ExprKind::Field(_,_) |
            ExprKind::Builtin(_,_) => {
                let rvalue = self.lower_as_rvalue(expr);
                self.assign_stmt(place, rvalue);
                
            },
            ExprKind::Cast(_) => todo!("Add non never casts"),
            ExprKind::Match(_,_) => todo!("Hope you like matrixes!")
        }
    }
    fn declare_bindings(&mut self, pattern:&Pattern){
        match &pattern.kind{
            &PatternKind::Binding(_,variable,ref sub_pattern) => {
                let local = self.new_local(LocalInfo { ty: pattern.ty.clone() });
                self.var_to_local.insert(variable, local);
                if let Some(sub_pattern) = sub_pattern.as_ref(){
                    self.declare_bindings(sub_pattern);
                }
            },
            PatternKind::Tuple(elements) => {
                for (_,element) in elements.iter().enumerate(){
                    self.declare_bindings(element);
                }
            },
            PatternKind::Constant(_) => (),
            PatternKind::Wildcard => (),
            PatternKind::Struct(_,_,operands) => {
                for &FieldPattern{field:_,ref pattern} in operands.iter(){
                    self.declare_bindings(pattern);
                }
            },
            PatternKind::Variant(_,_,_,fields) => {
                for element in fields.iter(){
                    self.declare_bindings(element);
                }
            }
        }
    }
    fn lower_body(mut self, expr: ExprId) -> Body{
        self.current_block = self.result_body.blocks.push(Block { stmts: Vec::new(), terminator: None });
        let return_local = self.new_local(LocalInfo { ty: self.body.exprs[expr].ty.clone() });
        for param in self.body.params.iter(){
            self.new_local(LocalInfo{ty:param.ty.clone()});
        }
        for param in self.body.params.iter(){
            match param.pattern.kind{
                PatternKind::Binding(_, _, None) => (),
                _ => self.declare_bindings(&param.pattern),
            }
        }
        self.lower_into_place(return_local.into(),expr);
        self.terminate(Terminator::Return);
        self.result_body
    }
}