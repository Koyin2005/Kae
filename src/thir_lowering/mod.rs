use fxhash::FxHashMap;
use indexmap::IndexMap;

use crate::{
    data_structures::{IndexVec, IntoIndex},
    frontend::{
        ast_lowering::hir::{self, BodyOwner},
        thir::{
            self, ExprId, ExprKind, FieldPattern, Pattern, PatternKind, StmtKind, Thir, ThirBody,
        },
        typechecking::{context::TypeContext, types::Type},
    },
    identifiers::{BodyIndex, FieldIndex, VariableIndex},
    middle::mir::{
        self, Block, BlockId, Body, BodyKind, BodySource, Constant, ConstantNumber, Local,
        LocalInfo, Mir, Operand, Place, PlaceProjection, RValue, Stmt, Terminator,
    },
};

mod matches;
pub struct MirBuild<'a> {
    thir: Thir,
    context: &'a TypeContext,
}

impl<'a> MirBuild<'a> {
    pub fn new(thir: Thir, context: &'a TypeContext) -> Self {
        Self { thir, context }
    }
    pub fn lower(self, body_owners: IndexVec<BodyIndex, BodyOwner>) -> Mir {
        let bodies = self
            .thir
            .bodies
            .into_iter()
            .zip(body_owners.into_iter())
            .map(|((body, expr), owner)| {
                let (id, kind) = match owner {
                    BodyOwner::AnonFunction(id) => (id, BodyKind::Anonymous),
                    BodyOwner::Function(id) => (id, BodyKind::Function),
                };
                let params = body.params.iter().map(|param| &param.ty).cloned().collect();
                let return_type = body.exprs[expr].ty.clone();
                let source = BodySource {
                    id,
                    kind,
                    params,
                    return_type,
                };
                BodyBuild::new(self.context, &body, source).lower_body(expr)
            })
            .collect();
        Mir { bodies: bodies }
    }
}

struct BodyBuild<'a> {
    pub context: &'a TypeContext,
    pub body: &'a ThirBody,
    pub current_block: BlockId,
    pub result_body: Body,
    var_to_local: IndexMap<VariableIndex, Local>,
}
impl<'a> BodyBuild<'a> {
    fn new(context: &'a TypeContext, body: &'a ThirBody, source: BodySource) -> Self {
        Self {
            body: &body,
            context,
            current_block: BlockId::new(0),
            result_body: Body {
                locals: IndexVec::new(),
                blocks: IndexVec::new(),
                source,
            },
            var_to_local: IndexMap::new(),
        }
    }
    pub fn new_block(&mut self) -> BlockId {
        self.result_body.blocks.push(Block {
            stmts: Vec::new(),
            terminator: None,
        })
    }
    pub fn terminate(&mut self, terminator: Terminator) {
        self.result_body.blocks[self.current_block].terminator = Some(terminator);
    }
    pub fn lower_let(&mut self, pattern: &Pattern, place: Place) {
        match &pattern.kind {
            &PatternKind::Binding(_, variable, ref sub_pattern) => {
                let local = *self
                    .var_to_local
                    .get(&variable)
                    .expect("There should be a variable");
                self.assign_stmt(local.into(), RValue::Use(Operand::Load(place)));
                if let Some(sub_pattern) = sub_pattern.as_ref() {
                    self.lower_let(&sub_pattern, local.into());
                }
            }
            PatternKind::Tuple(fields) => {
                for (i, field) in fields.iter().enumerate() {
                    self.lower_let(
                        field,
                        place
                            .clone()
                            .project(PlaceProjection::Field(FieldIndex::new(i))),
                    );
                }
            }
            PatternKind::Struct(_, _, fields) => {
                for &FieldPattern { field, ref pattern } in fields.iter() {
                    self.lower_let(
                        pattern,
                        place.clone().project(PlaceProjection::Field(field)),
                    );
                }
            }
            PatternKind::Wildcard | PatternKind::Constant(_) => (),
            PatternKind::Variant(enum_id, _, variant, fields) => {
                let id = self.context.get_variant_by_index(*enum_id, *variant).id;
                let place = place.project(PlaceProjection::Variant(
                    self.context.ident(id).index,
                    *variant,
                ));
                for (i, field) in fields.iter().enumerate() {
                    self.lower_let(
                        field,
                        place
                            .clone()
                            .project(PlaceProjection::Field(FieldIndex::new(i))),
                    );
                }
            }
        }
    }
    fn new_temporary(&mut self, ty: Type) -> Local {
        self.new_local(LocalInfo { ty })
    }
    fn new_local(&mut self, info: LocalInfo) -> Local {
        self.result_body.locals.push(info)
    }
    fn push_stmt(&mut self, stmt: Stmt) {
        self.result_body.blocks[self.current_block].stmts.push(stmt);
    }
    pub fn assign_stmt(&mut self, lvalue: Place, rvalue: RValue) {
        self.push_stmt(Stmt::Assign(lvalue, rvalue));
    }
    fn assign_constant(&mut self, place: Place, constant: Constant) {
        self.assign_stmt(place, RValue::Use(Operand::Constant(constant)));
    }
    pub fn assign_unit(&mut self, place: Place) {
        self.assign_constant(
            place,
            Constant {
                ty: Type::new_unit(),
                kind: mir::ConstantKind::ZeroSized,
            },
        );
    }
    pub fn new_temporary_for(&mut self, expr: ExprId) -> Local {
        let ty = self.body.exprs[expr].ty.clone();
        self.new_temporary(ty)
    }
    pub fn lower_as_place(&mut self, expr: ExprId) -> Place {
        match &self.body.exprs[expr].kind {
            &thir::ExprKind::Variable(variable) => self.var_to_local[&variable].into(),
            &thir::ExprKind::Field(base, field) => {
                let place = self.lower_as_place(base);
                place.project(PlaceProjection::Field(field))
            }
            &thir::ExprKind::Index(array, index) => {
                let array_place = self.lower_as_place(array);
                let index_place = self.lower_as_place(index);
                let index = if index_place.projections.is_empty() {
                    index_place.local
                } else {
                    let index_local = self.new_temporary_for(index);
                    let rvalue = RValue::Use(Operand::Load(index_place));
                    self.assign_stmt(index_local.into(), rvalue);
                    index_local
                };
                let len_local = self.new_temporary(Type::Int);
                self.assign_stmt(len_local.into(), RValue::Len(array_place.clone()));

                let is_lesser = self.new_temporary(Type::Bool);
                let index_operand = Operand::Load(index.into());
                let len_operand = Operand::Load(len_local.into());
                self.assign_stmt(
                    is_lesser.into(),
                    RValue::Binary(
                        hir::BinaryOp::Lesser,
                        Box::new((index_operand.clone(), len_operand.clone())),
                    ),
                );

                let new_block = self.new_block();
                self.terminate(Terminator::Assert(
                    Operand::Load(is_lesser.into()),
                    mir::AssertKind::ArrayBoundsCheck(index_operand.clone(), len_operand.clone()),
                    new_block,
                ));
                self.current_block = new_block;

                let is_non_negative = self.new_temporary(Type::Bool);
                self.assign_stmt(
                    is_non_negative.into(),
                    RValue::Binary(
                        hir::BinaryOp::GreaterEquals,
                        Box::new((
                            index_operand.clone(),
                            Operand::Constant(Constant {
                                ty: Type::Int,
                                kind: mir::ConstantKind::Int(0),
                            }),
                        )),
                    ),
                );

                let new_block = self.new_block();
                self.terminate(Terminator::Assert(
                    Operand::Load(is_non_negative.into()),
                    mir::AssertKind::ArrayBoundsCheck(index_operand, len_operand),
                    new_block,
                ));
                self.current_block = new_block;

                array_place.project(PlaceProjection::Index(index.into()))
            }
            _ => {
                let temp = self.new_temporary_for(expr);
                self.lower_expr(expr, Some(temp.into()));
                temp.into()
            }
        }
    }
    fn lower_as_constant(&mut self, expr: ExprId) -> Option<Constant>{match &self.body.exprs[expr].kind {
            &thir::ExprKind::Literal(literal) => {
                let kind = match literal {
                    hir::LiteralKind::Bool(value) => mir::ConstantKind::Bool(value),
                    hir::LiteralKind::Float(value) => mir::ConstantKind::Float(value),
                    hir::LiteralKind::Int(value) => mir::ConstantKind::Int(value),
                    hir::LiteralKind::String(string) => mir::ConstantKind::String(string),
                };
                Some(Constant {
                    ty: self.body.exprs[expr].ty.clone(),
                    kind,
                })
            }
            thir::ExprKind::Function(function) => {
                let kind = match function.kind {
                    thir::FunctionKind::Anon => mir::FunctionKind::Anon(function.id),
                    thir::FunctionKind::Method => mir::FunctionKind::Normal(function.id),
                    thir::FunctionKind::Normal => mir::FunctionKind::Normal(function.id),
                    thir::FunctionKind::Variant => mir::FunctionKind::Variant(function.id),
                };
                Some(Constant {
                    ty: self.body.exprs[expr].ty.clone(),
                    kind: mir::ConstantKind::Function(kind, function.generic_args.clone()),
                })
            }
            thir::ExprKind::Tuple(elements) if elements.is_empty() => Some(Constant {
                ty: self.body.exprs[expr].ty.clone(),
                kind: mir::ConstantKind::ZeroSized,
            }),
            &thir::ExprKind::Builtin(ref args, kind) => Some(Constant {
                ty: self.body.exprs[expr].ty.clone(),
                kind: mir::ConstantKind::Function(mir::FunctionKind::Builtin(kind), args.clone()),
            }),
            _ => None,
        }
    }
    fn lower_as_operand(&mut self, expr: ExprId) -> Operand {
        let constant = self.lower_as_constant(expr);
        if let Some(constant) = constant {
            Operand::Constant(constant)
        }
        else if let ExprKind::Block(block) = self.body.exprs[expr].kind{
            self.lower_block_stmts(block);
            match self.body.blocks[block].expr{
                Some(expr) => { self.lower_as_operand(expr) },
                None => { Operand::Constant(Constant::zero_sized(Type::new_unit()))}
            }
        } 
        else {    
            Operand::Load(self.lower_as_place(expr))
        }
    }
    fn lower_match_expr(
        &mut self,
        place: Option<Place>,
        _: ExprId,
        scrutinee: ExprId,
        arms: &[thir::ArmId],
    ) {
        let arms = arms.iter().copied().map(|arm| &self.body.arms[arm]);
        let scrutinee_place = self.lower_as_place(scrutinee);
        self.lower_match(place, scrutinee_place, &self.body.exprs[scrutinee].ty, arms);
    }
    fn lower_block_stmts(&mut self, id : thir::BlockId){
        let block = &self.body.blocks[id];
        for &stmt in &block.stmts {
            self.lower_stmt(&self.body.stmts[stmt]);
        }
    }
    pub fn lower_expr(&mut self, expr: ExprId, place: Option<Place>) {
        fn place_or_temporary(this: &mut BodyBuild, place: Option<Place>, expr: ExprId) -> Place {
            place.unwrap_or_else(|| this.new_temporary_for(expr).into())
        }
        match &self.body.exprs[expr].kind {
            &ExprKind::Assign(lvalue, rvalue) => {
                let lvaule = self.lower_as_place(lvalue);
                self.lower_expr(rvalue, Some(lvaule));
                if let Some(place) = place {
                    self.assign_unit(place);
                }
            }
            &ExprKind::Return(expr) => {
                let operand = match expr{
                    Some(expr) => {
                        self.lower_as_operand(expr)
                    },
                    None => {
                        Operand::Constant(Constant::zero_sized(Type::new_unit()))
                    }
                };
                self.terminate(Terminator::Return(operand));
                let next_block = self.new_block();
                self.current_block = next_block;
            }
            ExprKind::Print(args) => {
                let operands = args.iter().map(|arg| self.lower_as_operand(*arg)).collect();
                self.push_stmt(Stmt::Print(operands));
                if let Some(place) = place {
                    self.assign_unit(place);
                }
            }
            &ExprKind::While(condition, body) => {
                let condition_block = self.new_block();
                self.terminate(Terminator::Goto(condition_block));
                self.current_block = condition_block;
                let condition = self.lower_as_operand(condition);
                let body_block = self.new_block();
                let rest_block = self.new_block();
                self.terminate(Terminator::Switch(
                    condition,
                    Box::new([(0, rest_block)]),
                    body_block,
                ));
                self.current_block = body_block;
                self.lower_expr(body, None);
                self.terminate(Terminator::Goto(condition_block));
                self.current_block = rest_block;
                if let Some(place) = place {
                    self.assign_unit(place);
                }
            }
            &ExprKind::Block(id) => {
                let block = &self.body.blocks[id];
                self.lower_block_stmts(id);
                match (block.expr, place) {
                    (Some(expr), Some(place)) => {
                        self.lower_expr(expr, Some(place));
                    }
                    (None, Some(place)) => {
                        self.assign_unit(place);
                    }
                    (Some(expr), None) => {
                        let temporary = self.new_temporary(self.body.exprs[expr].ty.clone());
                        self.lower_expr(expr, Some(temporary.into()));
                    }
                    (None, None) => (),
                }
            }
            &ExprKind::If(condition, then_branch, else_branch) => {
                let condition = self.lower_as_operand(condition);
                let then_block = self.new_block();
                let else_block = self.new_block();
                let merge_block = self.new_block();
                self.terminate(Terminator::Switch(
                    condition,
                    Box::new([(0, else_block)]),
                    then_block,
                ));
                self.current_block = then_block;
                self.lower_expr(then_branch, place.clone());
                self.terminate(Terminator::Goto(merge_block));
                self.current_block = else_block;
                if let Some(else_branch) = else_branch {
                    self.lower_expr(else_branch, place);
                } else if let Some(place) = place {
                    self.assign_unit(place);
                }
                self.terminate(Terminator::Goto(merge_block));
                self.current_block = merge_block;
            }
            &ExprKind::Logical(op, left, right) => {
                let place = place_or_temporary(self, place, right);
                let left = self.lower_as_operand(left);
                let then_block = self.new_block();
                let else_block = self.new_block();
                let merge_block = self.new_block();

                self.terminate(Terminator::Switch(
                    left,
                    Box::new([(0, else_block)]),
                    then_block,
                ));
                let (right_block, const_block, constant) = match op {
                    hir::LogicalOp::And => (then_block, else_block, false),
                    hir::LogicalOp::Or => (else_block, then_block, true),
                };
                self.current_block = right_block;
                self.lower_expr(right, Some(place.clone()));
                self.terminate(Terminator::Goto(merge_block));
                self.current_block = const_block;
                self.assign_constant(place, Constant::from(constant));
                self.terminate(Terminator::Goto(merge_block));
                self.current_block = merge_block;
            }
            &ExprKind::NeverCast(expr) => {
                self.lower_expr(expr, None);
                if !matches!(self.body.exprs[expr].kind, ExprKind::Call { .. }) {
                    self.terminate(Terminator::Unreachable);
                    let next_block = self.new_block();
                    self.current_block = next_block;
                }
            }
            &ExprKind::Binary(op, left, right) => {
                let place = place_or_temporary(self, place, expr);
                let left = self.lower_as_operand(left);
                let right = self.lower_as_operand(right);
                match op {
                    hir::BinaryOp::Divide => {
                        let non_zero_block = self.new_block();
                        let is_zero = self.new_temporary(Type::Bool);
                        self.assign_stmt(
                            is_zero.into(),
                            RValue::Binary(
                                hir::BinaryOp::NotEquals,
                                Box::new((
                                    right.clone(),
                                    Operand::Constant(ConstantNumber::Int(0).into()),
                                )),
                            ),
                        );
                        self.terminate(mir::Terminator::Assert(
                            Operand::Load(is_zero.into()),
                            mir::AssertKind::DivisionByZero(left.clone()),
                            non_zero_block,
                        ));
                        self.current_block = non_zero_block;
                        self.assign_stmt(place, RValue::Binary(op, Box::new((left, right))));
                    }
                    _ => self.assign_stmt(place, RValue::Binary(op, Box::new((left, right)))),
                }
            }
            ExprKind::Variable(_)
            | ExprKind::Literal(_)
            | ExprKind::Function(_)
            | ExprKind::Field(_, _)
            | ExprKind::Index(_, _)
            | ExprKind::Builtin(_, _) => {
                let place = place_or_temporary(self, place, expr);
                let operand = self.lower_as_operand(expr);
                self.assign_stmt(place, RValue::Use(operand));
            }
            ExprKind::Tuple(elements) => {
                if elements.is_empty() {
                    if let Some(place) = place {
                        self.assign_unit(place);
                    }
                } else {
                    let place = place_or_temporary(self, place, expr);
                    let element_types = elements
                        .iter()
                        .map(|&element| self.body.exprs[element].ty.clone())
                        .collect();
                    let operands = elements
                        .iter()
                        .copied()
                        .map(|element| self.lower_as_operand(element))
                        .collect();
                    self.assign_stmt(place, RValue::Tuple(element_types, operands));
                }
            }
            &ExprKind::Call(callee, ref args) => {
                let place = place_or_temporary(self, place, expr);
                let callee = self.lower_as_operand(callee);
                let args = args
                    .iter()
                    .copied()
                    .map(|arg| self.lower_as_operand(arg))
                    .collect();
                self.assign_stmt(place, RValue::Call(callee, args));
                if !self.context.is_type_inhabited(&self.body.exprs[expr].ty) {
                    self.terminate(Terminator::Unreachable);
                    self.current_block = self.new_block();
                }
            }
            ExprKind::StructLiteral(struct_literal) => {
                let &thir::StructLiteral {
                    id,
                    kind: _,
                    ref generic_args,
                    variant,
                    ref fields,
                } = struct_literal.as_ref();
                let place = place_or_temporary(self, place, expr);
                let mut fields = fields
                    .iter()
                    .map(|field| (field.field, Some(self.lower_as_operand(field.expr))))
                    .collect::<FxHashMap<_, _>>();
                let fields = (0..fields.len())
                    .map(|field| {
                        let field = FieldIndex::new(field);
                        fields
                            .get_mut(&field)
                            .expect("There should be an operand in the fields list")
                            .take()
                            .expect("There should be an operand")
                    })
                    .collect();
                self.assign_stmt(
                    place,
                    RValue::Adt(Box::new((id, generic_args.clone(), variant)), fields),
                );
            }
            ExprKind::Array(elements) => {
                let ty = self.body.exprs[expr]
                    .ty
                    .index_of()
                    .expect("This should be indexable");
                let place = place_or_temporary(self, place, expr);
                let elements = elements
                    .iter()
                    .copied()
                    .map(|element| self.lower_as_operand(element))
                    .collect();
                self.assign_stmt(place, RValue::Array(ty, elements));
            }
            &ExprKind::Unary(op, operand) => {
                let place = place_or_temporary(self, place, expr);
                let operand = self.lower_as_operand(operand);
                self.assign_stmt(place, RValue::Unary(op, operand));
            }
            &ExprKind::Match(operand, ref arms) => {
                self.lower_match_expr(place, expr, operand, arms);
            }
        }
    }
    fn lower_stmt(&mut self, stmt: &thir::Stmt) {
        match &stmt.kind {
            &StmtKind::Expr(expr) => {
                self.lower_expr(expr, None);
            }
            &StmtKind::Let(ref pattern, expr) => {
                self.declare_bindings(&pattern);
                match &pattern.kind {
                    &PatternKind::Binding(_, variable, None) => {
                        let local = self.var_to_local[&variable];
                        self.lower_expr(expr, Some(local.into()));
                    }
                    _ => {
                        let place = self.lower_as_place(expr);
                        self.lower_let(pattern, place);
                    }
                }
            }
        }
    }
    fn declare_bindings(&mut self, pattern: &Pattern) {
        match &pattern.kind {
            &PatternKind::Binding(_, variable, ref sub_pattern) => {
                let local = self.new_local(LocalInfo {
                    ty: pattern.ty.clone(),
                });
                self.var_to_local.insert(variable, local);
                if let Some(sub_pattern) = sub_pattern.as_ref() {
                    self.declare_bindings(sub_pattern);
                }
            }
            PatternKind::Tuple(elements) => {
                for (_, element) in elements.iter().enumerate() {
                    self.declare_bindings(element);
                }
            }
            PatternKind::Constant(_) => (),
            PatternKind::Wildcard => (),
            PatternKind::Struct(_, _, operands) => {
                for &FieldPattern {
                    field: _,
                    ref pattern,
                } in operands.iter()
                {
                    self.declare_bindings(pattern);
                }
            }
            PatternKind::Variant(_, _, _, fields) => {
                for element in fields.iter() {
                    self.declare_bindings(element);
                }
            }
        }
    }
    fn lower_body(mut self, expr: ExprId) -> Body {
        self.current_block = self.result_body.blocks.push(Block {
            stmts: Vec::new(),
            terminator: None,
        });
        for param in self.body.params.iter() {
            self.new_local(LocalInfo {
                ty: param.ty.clone(),
            });
        }
        for (i, param) in self.body.params.iter().enumerate() {
            let param_local = Local::new(i);
            match param.pattern.kind {
                PatternKind::Binding(_, id, None) => {
                    self.var_to_local.insert(id, param_local);
                }
                _ => {
                    self.declare_bindings(&param.pattern);
                    self.lower_let(&param.pattern, param_local.into());
                }
            }
        }
        let operand = self.lower_as_operand(expr);
        self.terminate(Terminator::Return(operand));
        self.result_body
    }
}
