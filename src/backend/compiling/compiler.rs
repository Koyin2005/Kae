use std::rc::Rc;

use crate::{backend::{disassembly::disassemble, instructions::{Chunk, Constant, Instruction, Program}, values::Function}, frontend::typechecking::{substituter::{sub_function, sub_name}, names::Structs, typechecker::GenericTypeId, typed_ast::{BinaryOp, LogicalOp, NumberKind, PatternNode, PatternNodeKind, TypedAssignmentTargetKind, TypedExprNode, TypedExprNodeKind, TypedFunction, TypedStmtNode, UnaryOp}, types::Type}};


struct Local{
    name : String,
    index : usize,
    depth : usize
}

struct GenericFunction{
    name : String,
    generic_params : Vec<GenericTypeId>,
    depth : usize,
    template : TypedFunction,
    monos : Vec<(String,usize)>
}
pub struct CompileFailed;
#[derive(Default)]
pub struct Compiler{
    current_chunk : Chunk,
    constants : Vec<Constant>,
    globals : Vec<String>,
    generic_functions : Vec<GenericFunction>,
    locals : Vec<Local>,
    scope_depth : usize,
    structs : Structs,
    mono_counter : usize
}
impl Compiler{
    pub fn new(structs:Structs)->Self{
        Self { structs,..Default::default() }
    }
    fn begin_scope(&mut self){
        self.scope_depth += 1;
    }
    fn end_scope(&mut self){
        self.scope_depth -= 1;
        self.locals.retain(|local| {
            local.depth <= self.scope_depth
        });

        self.generic_functions.retain(|function| function.depth <= self.scope_depth);
    }
    fn get_global(&self,name:&str)->Option<usize>{
       self.globals.iter().rev().position(|global| global == name).map(|index|  self.globals.len() - index - 1)
    }
    fn get_local(&self,name:&str)->Option<usize>{
        self.locals.iter().rev().find(|local| local.name == name).map(|local| local.index)
    }
    fn emit_define_instruction(&mut self,index:usize,line:u32){
        if self.scope_depth == 0{
            self.emit_instruction(Instruction::StoreGlobal(index as u16),line);

        }
        else{
            self.emit_instruction(Instruction::StoreLocal(index as u16),line);
        }

    }
    fn define_name(&mut self,name:String,line:u32){
        let index = self.declare_name(name);
        self.emit_define_instruction(index, line);
    }
    fn load_name(&mut self,name:&str,line:u32){
        if let Some(index) = self.get_local(name){
            self.emit_instruction(Instruction::LoadLocal(index as u16),line);
        }
        else{
            let index = self.get_global(name).unwrap_or_else(|| panic!("Already checked for variable named \'{}\'.",name));
            self.emit_instruction(Instruction::LoadGlobal(index as u16),line);
        }
    }
    fn store_name(&mut self,name:&str,line:u32){
        if let Some(index) = self.get_local(name){
            self.emit_instruction(Instruction::StoreLocal(index as u16),line);
        }
        else if let Some(index) = self.get_global(name){
            self.emit_instruction(Instruction::StoreGlobal(index as u16),line);
        }
    }
    fn declare_global(&mut self,name:String)->usize{
        self.globals.push(name);
        self.globals.len()-1
    }
    fn declare_name(&mut self,name:String)->usize{
        if self.scope_depth == 0{
            self.declare_global(name)
        }else{
            let local_index = self.locals.len();
            self.locals.push(Local { name,index: local_index, depth: self.scope_depth });
            self.current_chunk.locals = self.current_chunk.locals.max(self.locals.len());
            local_index
        }
    }
    fn emit_loop(&mut self,loop_start:usize,line:u32){
        let offset = self.current_chunk.code.len();
        self.emit_instruction(Instruction::Loop((offset + 1- loop_start) as u16), line);
    }
    fn emit_jump_instruction(&mut self,instruction : Instruction,line:u32)->usize{
        self.emit_instruction(instruction, line);
        self.current_chunk.code.len() - 1
    }
    fn patch_jump(&mut self,index:usize){
        let next_instr = self.current_chunk.code.len();
        match &mut self.current_chunk.code[index]{
            Instruction::Jump(offset) | Instruction::JumpIfFalse(offset) | Instruction::JumpIfTrue(offset) | Instruction::JumpIfFalsePeek(offset) => {
                *offset = (next_instr - index - 1) as u16;
            },
            _ => unreachable!()
        }
    }
    fn emit_instruction(&mut self,instruction : Instruction,line:u32){
        self.current_chunk.code.push(instruction);
        self.current_chunk.lines.push(line);
    }
    fn add_constant(&mut self,constant:Constant)->usize{
        self.constants.iter().position(|current_constant|{
            &constant == current_constant
        }).unwrap_or_else(||{
            self.constants.push(constant);
            self.constants.len()-1
        })
    }
    fn load_constant_at_index(&mut self,constant:usize,line:u32){
        if constant>=u16::MAX as usize{
            todo!("Too many constants in one chunk.")
        }
        let constant = constant as u16;
        self.emit_instruction(Instruction::LoadConstant(constant),line);
        

    }
    fn load_constant(&mut self,constant:Constant,line:u32)->usize{
        let constant = self.add_constant(constant);
        self.load_constant_at_index(constant, line);
        constant
    }
    fn load_int(&mut self,int:i64,line:u32){
        if int <= i16::MAX as i64  && int >= i16::MIN as i64 {
            self.emit_instruction(Instruction::LoadInt(int as i16),line);
        }
        else{
            self.load_constant(Constant::Int(int), line);
        }

    }
    fn compile_function(&mut self,function:&TypedFunction,function_name:String,constant_index : Option<usize>){
        let old_locals = std::mem::take(&mut self.locals);
        let old_chunk = std::mem::take(&mut self.current_chunk);
        
        self.begin_scope();
        let params = function.signature.params.iter().enumerate().filter_map(|(i,(pattern,ty))|{
            match &pattern.kind{
                PatternNodeKind::Name(name) => {
                    self.declare_name(name.clone());
                    None

                },
                PatternNodeKind::Tuple(elements) if elements.is_empty() => {
                    self.declare_name(format!("*param_{}",i));
                    None
                },
                _ => Some((self.declare_name(format!("*param_{}",i)),pattern,ty))
            }

        }).collect::<Vec<_>>();

        for (local_index,pattern,ty) in params{
            self.emit_instruction(Instruction::LoadLocal(local_index as u16),pattern.location.start_line);
            self.compile_pattern_assignment(pattern, ty,pattern.location.end_line);
        }

        self.compile_expr(&function.body);
        self.end_scope();

        if function.body.ty != Type::Never{
            self.emit_instruction(Instruction::Return, function.body.location.end_line);
        }
        disassemble(&function_name, &self.current_chunk);
        self.locals = old_locals;
        let func_code = std::mem::replace(&mut self.current_chunk, old_chunk);
        let func_constant = Constant::Function(Rc::new(Function{
            name : function_name,
            chunk : func_code
        }));
        let func_constant = if let Some(constant_index) = constant_index{
            self.constants[constant_index] = func_constant;
            constant_index
        }
        else{
            self.add_constant(func_constant)
        };
        self.load_constant_at_index(func_constant,function.body.location.end_line);
    }
    fn compile_pattern_check(&mut self,pattern:&PatternNode){
        match &pattern.kind{
            &PatternNodeKind::Bool(bool) => {
                self.emit_instruction(Instruction::LoadBool(bool), pattern.location.end_line);
                self.emit_instruction(Instruction::Equals, pattern.location.end_line);
            }
            &PatternNodeKind::Int(int) => {
                self.load_int(int, pattern.location.end_line);
                self.emit_instruction(Instruction::Equals, pattern.location.end_line);
            },
            &PatternNodeKind::Float(float) => {
                self.load_constant(Constant::Float(float),pattern.location.end_line);
                self.emit_instruction(Instruction::Equals, pattern.location.end_line);
            },
            PatternNodeKind::String(string) => {
                self.load_constant(Constant::String(Rc::from(string as &str)),pattern.location.end_line);
                self.emit_instruction(Instruction::Equals, pattern.location.end_line);
            },
            PatternNodeKind::Array(before,ignore ,after ) => {

                match ignore.as_ref(){
                    Some(ignore) if before.is_empty() && after.is_empty() => {
                        self.emit_instruction(Instruction::Pop, ignore.location.start_line);
                        self.emit_instruction(Instruction::LoadBool(true), ignore.location.start_line);
                        return;
                    },
                    _ => ()
                }
                let total_before_and_after_len = (before.len() + after.len()) as i64;
                self.emit_instruction(Instruction::Copy(1), pattern.location.start_line);
                self.emit_instruction(Instruction::GetArrayLength,pattern.location.start_line);
                self.load_constant(Constant::Int(total_before_and_after_len),pattern.location.start_line);
                if ignore.is_some(){
                    self.emit_instruction(Instruction::GreaterEqualsInt, pattern.location.start_line);
                }
                else{
                    self.emit_instruction(Instruction::Equals, pattern.location.start_line);
                }

                let length_jump = self.emit_jump_instruction(Instruction::JumpIfFalse(0xFF), pattern.location.start_line);

                let mut jumps = Vec::new();
                for (i,pattern) in before.iter().enumerate(){
                    self.emit_instruction(Instruction::Copy(1), pattern.location.start_line);
                    self.load_int(i as i64, pattern.location.start_line);
                    self.emit_instruction(Instruction::LoadIndex,pattern.location.start_line);
                    self.compile_pattern_check(pattern);
                    jumps.push(self.emit_jump_instruction(Instruction::JumpIfFalse(0xFF), pattern.location.end_line));
                }
                let mut after_jumps = Vec::new();
                if !after.is_empty(){

                    self.emit_instruction(Instruction::Copy(1), pattern.location.start_line);
                    self.emit_instruction(Instruction::GetArrayLength, pattern.location.start_line);
                    self.load_int(after.len() as i64, pattern.location.start_line);
                    self.emit_instruction(Instruction::SubtractInt, pattern.location.start_line);

                    for (i,pattern) in after.iter().enumerate(){
                        self.emit_instruction(Instruction::Copy(2), pattern.location.start_line);
                        self.emit_instruction(Instruction::Copy(2), pattern.location.start_line);
                        self.load_int(i as i64, pattern.location.start_line);
                        self.emit_instruction(Instruction::AddInt, pattern.location.start_line);
                        self.emit_instruction(Instruction::LoadIndex,pattern.location.start_line);
                        self.compile_pattern_check(pattern);
                        after_jumps.push(self.emit_jump_instruction(Instruction::JumpIfFalse(0xFF), pattern.location.end_line));
                    }

                    self.emit_instruction(Instruction::Pop, pattern.location.end_line);
                }
                self.emit_instruction(Instruction::Pop, pattern.location.end_line);
                self.emit_instruction(Instruction::LoadBool(true), pattern.location.end_line);
                let end_jump = self.emit_jump_instruction(Instruction::Jump(0xFF), pattern.location.end_line);
                
                if !after_jumps.is_empty(){
                    self.emit_instruction(Instruction::Pop,pattern.location.end_line);
                    for jump in after_jumps{
                        self.patch_jump(jump);
                    }
                }
                self.patch_jump(length_jump);
                for jump in jumps{
                    self.patch_jump(jump);
                }
                self.emit_instruction(Instruction::Pop, pattern.location.end_line);
                self.emit_instruction(Instruction::LoadBool(false), pattern.location.end_line);
                self.patch_jump(end_jump);
            }
            PatternNodeKind::Tuple(elements) => {
                
                let mut jump = None;
                for (i,element) in elements.iter().enumerate(){
                    if let Some(jump) = jump{
                        self.patch_jump(jump);
                    }
                    self.emit_instruction(Instruction::Copy(1), pattern.location.start_line);
                    self.emit_instruction(Instruction::GetTupleElement(i as u16), pattern.location.start_line);
                    self.compile_pattern_check(element); 
                    jump = Some(self.emit_jump_instruction(Instruction::JumpIfFalse(0xFF), element.location.start_line));
                }
                self.emit_instruction(Instruction::Pop,pattern.location.end_line);
                self.emit_instruction(Instruction::LoadBool(true), pattern.location.end_line);
                if let Some(jump) = jump{
                    let end_jump = self.emit_jump_instruction(Instruction::Jump(0xFF), pattern.location.end_line);
                    self.patch_jump(jump);
                    self.emit_instruction(Instruction::LoadBool(false), pattern.location.end_line);
                    self.patch_jump(end_jump);
                }
            },
            PatternNodeKind::Struct { ty, fields } => {
                let mut jump = None;
                for (field_name,pattern) in fields{
                    if let Some(jump) = jump{
                        self.patch_jump(jump);
                    }
                    self.emit_instruction(Instruction::Copy(1), pattern.location.start_line);
                    let field_index = ty.get_field_index(field_name, &self.structs).expect("Can only have valid fields");
                    self.emit_instruction(Instruction::LoadField(field_index as u16),pattern.location.start_line);
                    self.compile_pattern_check(pattern);
                    jump = Some(self.emit_jump_instruction(Instruction::JumpIfFalse(0xFF), pattern.location.end_line));
                    
                }
                self.emit_instruction(Instruction::Pop, pattern.location.end_line);
                self.emit_instruction(Instruction::LoadBool(true), pattern.location.end_line);
                if let Some(jump) = jump{
                    let end_jump = self.emit_jump_instruction(Instruction::Jump(0xFF), pattern.location.end_line);
                    self.patch_jump(jump);
                    self.emit_instruction(Instruction::LoadBool(false), pattern.location.end_line);
                    self.patch_jump(end_jump);
                }
            
            },
            PatternNodeKind::Wildcard => {
                self.emit_instruction(Instruction::Pop, pattern.location.end_line);
                self.emit_instruction(Instruction::LoadBool(true), pattern.location.end_line);
            }
            PatternNodeKind::Name(name) => {
                self.define_name(name.clone(),pattern.location.end_line);
                self.emit_instruction(Instruction::LoadBool(true), pattern.location.end_line);
            }

        }
    }
    fn compile_expr(&mut self,expr:&TypedExprNode){
        match &expr.kind{
            TypedExprNodeKind::Unit => {
                self.emit_instruction(Instruction::LoadUnit,expr.location.end_line);
            },
            TypedExprNodeKind::Number(kind) => {
                match *kind{
                    NumberKind::Int(int) => {
                        self.load_int(int, expr.location.end_line);
                    },
                    NumberKind::Float(float) => {
                        self.load_constant(Constant::Float(float),expr.location.end_line);
                    }
                }
            },
            TypedExprNodeKind::String(string) => {
                self.load_constant(Constant::String(string.clone()),expr.location.end_line);
            },
            TypedExprNodeKind::Bool(bool) => {
                self.emit_instruction(Instruction::LoadBool(*bool),expr.location.end_line);
            },
            TypedExprNodeKind::Tuple(elements) => {
                for element in elements{
                    self.compile_expr(element);
                }
                if elements.len() > u16::MAX as usize{
                    todo!("Too many elements in tuple");
                }
                self.emit_instruction(Instruction::BuildTuple(elements.len() as u16),expr.location.end_line);
            },
            TypedExprNodeKind::Get(name) => {
                self.load_name(name,expr.location.end_line);
            },
            TypedExprNodeKind::Print(args) => {
                for arg in args{
                    self.compile_expr(arg);
                }
                self.emit_instruction(Instruction::Print(args.len() as u16),expr.location.end_line);
                self.emit_instruction(Instruction::LoadUnit,expr.location.end_line);
            },
            TypedExprNodeKind::Block { stmts, expr:result_expr } => {
                self.begin_scope();
                self.compile_stmts(stmts);
                if let Some(expr) = result_expr.as_ref(){
                    self.compile_expr(expr);
                }
                else if expr.ty != Type::Never{
                    self.emit_instruction(Instruction::LoadUnit,expr.location.end_line);
                }
                self.end_scope();
            },
            TypedExprNodeKind::Array(elements) => {
                for element in elements{
                    self.compile_expr(element);
                }
                self.emit_instruction(Instruction::BuildList(elements.len() as u16),expr.location.end_line);

            },
            TypedExprNodeKind::Index { lhs, rhs } => {
                self.compile_expr(lhs);
                self.compile_expr(rhs);
                self.emit_instruction(Instruction::LoadIndex,rhs.location.end_line);
            },
            TypedExprNodeKind::Binary { op, left, right } => {
                self.compile_expr(left);
                self.compile_expr(right);
                let is_int = left.ty == Type::Int;
                self.emit_instruction(match op {
                    BinaryOp::Add => if is_int { Instruction::AddInt } else if left.ty == Type::String {Instruction::Concatenate} else {Instruction::AddFloat},
                    BinaryOp::Subtract => if is_int {Instruction::SubtractInt } else {Instruction::SubtractFloat},
                    BinaryOp::Multiply => if is_int {Instruction::MultiplyInt} else {Instruction::MultiplyFloat},
                    BinaryOp::Divide => if is_int { Instruction::DivideInt} else {Instruction::DivideFloat},
                    BinaryOp::Lesser => if is_int { Instruction::LesserInt } else {Instruction::LesserFloat},
                    BinaryOp::LesserEquals => if is_int {Instruction::LesserEqualsInt } else {Instruction::LesserEqualsFloat},
                    BinaryOp::Greater => if is_int {Instruction::GreaterInt } else {Instruction::GreaterFloat},
                    BinaryOp::GreaterEquals => if is_int {Instruction::GreaterEqualsInt} else {Instruction::GreaterEqualsFloat},
                    BinaryOp::Equals => Instruction::Equals,
                    BinaryOp::NotEquals => Instruction::NotEquals
                },right.location.end_line)
            },
            TypedExprNodeKind::Unary { op, operand } => {
                self.compile_expr(operand);
                let is_int = operand.ty == Type::Int;
                self.emit_instruction(match op{
                    UnaryOp::Negate => if is_int { Instruction::NegateInt} else {Instruction::NegateFloat}
                },operand.location.end_line);
            },
            TypedExprNodeKind::Logical { op, left, right } => {
                self.compile_expr(left);
                let jump = self.emit_jump_instruction(match op {
                    LogicalOp::And => {
                        Instruction::JumpIfFalse(0xFF)
                    },
                    LogicalOp::Or => {
                        Instruction::JumpIfTrue(0xFF)
                    }
                }, left.location.end_line);
                self.compile_expr(right);
                self.patch_jump(jump);
                self.emit_instruction(match op{
                    LogicalOp::And => Instruction::LoadBool(false),
                    LogicalOp::Or => Instruction::LoadBool(true),
                },
                right.location.end_line);
            },
            TypedExprNodeKind::If { condition, then_branch, else_branch } => {
                self.compile_expr(condition);
                let else_branchjump = self.emit_jump_instruction(Instruction::JumpIfFalse(0xFF), condition.location.end_line);
                self.compile_expr(then_branch);
                if let Some(else_branch) = else_branch{
                    let end_jump = self.emit_jump_instruction(Instruction::Jump(0xFF), else_branch.location.start_line);
                    self.patch_jump(else_branchjump);
                    self.compile_expr(else_branch);
                    self.patch_jump(end_jump);
                }
                else{
                    self.patch_jump(else_branchjump);
                }
            },
            TypedExprNodeKind::Match { matchee, arms } => {
                self.compile_expr(matchee);
                let jumps_to_patch = arms.iter().map(|arm|{
                    self.emit_instruction(Instruction::Copy(1),arm.pattern.location.start_line);
                    self.begin_scope();
                    self.compile_pattern_check(&arm.pattern);
                    let then_jump = self.emit_jump_instruction(Instruction::JumpIfFalse(0xFF), arm.pattern.location.end_line);
                    self.compile_expr(&arm.expr);
                    self.end_scope();
                    let end_jump = self.emit_jump_instruction(Instruction::Jump(0xFF), arm.expr.location.end_line);
                    self.patch_jump(then_jump);
                    end_jump
                }).collect::<Box<[_]>>();
                for jump in jumps_to_patch.into_vec(){
                    self.patch_jump(jump);
                }
            },
            TypedExprNodeKind::While { condition, body } => {
                let loop_start = self.current_chunk.code.len();
                self.compile_expr(condition);
                let loop_jump = self.emit_jump_instruction(Instruction::JumpIfFalse(0xFF),condition.location.end_line);
                self.compile_expr(body);
                self.emit_instruction(Instruction::Pop,body.location.end_line);
                self.emit_loop(loop_start,body.location.end_line);
                self.patch_jump(loop_jump);
                self.emit_instruction(Instruction::LoadUnit,body.location.end_line);
            },
            TypedExprNodeKind::Assign { lhs, rhs } => {
                match &lhs.kind{
                    TypedAssignmentTargetKind::Name(name) => {
                        self.compile_expr(rhs);
                        self.store_name(name, rhs.location.end_line);
                        self.load_name(name,rhs.location.end_line);

                    },
                    TypedAssignmentTargetKind::Index { lhs, rhs:index } => {
                        self.compile_expr(lhs);
                        self.compile_expr(index);
                        self.compile_expr(rhs);
                        self.emit_instruction(Instruction::StoreIndex, rhs.location.end_line);
                        self.emit_instruction(Instruction::LoadIndex, rhs.location.end_line);
                    },
                    TypedAssignmentTargetKind::Field { lhs, name } => {
                        self.compile_expr(lhs);
                        self.compile_expr(rhs);
                        let field_index= lhs.ty.get_field_index(&name.content, &self.structs).expect("Already checked fields");
                        self.emit_instruction(Instruction::StoreField(field_index as u16), rhs.location.end_line);
                        self.emit_instruction(Instruction::LoadField(field_index as u16), rhs.location.end_line);
                    }
                }

            },
            TypedExprNodeKind::Function (function) => {
                self.compile_function(function, "anonymous".to_string(),None);
            },
            TypedExprNodeKind::Call { callee, args } => {
                self.compile_expr(callee);
                for arg in args{
                    self.compile_expr(arg);
                }
                self.emit_instruction(Instruction::Call(args.len() as u16),expr.location.end_line);
            },
            TypedExprNodeKind::Return { expr:return_expr } => {
                if let Some(expr) = return_expr.as_ref(){
                    self.compile_expr(expr);
                }
                else{
                    self.emit_instruction(Instruction::LoadUnit, expr.location.end_line);
                }
                self.emit_instruction(Instruction::Return, expr.location.end_line);
            },
            TypedExprNodeKind::GetGeneric { name, args } => {
                let (index,generic_function) = self.generic_functions.iter().enumerate().rev()
                    .find(|(_,generic_function)| &generic_function.name == name)
                .expect("Should have already checked functions");

                let name = sub_name(name, args);
                if let Some((_,constant))  = generic_function.monos.iter().find(|(monoed_name,..)| monoed_name == &name){
                    self.load_constant_at_index(*constant, expr.location.end_line);
                }
                else{
                    let mut monoed_function = generic_function.template.clone();
                    let mono_name = format!("{}{}",name,self.mono_counter);
                    self.mono_counter +=1 ;
                    sub_function(&mut monoed_function,&generic_function.generic_params.iter().cloned().zip(args.clone()).collect());
                    let  function_placeholder = Function { name: mono_name, ..Default::default()};
                    let function_constant_index = self.add_constant(Constant::Function(Rc::new(function_placeholder)));
                    self.generic_functions[index].monos.push((name.clone(),function_constant_index));
                    self.compile_function(&monoed_function, name,Some(function_constant_index));
                }
            },
            TypedExprNodeKind::TypenameOf(ty) => {
                self.load_constant(Constant::String(Rc::from(format!("{}",ty))),expr.location.end_line);
            },
            TypedExprNodeKind::Field(lhs, field_name) => {
                self.compile_expr(lhs);
                match (&lhs.ty,&field_name.content as &str){
                    (Type::Array(..),"length") => {
                        self.emit_instruction(Instruction::GetArrayLength, field_name.location.end_line);
                    },
                    (Type::Struct { id,.. },field) => {
                        self.emit_instruction(
                            Instruction::LoadField(self.structs.get_struct_info(id).expect("Struct should exist").get_field(field).expect("Field should exist").0 as u16,
                            ),field_name.location.end_line
                        );
                    }
                    _ => unreachable!("{}",lhs.ty)
                }
            },
            TypedExprNodeKind::StructInit { fields } => {
                self.emit_instruction(Instruction::InitRecord(fields.len() as u16),expr.location.start_line);
                for (name,field_expr) in fields{
                    self.compile_expr(field_expr);
                    let field_index = match &expr.ty{
                        Type::Struct { id,.. } => {
                            self.structs.get_struct_info(id).expect("Should definitely be a struct").get_field(name).expect("Struct should definitely have field").0
                        },
                        _ => unreachable!("Should definitely be a struct")
                    };
                    self.emit_instruction(Instruction::StoreField(field_index as u16), field_expr.location.end_line);
                }
            }
        }
    }
    fn compile_pattern_assignment(&mut self,pattern:&PatternNode,ty:&Type,line:u32){
        match &pattern.kind{
            PatternNodeKind::Name(name) => {
                self.define_name(name.clone(),line);
            },
            PatternNodeKind::Tuple(patterns) => {
                if !patterns.is_empty(){
                    let Type::Tuple(elements) = ty else {
                        unreachable!()
                    };
                    self.emit_instruction(Instruction::UnpackTuple,line);
                    for (pattern,ty) in patterns.iter().zip(elements.iter()){
                        self.compile_pattern_assignment(pattern, ty,line);
                    }
                }
                else{
                    self.emit_instruction(Instruction::Pop,line)
                }
            },
            PatternNodeKind::Struct { fields,ty } => {
                for (field_name,field) in fields.iter(){
                    let index = ty.get_field_index(field_name, &self.structs).expect("All fields should be checked");
                    self.emit_instruction(Instruction::Copy(1), line);
                    self.emit_instruction(Instruction::LoadField(index as u16), line);
                    self.compile_pattern_assignment(field, ty, line);
                }
                self.emit_instruction(Instruction::Pop, line);
            },
            PatternNodeKind::Wildcard => {
                self.emit_instruction(Instruction::Pop, line);
            },
            PatternNodeKind::Array(before, ignore, after) if before.is_empty() && after.is_empty() && ignore.is_some() => {
                self.emit_instruction(Instruction::Pop, line);
            }
            _ => {}
        }
    }
    fn compile_stmt(&mut self,stmt:&TypedStmtNode){
        match stmt{
            TypedStmtNode::Expr(expr) => {
                self.compile_expr(expr);
                if expr.ty == Type::Unit{
                    self.emit_instruction(Instruction::Pop, expr.location.end_line);
                }
            },
            TypedStmtNode::ExprWithSemi(expr) => {
                self.compile_expr(expr);
                if expr.ty != Type::Never{
                    self.emit_instruction(Instruction::Pop,expr.location.end_line);
                }
            },
            TypedStmtNode::Let { pattern, expr } => {
                self.compile_expr(expr);
                self.compile_pattern_assignment(pattern, &expr.ty,expr.location.end_line);
            },
            TypedStmtNode::Fun { name, function} => {
                    let name= name.content.clone();
                    let index = self.declare_name(name.clone());
                    self.compile_function(function,name.clone(),None);
                    self.emit_define_instruction(index, function.body.location.end_line);
                
            },
            TypedStmtNode::GenericFunction {function,name,generic_params } => {
                self.generic_functions.push(GenericFunction { name: name.content.clone(),
                        generic_params:generic_params.clone(), 
                        depth: self.scope_depth, template: function.clone(),
                    monos : Vec::new()
                });
            },
            TypedStmtNode::Struct { .. } => {

            }
        }
    }
    fn compile_stmts(&mut self,stmts : &[TypedStmtNode]){
        for stmt in stmts{
            self.compile_stmt(stmt);
        }
    }
    pub fn compile(mut self,stmts : Vec<TypedStmtNode>) -> Result<Program,CompileFailed> {
        
        self.compile_stmts(&stmts);
        let last_line = self.current_chunk.lines.last().copied().unwrap_or(1);
        self.emit_instruction(Instruction::LoadUnit,last_line);
        self.emit_instruction(Instruction::Return,last_line);
        disassemble("<main>", &self.current_chunk);
        Ok(Program{constants:self.constants,chunk:self.current_chunk})
    }
}