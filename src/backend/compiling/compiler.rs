use std::rc::Rc;

use crate::{backend::{disassembly::disassemble, instructions::{Chunk, Constant, Instruction, Program}, natives::{native_input, native_panic, native_parse_int, native_pop, native_push}, values::{Function, NativeFunction}}, frontend::typechecking::{ substituter::{sub_function, sub_name},  typed_ast::{BinaryOp, InitKind, LogicalOp, NumberKind, PatternNode, PatternNodeKind, TypedAssignmentTargetKind, TypedExprNode, TypedExprNodeKind, TypedFunction, TypedStmtNode, UnaryOp}, types::{Type, TypeContext}}};


struct Local{
    name : String,
    index : usize,
    depth : usize
}
#[derive(PartialEq,Eq,Clone, Copy)]
enum Upvalue{
    Local(usize),
    Upvalue(usize)
}
struct GenericFunction{
    name : String,
    depth : usize,
    template : TypedFunction,
    monos : Vec<(String,usize)>
}
#[derive(Default)]
struct CompiledFunction{
    pub locals : Vec<Local>,
    pub upvalues : Vec<Upvalue>
}
pub struct CompileFailed;
#[derive(Default)]
pub struct Compiler{
    current_chunk : Chunk,
    constants : Vec<Constant>,
    names : Vec<String>,
    globals : Vec<String>,
    generic_functions : Vec<GenericFunction>,
    functions : Vec<CompiledFunction>,
    scope_depth : usize,
    type_context : TypeContext,
    mono_counter : usize
}
impl Compiler{
    pub fn new(type_context:TypeContext)->Self{
        Self { type_context,functions:vec![CompiledFunction::default()],..Default::default() }
    }
    fn begin_scope(&mut self){
        self.scope_depth += 1;
    }
    fn end_scope(&mut self){
        self.scope_depth -= 1;
        self.functions.last_mut().unwrap().locals.retain(|local| {
            local.depth <= self.scope_depth
        });

        self.generic_functions.retain(|function| function.depth <= self.scope_depth);
    }
    fn get_global(&self,name:&str)->Option<usize>{
       self.globals.iter().rev().position(|global| global == name).map(|index|  self.globals.len() - index - 1)
    }
    fn get_local(&self,name:&str)->Option<usize>{
        self.functions.last().unwrap().locals.iter().rev().find(|local| local.name == name).map(|local| local.index)
    }
    fn emit_define_instruction(&mut self,index:usize,line:u32){
        if self.scope_depth == 0{
            self.emit_instruction(Instruction::StoreGlobal(index as u16),line);

        }
        else{
            self.emit_instruction(Instruction::StoreLocal(index as u16),line);
        }

    }
    fn load_string(&mut self,name:String,line:u32){
        self.load_constant(Constant::String(name.into()), line);
    }
    fn push_top_of_stack(&mut self,line:u32){
        self.push_slots_below_to_top(1, line);
    }
    fn push_slots_below_to_top(&mut self,slots:u16,line:u32){
        self.emit_instruction(Instruction::Copy(slots), line);
    }
    fn load_bool(&mut self,bool:bool,line:u32){
        self.emit_instruction(Instruction::LoadBool(bool), line);
    }
    fn define_name(&mut self,name:String,line:u32){
        let index = self.declare_name(name);
        self.emit_define_instruction(index, line);
    }
    fn resolve_upvalue(&mut self,name:&str)->Option<usize>{
        
        let (function_depth,local_index) = self.functions.iter().enumerate().rev().filter_map(|(i,function)|{
            function.locals.iter().rev().find(|local| local.name == name).map(|local| (i,local.index))
        }).next().expect("All variables should be checked.");
        let upvalue = self.functions[function_depth+1..].iter_mut().enumerate().map(|(i,function)|{
            let next_upvalue = if i == 0 { Upvalue::Local(local_index) } else {
                let upvalue_count = function.upvalues.len();
                Upvalue::Upvalue(upvalue_count)
            };
            if let Some(upvalue) = function.upvalues.iter().position(|upvalue| upvalue == &next_upvalue){
                upvalue
            }
            else{
                function.upvalues.push(next_upvalue);
                function.upvalues.len()-1
            }
        }).last();
        upvalue
    }
    fn load_name(&mut self,name:&str,line:u32){
        if let Some(index) = self.get_local(name){
            self.emit_instruction(Instruction::LoadLocal(index as u16),line);
        }
        else if let Some(index) =  self.get_global(name){
            self.emit_instruction(Instruction::LoadGlobal(index as u16),line);
        }
        else{
            let upvalue = self.resolve_upvalue(name).unwrap() ;
            self.emit_instruction(Instruction::LoadUpvalue(upvalue as u16), line);
        }
    }
    fn store_name(&mut self,name:&str,line:u32){
        if let Some(index) = self.get_local(name){
            self.emit_instruction(Instruction::StoreLocal(index as u16),line);
        }
        else if let Some(index) = self.get_global(name){
            self.emit_instruction(Instruction::StoreGlobal(index as u16),line);
        }
        else{
            let upvalue = self.resolve_upvalue(name).unwrap() ;
            self.emit_instruction(Instruction::StoreUpvalue(upvalue as u16), line);
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
            let local_index = self.functions.last().unwrap().locals.len();
            self.functions.last_mut().unwrap().locals.push(Local { name,index: local_index, depth: self.scope_depth });
            self.current_chunk.locals = self.current_chunk.locals.max(self.functions.last().unwrap().locals.len());
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
        self.functions.push(CompiledFunction::default());
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
        disassemble(&function_name, &self.current_chunk,&self.constants);
        let compiled_function = self.functions.pop().expect("Function should still be around");
        for upvalue in &compiled_function.upvalues{
            match upvalue{
                Upvalue::Local(local) => {
                    println!("Captured local {}",self.functions.last().unwrap().locals[*local].name);
                },
                Upvalue::Upvalue(upvalue) => {
                    println!("Captured Upvalue {}",upvalue);
                }
            }
        }
        let func_code = std::mem::replace(&mut self.current_chunk, old_chunk);
        let func_constant = Constant::Function(Rc::new(Function{
            name : function_name,
            chunk : func_code,
            upvalues : compiled_function.upvalues.iter().copied().map(|upvalue|{
                match upvalue{
                    Upvalue::Local(local) => (local,true),
                    Upvalue::Upvalue(upvalue) => (upvalue,false)
                }
            }).collect()
        }));
        let func_constant = if let Some(constant_index) = constant_index{
            self.constants[constant_index] = func_constant;
            constant_index
        }
        else{
            self.add_constant(func_constant)
        };

        if !compiled_function.upvalues.is_empty(){
            self.load_constant_at_index(func_constant,function.body.location.end_line);
        }
        else{
            self.emit_instruction(Instruction::Closure(func_constant as u16), function.body.location.end_line);
        }
    }
    fn compile_pattern_check(&mut self,pattern:&PatternNode){
        match &pattern.kind{
            PatternNodeKind::Int(int) => {
                self.push_top_of_stack(pattern.location.end_line);
                self.load_int(*int, pattern.location.end_line);
                self.emit_instruction(Instruction::Equals, pattern.location.end_line);
            },
            PatternNodeKind::Float(float) => {
                self.push_top_of_stack(pattern.location.end_line);
                self.load_constant(Constant::Float(*float), pattern.location.end_line);
                self.emit_instruction(Instruction::Equals, pattern.location.end_line);
            },
            PatternNodeKind::String(string) => {
                self.push_top_of_stack(pattern.location.end_line);
                self.load_string(string.clone(), pattern.location.end_line);
                self.emit_instruction(Instruction::Equals, pattern.location.end_line);
            },
            PatternNodeKind::Wildcard => {
                self.load_bool(true, pattern.location.end_line);
            },
            PatternNodeKind::Name(name) => {
                self.push_top_of_stack(pattern.location.start_line);
                self.define_name(name.clone(), pattern.location.end_line);
                self.load_bool(true, pattern.location.end_line);
            },
            PatternNodeKind::Is(name,right_pattern) => {
                self.push_top_of_stack(right_pattern.location.start_line);
                self.compile_pattern_check(right_pattern);
                let false_jump = self.emit_jump_instruction(Instruction::JumpIfFalse(0xFF), right_pattern.location.end_line);
                self.define_name(name.content.clone(), right_pattern.location.end_line);
                self.load_bool(true, right_pattern.location.end_line);
                let true_jump = self.emit_jump_instruction(Instruction::Jump(0xFF), right_pattern.location.end_line);
                self.patch_jump(false_jump);
                self.emit_instruction(Instruction::Pop, right_pattern.location.end_line);
                self.load_bool(false, right_pattern.location.end_line);
                self.patch_jump(true_jump);
            },
            PatternNodeKind::Tuple(elements) => {
                let mut jumps = Vec::new();
                for (i,element) in  elements.iter().enumerate(){
                    self.push_top_of_stack(element.location.start_line);
                    self.emit_instruction(Instruction::GetTupleElement(i as u16), element.location.start_line);
                    self.compile_pattern_check(element);
                    let false_jump = self.emit_jump_instruction(Instruction::JumpIfFalse(0xFF), element.location.end_line);
                    self.emit_instruction(Instruction::Pop,element.location.end_line);
                    let true_jump = self.emit_jump_instruction(Instruction::Jump(0xFF), element.location.end_line);
                    self.patch_jump(false_jump);
                    self.emit_instruction(Instruction::Pop,element.location.end_line);
                    let skip_jump = self.emit_jump_instruction(Instruction::Jump(0xFF), element.location.end_line);
                    self.patch_jump(true_jump);
                    jumps.push(skip_jump);
                }
                self.load_bool(true,pattern.location.end_line);
                let jump = self.emit_jump_instruction(Instruction::Jump(0xFF), pattern.location.end_line);
                for jump in jumps{
                    self.patch_jump(jump);
                }
                self.load_bool(false, pattern.location.end_line);
                self.patch_jump(jump);

            },
            PatternNodeKind::Struct { ty, fields } => {
                let mut jumps = Vec::new();
                if let Type::EnumVariant { variant_index,.. } = ty{
                    self.push_top_of_stack(pattern.location.start_line);
                    self.emit_instruction(Instruction::LoadField(0), pattern.location.start_line);
                    self.load_int(*variant_index as i64, pattern.location.start_line);
                    self.emit_instruction(Instruction::Equals, pattern.location.start_line);
                    jumps.push(self.emit_jump_instruction(Instruction::JumpIfFalse(0xFF), pattern.location.start_line));
                }
                for (field_name,field_pattern) in fields{
                    self.push_top_of_stack(field_pattern.location.start_line);
                    self.emit_instruction(Instruction::LoadField(ty.get_field_index(field_name, &self.type_context).unwrap() as u16),field_pattern.location.start_line);
                    self.compile_pattern_check(field_pattern);
                    let false_jump  = self.emit_jump_instruction(Instruction::JumpIfFalse(0xFF), field_pattern.location.end_line);
                    self.emit_instruction(Instruction::Pop, field_pattern.location.end_line);
                    let skip_jump = self.emit_jump_instruction(Instruction::Jump(0xFF), field_pattern.location.end_line);
                    self.patch_jump(false_jump);
                    self.emit_instruction(Instruction::Pop, field_pattern.location.end_line);
                    let false_jump = self.emit_jump_instruction(Instruction::Jump(0xFF), field_pattern.location.end_line);
                    self.patch_jump(skip_jump);
                    jumps.push(false_jump);
                }
                self.load_bool(true, pattern.location.end_line);
                let end_jump = self.emit_jump_instruction(Instruction::Jump(0xFF), pattern.location.end_line);
                for jump in jumps{
                    self.patch_jump(jump);
                }
                self.load_bool(false, pattern.location.end_line);
                self.patch_jump(end_jump);
            },
            
            _ => todo!("{:?}",pattern.kind)
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
                let then_jump = self.emit_jump_instruction(Instruction::Jump(0xFF),right.location.end_line);
                self.patch_jump(jump);
                self.emit_instruction(match op{
                    LogicalOp::And => Instruction::LoadBool(false),
                    LogicalOp::Or => Instruction::LoadBool(true),
                },
                right.location.end_line);
                self.patch_jump(then_jump);
            },
            TypedExprNodeKind::If { condition, then_branch, else_branch } => {
                self.compile_expr(condition);
                let else_branchjump = self.emit_jump_instruction(Instruction::JumpIfFalse(0xFF), condition.location.end_line);
                self.compile_expr(then_branch);
                let end_jump = self.emit_jump_instruction(Instruction::Jump(0xFF), else_branch.as_ref().map_or(then_branch.location.end_line, |else_branch| else_branch.location.start_line));
                self.patch_jump(else_branchjump);
                if let Some(else_branch) = else_branch{
                    self.compile_expr(else_branch);
                }
                else{
                    self.emit_instruction(Instruction::LoadUnit, then_branch.location.end_line);
                }
                self.patch_jump(end_jump);
            },
            TypedExprNodeKind::Match { matchee, arms } => {
                self.compile_expr(matchee);
                let jumps_to_patch = arms.iter().map(|arm|{
                    self.begin_scope();
                    self.compile_pattern_check(&arm.pattern);
                    let false_jump = self.emit_jump_instruction(Instruction::JumpIfFalse(0xFF), arm.pattern.location.end_line);
                    self.emit_instruction(Instruction::Pop, arm.pattern.location.end_line);
                    self.compile_expr(&arm.expr);
                    self.end_scope();
                    let end_jump = self.emit_jump_instruction(Instruction::Jump(0xFF), arm.expr.location.end_line);
                    self.patch_jump(false_jump);
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
                        self.push_top_of_stack(rhs.location.end_line);
                        self.store_name(name, rhs.location.end_line);

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
                        let field_index= lhs.ty.get_field_index(&name.content, &self.type_context).expect("Already checked fields");
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
                let Some((index,generic_function)) = self.generic_functions.iter().enumerate().rev()
                    .find(|(_,generic_function)| &generic_function.name == name) else {
                        self.load_name(name, expr.location.end_line);
                        return;
                    };

                let name = sub_name(name, args);
                if let Some((_,constant))  = generic_function.monos.iter().find(|(monoed_name,..)| monoed_name == &name){
                    self.load_constant_at_index(*constant, expr.location.end_line);
                }
                else{
                    let mut monoed_function = generic_function.template.clone();
                    let mono_name = format!("{}{}",name,self.mono_counter);
                    self.mono_counter +=1 ;
                    sub_function(&mut monoed_function,&args.clone());
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
                    (ty @ (Type::Struct {.. } | Type::EnumVariant {.. }),field) => {
                        self.emit_instruction(
                            Instruction::LoadField(ty.get_field_index(field, &self.type_context).expect("All fields should be checked") as u16,
                            ),field_name.location.end_line
                        );
                    }
                    _ => unreachable!("{:?}",lhs.ty)
                }
            },
            TypedExprNodeKind::StructInit { kind,fields } => {

                let total_fields = match kind{
                    InitKind::Struct(_) => fields.len(),
                    InitKind::Variant(id, _) => {
                        self.type_context.enums.get_enum(*id).variants.iter().map(|variant|{
                            variant.fields.len()
                        }).max().unwrap_or(0) + 1
                    }
                };
                let name = match kind{
                    InitKind::Variant(id,variant_index ) => {
                        let enum_info = self.type_context.enums.get_enum(*id);
                        enum_info.variants[*variant_index].name.clone()
                    },
                    InitKind::Struct(_) => {
                        format!("{}",expr.ty)
                    }
                };
                self.load_string(name, expr.location.start_line);
                match kind {
                    InitKind::Variant(id, variant_index) => {
                        self.load_int(*variant_index as i64, expr.location.start_line);
                        let enum_info = self.type_context.enums.get_enum(*id);
                        let field_count = enum_info.variants[*variant_index].fields.len() as i64;
                        self.load_int(field_count , expr.location.start_line);
                        self.emit_instruction(Instruction::BuildCaseRecord(total_fields as u16), expr.location.start_line);
                    },
                    InitKind::Struct(_) =>{
                        self.emit_instruction(Instruction::BuildRecord(total_fields as u16),expr.location.start_line);
                    }
                };
                for (name,field_expr) in fields{
                    self.compile_expr(field_expr);
                    let field_index =  match kind{
                        InitKind::Struct(id) => self.type_context.structs.get_struct_info(id).expect("Should definitely be a struct").get_field(name).expect("Struct should definitely have field").0,
                        InitKind::Variant(id, variant) => {
                            self.type_context.enums.get_enum(*id).variants[*variant].fields.iter().position(|(field_name,_)| field_name == name).map(|index| index + 1).expect("Already checked fields")
                        }
                    };
                    self.emit_instruction(Instruction::StoreField(field_index as u16), field_expr.location.end_line);
                }
            },
            TypedExprNodeKind::MethodCall { lhs, method, args } => {
                self.load_name(&format!("{}::{}",lhs.ty,method.content), lhs.location.start_line);
                self.compile_expr(lhs);
                for arg in args{
                    self.compile_expr(arg);
                }
                self.emit_instruction(Instruction::Call((args.len()+1) as u16), expr.location.end_line);
            },
            TypedExprNodeKind::GetMethod { ty, method } => {
                self.load_name(&format!("{}::{}",ty,method.content),method.location.end_line);
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
                    let index = ty.get_field_index(field_name, &self.type_context).expect("All fields should be checked");
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
            },
            PatternNodeKind::Is(name, right_pattern) => {
                self.emit_instruction(Instruction::Copy(1), line);
                self.define_name(name.content.clone(), line);
                self.compile_pattern_assignment(right_pattern, ty, line);
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
            TypedStmtNode::GenericFunction {function,name,.. } => {
                self.generic_functions.push(GenericFunction { name: name.content.clone(),
                        depth: self.scope_depth, template: function.clone(),
                    monos : Vec::new()
                });
            },
            TypedStmtNode::Struct { .. } | TypedStmtNode::Enum { .. }  => {

            },
            TypedStmtNode::Impl { ty, methods } => {
                for method in methods{
                    let method_name = format!("{}::{}",ty,method.name.content);
                    self.compile_function(&method.function, method_name.clone(), None);
                    self.define_name(method_name, method.function.body.location.end_line);
                }
            }
        }
    }
    fn compile_stmts(&mut self,stmts : &[TypedStmtNode]){
        for stmt in stmts{
            self.compile_stmt(stmt);
        }
    }
    pub fn compile(mut self,stmts : Vec<TypedStmtNode>) -> Result<Program,CompileFailed> {
        self.load_constant(Constant::NativeFunction(Rc::new(NativeFunction{
            name : "input".to_string(),
            function : native_input
        })), 1);
        self.define_name("input".to_string(), 1);

        self.load_constant(Constant::NativeFunction(Rc::new(NativeFunction{
            name : "panic".to_string(),
            function : native_panic
        })), 1);
        self.define_name("panic".to_string(), 1);
        
        self.load_constant(Constant::NativeFunction(Rc::new(NativeFunction{
            name : "push".to_string(),
            function : native_push
        })), 1);
        self.define_name("push".to_string(), 1);

        
        self.load_constant(Constant::NativeFunction(Rc::new(NativeFunction{
            name : "pop".to_string(),
            function : native_pop
        })), 1);
        self.define_name("pop".to_string(), 1);

        
        self.load_constant(Constant::NativeFunction(Rc::new(NativeFunction{
            name : "parse_int".to_string(),
            function : native_parse_int
        })), 1);
        self.define_name("parse_int".to_string(), 1);

        self.compile_stmts(&stmts);
        let last_line = self.current_chunk.lines.last().copied().unwrap_or(1);
        self.emit_instruction(Instruction::LoadUnit,last_line);
        self.emit_instruction(Instruction::Return,last_line);
        disassemble("<main>", &self.current_chunk,&self.constants);
        Ok(Program{constants:self.constants,chunk:self.current_chunk,names:self.names.into_iter().map(|name| name.into()).collect()})
    }
}