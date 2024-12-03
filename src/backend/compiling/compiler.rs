use std::rc::Rc;

use crate::{backend::{disassembly::disassemble, instructions::{Chunk, Constant, Instruction, Program}, natives::{native_input, native_panic, native_parse_int, native_pop, native_push}, values::{Function, NativeFunction}}, frontend::typechecking::{ substituter::{sub_function, sub_name},  typed_ast::{BinaryOp, InitKind, LogicalOp, NumberKind, PatternNode, PatternNodeKind, TypedAssignmentTargetKind, TypedExprNode, TypedExprNodeKind, TypedFunction, TypedStmtNode, UnaryOp}, types::{Struct, StructId, Type, TypeContext}}};


struct Local{
    name : String,
    index : usize,
    depth : usize,
    is_captured : bool
}
#[derive(Clone, Copy,PartialEq)]
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

struct Global{
    pub name : String,
    pub index : usize
}
pub struct CompileFailed;
#[derive(Default)]
pub struct Compiler{
    current_chunk : Chunk,
    constants : Vec<Constant>,
    names : Vec<String>,
    globals : Vec<Global>,
    next_global:usize,
    generic_functions : Vec<GenericFunction>,
    next_local:usize,
    functions : Vec<CompiledFunction>,
    scope_depth : usize,
    type_context : TypeContext,
    mono_counter : usize,
    anonymous_var_counter:usize
}
impl Compiler{
    fn is_ref_type(&self,ty:&Type)->bool{
        matches!(ty,Type::Array(_)|Type::String|Type::Function { .. }) 
    }
    fn get_field_offset(&self,base_ty:&Type,name:&str)->usize{
        let field_index = base_ty.get_field_index(name, &self.type_context).expect("Should have checked all fields");
        self.get_fields(base_ty).iter().take(if field_index > 0 { field_index} else { 0}).map(|(_,ty)| self.get_size_in_stack_slots(ty)).sum()
    }
    fn get_size_in_stack_slots(&self,ty:&Type)->usize{
        match ty{
            Type::Struct {.. } => self.get_fields(ty).iter().map(|(_,ty)| self.get_size_in_stack_slots(ty)).sum(),
            Type::Tuple(elements) => elements.iter().map(|ty| self.get_size_in_stack_slots(ty)).sum(),
            _ => 1
        }
    }
    fn get_fields(&self,ty:&Type)->Vec<(String,Type)>{
        match ty{
            Type::Struct { generic_args, id, .. } => {
                    let fields_iter = self.get_struct_info(id).fields.iter();
                    if generic_args.is_empty(){
                        fields_iter.cloned().collect()
                    }
                    else{
                        let fields_iter = fields_iter.map(|(field_name,_)|{
                            (field_name.clone(),ty.get_field(&field_name, &self.type_context).expect("All fields should exist"))
                        });
                        fields_iter.collect()
                    }
            },
            _ => Vec::new()
            
        }
    }
    fn get_struct_info(&self,struct_id:&StructId)->&Struct{
        self.type_context.structs.get_struct_info(struct_id).expect("All structs should be checked")
    }
    pub fn new(type_context:TypeContext)->Self{
        Self { type_context,functions:vec![CompiledFunction::default()],..Default::default() }
    }
    fn begin_scope(&mut self){
        self.scope_depth += 1;
    }
    fn end_scope(&mut self,line:u32){
        self.scope_depth -= 1;
        let mut captured_locals = Vec::new();
        self.functions.last_mut().unwrap().locals.retain(|local| {
            if local.depth > self.scope_depth{
                if local.is_captured{
                    captured_locals.push(local.index);
                }
                false
            }
            else { 
                true
            }
        });
        for local in captured_locals{
            self.emit_instruction(Instruction::CloseUpvalue(local as u16), line);
        }
        self.generic_functions.retain(|function| function.depth <= self.scope_depth);
    }
    fn get_global(&self,name:&str)->Option<usize>{
       self.globals.iter().rev().find(|global| global.name == name).map(|global| global.index)
    }
    fn get_local(&self,name:&str)->Option<usize>{
        self.functions.last().unwrap().locals.iter().rev().find(|local| local.name == name).map(|local| local.index)
    }
    fn emit_define_instruction(&mut self,index:usize,size:usize,line:u32){
        if self.scope_depth == 0{
            if size == 1{
                self.emit_instruction(Instruction::StoreGlobal(index as u16),line);
            }
            else{
                self.emit_instruction(Instruction::StoreGlobalStruct(index as u16,size),line);
            }
        }
        else{
            if size == 1{
                self.emit_instruction(Instruction::StoreLocal(index as u16),line);
            }
            else{
                self.emit_instruction(Instruction::StoreLocalStruct(index as u16,size),line);
            }
        }

    }
    fn load_string(&mut self,name:String,line:u32){
        self.load_constant(Constant::String(name.into()), line);
    }
    fn push_values_on_top_of_stack(&mut self,size:usize,line:u32){
        for _ in 0..size{
            self.push_slots_below_to_top(size as u16, line);
        }
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
    fn define_name(&mut self,name:String,size:usize,line:u32){
        let index = self.declare_name(name,size);
        self.emit_define_instruction(index, size,line);
    }
    fn resolve_upvalue(&mut self,name:&str)->usize{
        fn add_upvalue(function :&mut CompiledFunction,new_upvalue:Upvalue)->usize{
            if let Some(upvalue) =  function.upvalues.iter().position(|upvalue| upvalue == &new_upvalue){
                upvalue
            }
            else{
                function.upvalues.push(new_upvalue);
                function.upvalues.len()-1
            }
        }
        let (Some(function_index),Some(local_index)) =  self.functions.iter_mut().enumerate().rev()
        .filter_map(|(i,function)|{
            function.locals.iter_mut().rev().find(|local| local.name == name).map(|local|{
                local.is_captured = true;
                (i,local.index)
            })
        }).next().map_or((None,None),|(i,local_index)| (Some(i),Some(local_index))) else {
            panic!("Variable '{}' should definitely be in a function's scope.",name);
        };
        let mut upvalue = None;
        for i in function_index+1..self.functions.len(){
            let next_upvalue = if i == function_index+1{
                add_upvalue(&mut self.functions[i],Upvalue::Local(local_index))
            }
            else{
                add_upvalue(&mut self.functions[i], Upvalue::Upvalue(upvalue.unwrap()))
            };
            upvalue = Some(next_upvalue);
        }
        upvalue.unwrap()
    }
    fn load_name(&mut self,name:&str,size:usize,line:u32){
        let instruction = if let Some(index) = self.get_local(name){
            if size==1{
                Instruction::LoadLocal(index as u16)
            }
            else{
                Instruction::LoadLocalStruct(index as u16,size)
            }
        }
        else if let Some(global) =  self.get_global(name){
            if size==1{
                Instruction::LoadGlobal(global as u16)
            }
            else{
                Instruction::LoadGlobalStruct(global as u16,size)
            }
        }
        else{
            let upvalue = self.resolve_upvalue(name);
            if size == 1{
                Instruction::LoadUpvalue(upvalue as u16)
            }
            else{
                Instruction::LoadUpvalueStruct(upvalue as u16,size)

            }
        };
        self.emit_instruction(instruction, line);

    }
    fn store_name(&mut self,name:&str,size:usize,line:u32){
        let instruction = if let Some(index) = self.get_local(name){
            if size == 1{
                Instruction::StoreLocal(index as u16)
            }
            else{
                Instruction::StoreLocalStruct(index as u16,size)
            }
        }
        else if let Some(global) = self.get_global(name){
            if size == 1 {
                Instruction::StoreGlobal(global as u16)
            }
            else {
                Instruction::StoreGlobalStruct(global as u16,size)
            }
        }
        else{
            let upvalue = self.resolve_upvalue(name);
            if size == 1{
                Instruction::StoreUpvalue(upvalue as u16)
            }
            else{
                Instruction::StoreUpvalueStruct(upvalue as u16,size)
            }
        };
        self.emit_instruction(instruction,line);
    }
    fn declare_name(&mut self,name:String,size:usize)->usize{
        if self.scope_depth == 0{
            self.globals.push(Global { name,index:self.next_global});
            let global_index = self.next_global;
            self.next_global += size;
            global_index
        }else{
            let local_index = self.next_local;
            self.next_local+=size;
            self.functions.last_mut().unwrap().locals.push(Local { name,index: local_index, depth: self.scope_depth ,is_captured:false});
            self.current_chunk.locals = self.current_chunk.locals.max(self.next_local);
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
            Instruction::Jump(offset) | Instruction::JumpIfFalse(offset) | Instruction::JumpIfTrue(offset) |
             Instruction::JumpIfFalsePeek(offset)|
             Instruction::JumpIfFalseAndPop(offset) => {
                *offset = (next_instr - index - 1) as u16;
            },
            _ => unreachable!()
        }
    }
    fn emit_instruction(&mut self,instruction : Instruction,line:u32){
        self.current_chunk.code.push(instruction);
        self.current_chunk.lines.push(line);
    }
    fn emit_pops(&mut self,n:usize,line:u32){
        if n>1{
            self.emit_instruction(Instruction::PopStruct(n), line);
        }
        else if n==1{
            self.emit_instruction(Instruction::Pop, line);
        }
    }
    fn emit_load_field(&mut self,field_offset:usize,field_size:usize,line:u32){
        if field_size == 1{
            self.emit_instruction(Instruction::LoadField(field_offset as u16), line);
        }
        else{
            self.emit_instruction(Instruction::LoadStructField(field_offset as u16,field_size), line);
        }
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
    fn load_size(&mut self,size:usize,line:u32){
        if size <= i16::MAX as usize {
            self.emit_instruction(Instruction::LoadInt(size as i16),line);
        }
        else{
            self.load_constant(Constant::Int(size as i64), line);
        }

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
            let size = self.get_size_in_stack_slots(ty);
            match &pattern.kind{
                PatternNodeKind::Name(name) => {
                    self.declare_name(name.clone(),size);
                    None

                },
                PatternNodeKind::Tuple(elements) if elements.is_empty() => {
                    self.declare_name(format!("*param_{}",i),size);
                    None
                },
                _ => Some((self.declare_name(format!("*param_{}",i),size),pattern,ty))
            }

        }).collect::<Vec<_>>();

        for (local_index,pattern,ty) in params{
            self.emit_instruction(Instruction::LoadLocal(local_index as u16),pattern.location.start_line);
            self.compile_pattern_assignment(pattern, ty,pattern.location.end_line);
        }

        self.compile_expr(&function.body);
        self.end_scope(function.body.location.end_line);

        if function.body.ty != Type::Never{
            let size = self.get_size_in_stack_slots(&function.body.ty);
            if size == 1{
                self.emit_instruction(Instruction::Return, function.body.location.end_line);
            }
            else{
                self.emit_instruction(Instruction::ReturnStruct(size), function.body.location.end_line);
            }
        }
        disassemble(&function_name, &self.current_chunk,&self.constants);
        let compiled_function = self.functions.pop().expect("Function should still be around");
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
        if compiled_function.upvalues.is_empty(){
            self.load_constant_at_index(func_constant,function.body.location.end_line);
        }
        else{
            self.emit_instruction(Instruction::LoadClosure(func_constant as u16), function.body.location.end_line);
        }
    }
    fn compile_pattern_check(&mut self,pattern:&PatternNode,ty:&Type){
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
            PatternNodeKind::Bool(bool) => {
                self.push_top_of_stack(pattern.location.end_line);
                self.load_bool(*bool, pattern.location.end_line);
                self.emit_instruction(Instruction::Equals, pattern.location.end_line);
            },
            PatternNodeKind::Wildcard => {
                self.load_bool(true, pattern.location.end_line);
            },
            PatternNodeKind::Name(name) => {
                let size = self.get_size_in_stack_slots(ty);
                self.push_top_of_stack(pattern.location.start_line);
                self.define_name(name.clone(), size,pattern.location.end_line);
                self.load_bool(true, pattern.location.end_line);
            },
            PatternNodeKind::Is(name,right_pattern) => {
                let size = self.get_size_in_stack_slots(ty);
                self.push_values_on_top_of_stack(size,right_pattern.location.start_line);
                self.compile_pattern_check(right_pattern,ty);
                let false_jump = self.emit_jump_instruction(Instruction::JumpIfFalse(0xFF), right_pattern.location.end_line);
                self.define_name(name.content.clone(), size,right_pattern.location.end_line);
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
                    self.compile_pattern_check(element,ty);
                    jumps.push(self.emit_jump_instruction(Instruction::JumpIfFalseAndPop(0xFF), element.location.end_line));
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
                let size = self.get_size_in_stack_slots(ty);
                for (field_name,field_pattern) in fields{

                }
            },
            PatternNodeKind::Array(before,ignore ,after) => {
                let total_length = before.len() + after.len();
                self.push_top_of_stack(pattern.location.start_line);
                self.emit_instruction(Instruction::GetArrayLength, pattern.location.start_line);
                self.load_int(total_length as i64, pattern.location.start_line);
                match ignore{
                    Some(_) => {
                        self.emit_instruction(Instruction::GreaterEqualsInt,pattern.location.start_line);
                    },
                    None => {
                        self.emit_instruction(Instruction::Equals,pattern.location.start_line);
                    }
                }
                let length_jump = self.emit_jump_instruction(Instruction::JumpIfFalse(0xFF), pattern.location.start_line);
                let mut jumps = vec![length_jump];
                for (i,pattern) in before.iter().enumerate(){
                    self.push_top_of_stack(pattern.location.start_line);
                    self.load_int(i as i64, pattern.location.start_line);
                    self.emit_instruction(Instruction::LoadIndex, pattern.location.start_line);
                    self.compile_pattern_check(pattern,ty);
                    jumps.push(self.emit_jump_instruction(Instruction::JumpIfFalseAndPop(0xFF), pattern.location.end_line));
                }

                if let Some(ignore) = ignore.as_ref(){
                    if !after.is_empty(){
                        self.push_top_of_stack(ignore.location.start_line);
                        self.emit_instruction(Instruction::GetArrayLength, ignore.location.start_line);
                        self.load_int(after.len() as i64, ignore.location.start_line);
                        self.emit_instruction(Instruction::SubtractInt, ignore.location.start_line);
                        let mut after_jumps = Vec::new();
                        for (i,pattern) in after.iter().enumerate(){
                            self.push_slots_below_to_top(2, pattern.location.start_line);
                            self.push_slots_below_to_top(2, pattern.location.start_line);
                            if i > 0{
                                self.load_int(i as i64, pattern.location.start_line);
                                self.emit_instruction(Instruction::AddInt, pattern.location.start_line);
                            }
                            self.emit_instruction(Instruction::LoadIndex, pattern.location.start_line);
                            self.compile_pattern_check(pattern,ty);
                            let false_jump = self.emit_jump_instruction(Instruction::JumpIfFalseAndPop(0xFF), pattern.location.end_line);
                            after_jumps.push(false_jump);

                        }
                        self.emit_instruction(Instruction::Pop,pattern.location.end_line);
                        let skip_jump = self.emit_jump_instruction(Instruction::Jump(0xFF), pattern.location.end_line);
                        for jump in after_jumps{
                            self.patch_jump(jump);
                        }
                        self.emit_instruction(Instruction::Pop,pattern.location.end_line);
                        let end_jump  = self.emit_jump_instruction(Instruction::Jump(0xFF), pattern.location.end_line);
                        jumps.push(end_jump);
                        self.patch_jump(skip_jump);
                    }
                }
                else{
                    for (i,pattern) in after.iter().enumerate(){
                        self.push_top_of_stack(pattern.location.start_line);
                        self.load_int((i+before.len()) as i64, pattern.location.start_line);
                        self.emit_instruction(Instruction::LoadIndex, pattern.location.start_line);
                        self.compile_pattern_check(pattern,ty);
                        let false_jump = self.emit_jump_instruction(Instruction::JumpIfFalse(0xFF), pattern.location.end_line);
                        self.emit_instruction(Instruction::Pop, pattern.location.end_line);
                        let true_jump = self.emit_jump_instruction(Instruction::Jump(0xFF), pattern.location.end_line);
                        self.patch_jump(false_jump);
                        self.emit_instruction(Instruction::Pop, pattern.location.end_line);
                        let end_jump = self.emit_jump_instruction(Instruction::Jump(0xFF), pattern.location.end_line);
                        jumps.push(end_jump);
                        self.patch_jump(true_jump);
                    }
                }
                self.load_bool(true, pattern.location.end_line);
                let end_jump = self.emit_jump_instruction(Instruction::Jump(0xFF), pattern.location.end_line);
                for jump in jumps{
                    self.patch_jump(jump);
                }
                self.load_bool(false, pattern.location.end_line);
                self.patch_jump(end_jump);
            },
            
        }
    }
    fn compile_print(&mut self,ty:&Type,after:u8,line:u32){
        match ty{
            Type::Unit|Type::Bool|Type::Int|Type::Float|Type::Array(_)|Type::String|Type::Function {.. } => {
                self.emit_instruction(Instruction::PrintValue(Some(after)), line);
            },
            Type::Struct { id,.. } => {
                let field_count = self.get_struct_info(id).fields.len();
                let has_fields = field_count>0;
                let size = self.get_size_in_stack_slots(ty);
                self.load_string(format!("{}",ty), line);
                self.emit_instruction(Instruction::PrintValue(Some(if !has_fields {after} else {b'{'})), line);
                if has_fields{
                    for (i,(field_name,field_type)) in self.get_fields(ty).into_iter().enumerate(){
                        self.emit_instruction(Instruction::LoadStackTopOffset(size), line);
                        let field_offset = self.get_field_offset(ty, &field_name);
                        let field_size = self.get_size_in_stack_slots(&field_type);
                        self.emit_load_field(field_offset, field_size, line);
                        self.compile_print(&field_type, if i < field_count-1 { b','} else { b'}'} , line);

                    }
                    self.emit_pops(size, line);
                    self.emit_instruction(Instruction::PrintAscii(after), line);
                }
            },
            Type::Tuple(elements) => {
                self.emit_instruction(Instruction::PrintAscii('(' as u8), line);
                let mut field_offset = 0;
                let size = self.get_size_in_stack_slots(ty);
                for (i,element) in elements.iter().enumerate(){
                    self.emit_instruction(Instruction::LoadStackTopOffset(size), line);
                    let element_size = self.get_size_in_stack_slots(element);
                    self.emit_load_field(field_offset, element_size, line);
                    self.compile_print(&element, if i < elements.len()-1 { b','} else { b')'} , line);
                    field_offset += element_size;
                }
                self.emit_pops(size, line);
                self.emit_instruction(Instruction::PrintAscii(after), line);
            },
            Type::Never => {},
            Type::Param { .. } => unreachable!("All values that get printed should be fully substituted!"),
            ty => todo!("Add support for {}.",ty)
        }
    }
    fn compile_lvalue(&mut self,expr:&TypedExprNode){
        match &expr.kind{
            TypedExprNodeKind::Get(name) => {
                if let Some(local) = self.get_local(name){
                    self.emit_instruction(Instruction::LoadLocalRef(local as u16), expr.location.end_line);
                }
                else if let Some(global) = self.get_global(name){
                    self.emit_instruction(Instruction::LoadGlobalRef(global as u16), expr.location.end_line);
                }
                else{
                    let _upvalue = self.resolve_upvalue(name);
                    todo!("UPVALUE REFS")
                }
            },
            TypedExprNodeKind::Field(lhs, field) => {
                self.compile_lvalue(lhs);
                let field_offset = self.get_field_offset(&lhs.ty, &field.content);
                self.emit_instruction(Instruction::LoadFieldRef(field_offset as u16), field.location.end_line);
            }
            _ => {
                self.compile_expr(expr);
                self.emit_instruction(Instruction::LoadStackTopOffset(self.get_size_in_stack_slots(&expr.ty)),expr.location.end_line);
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
            },
            TypedExprNodeKind::Get(name) => {
                self.load_name(name,self.get_size_in_stack_slots(&expr.ty),expr.location.end_line);
            },
            TypedExprNodeKind::Print(args) => {
                for (i,arg) in args.iter().enumerate(){
                    self.compile_expr(arg);
                    self.compile_print(&arg.ty,if i<args.len()-1 {b' '} else{b'\n'},arg.location.end_line);
                }
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
                self.end_scope(expr.location.end_line);
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
                    self.compile_pattern_check(&arm.pattern,&matchee.ty);
                    let false_jump = self.emit_jump_instruction(Instruction::JumpIfFalse(0xFF), arm.pattern.location.end_line);
                    self.emit_instruction(Instruction::Pop, arm.pattern.location.end_line);
                    self.compile_expr(&arm.expr);
                    self.end_scope(arm.expr.location.end_line);
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
                let size = self.get_size_in_stack_slots(&rhs.ty);
                match &lhs.kind{
                    TypedAssignmentTargetKind::Name(name) => {
                        self.compile_expr(rhs);
                        for _ in 0..size{
                            self.push_slots_below_to_top(size as u16, rhs.location.end_line);
                        }
                        self.store_name(name, size,rhs.location.end_line);

                    },
                    TypedAssignmentTargetKind::Index { lhs, rhs:index } => {
                        self.compile_expr(lhs);
                        self.compile_expr(index);
                        self.compile_expr(rhs);
                        self.emit_instruction(Instruction::StoreIndex, rhs.location.end_line);
                        self.emit_instruction(Instruction::LoadIndex, rhs.location.end_line);
                    },
                    TypedAssignmentTargetKind::Field { lhs, name } => {
                        self.compile_lvalue(lhs);
                        self.compile_expr(rhs);
                        let field_index= self.get_field_offset(&lhs.ty,&name.content);
                        if size == 1{
                            self.emit_instruction(Instruction::StoreField(field_index as u16), rhs.location.end_line);
                            self.emit_instruction(Instruction::LoadField(field_index as u16), rhs.location.end_line);
                        }
                        else{
                            self.emit_instruction(Instruction::StoreStructField(field_index as u16,size), rhs.location.end_line);
                            self.emit_instruction(Instruction::LoadStructField(field_index as u16,size), rhs.location.end_line);

                        }
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
                self.emit_instruction(Instruction::Call(args.iter().map(|arg| self.get_size_in_stack_slots(&arg.ty)).sum::<usize>() as u16),expr.location.end_line);
            },
            TypedExprNodeKind::Return { expr:return_expr } => {
                if let Some(expr) = return_expr.as_ref(){
                    self.compile_expr(expr);
                    let size = self.get_size_in_stack_slots(&expr.ty);
                    if size == 1{
                        self.emit_instruction(Instruction::Return, expr.location.end_line);
                    }
                    else {
                        self.emit_instruction(Instruction::ReturnStruct(size), expr.location.end_line);
                    }
                }
                else{
                    self.emit_instruction(Instruction::LoadUnit, expr.location.end_line);
                    self.emit_instruction(Instruction::Return, expr.location.end_line);
                }
            },
            TypedExprNodeKind::GetGeneric { name, args } => {
                let Some((index,generic_function)) = self.generic_functions.iter().enumerate().rev()
                    .find(|(_,generic_function)| &generic_function.name == name) else {
                        self.load_name(name, 1,expr.location.end_line);
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
                match (&lhs.ty,&field_name.content as &str){
                    (Type::Array(..),"length") => {
                        self.compile_expr(lhs);
                        self.emit_instruction(Instruction::GetArrayLength, field_name.location.end_line);
                    },
                    (ty @ Type::Struct {id,.. },field) => {
                        if matches!(ty,Type::EnumVariant {.. }) {
                            todo!("Re-implement Enum variants")
                        }
                        self.compile_lvalue(lhs);
                        let field = self.get_field_offset(ty, field);
                        let field_size = self.get_size_in_stack_slots(&expr.ty);
                        if field_size == 1{
                            self.emit_instruction(Instruction::LoadField(field as u16),field_name.location.end_line);
                        }
                        else{
                            self.emit_instruction(Instruction::LoadStructField(field as u16,field_size),field_name.location.end_line); 
                        }
                    }
                    _ => unreachable!("{:?}",lhs.ty)
                }
            },
            TypedExprNodeKind::StructInit { kind,fields } => {
                match kind{
                    InitKind::Struct(_) => {
                        self.emit_instruction(Instruction::StackAlloc(Some(self.get_size_in_stack_slots(&expr.ty))),expr.location.start_line);
                        for (field_name,field_expr) in fields{
                            let field_offset = self.get_field_offset(&expr.ty, &field_name);
                            if field_offset >= u16::MAX as usize{
                                todo!("Add support for wider fields")
                            }
                            self.compile_expr(field_expr);
                            let size = self.get_size_in_stack_slots(&field_expr.ty);
                            if size == 1{
                                self.emit_instruction(Instruction::StoreField(field_offset as u16), field_expr.location.end_line);
                            }
                            else{
                                self.emit_instruction(Instruction::StoreStructField(field_offset as u16,size), field_expr.location.end_line);
                            }
                        }
                        self.emit_instruction(Instruction::Pop,expr.location.end_line);
                    },
                    InitKind::Variant(.. ) => {
                        todo!()
                    }
                }
            },
            TypedExprNodeKind::MethodCall { lhs, method, args } => {
                self.load_name(&format!("{}::{}",lhs.ty,method.content), 1,lhs.location.start_line);
                self.compile_expr(lhs);
                for arg in args{
                    self.compile_expr(arg);
                }
                self.emit_instruction(Instruction::Call((args.len()+1) as u16), expr.location.end_line);
            },
            TypedExprNodeKind::GetMethod { ty, method } => {
                self.load_name(&format!("{}::{}",ty,method.content),1,method.location.end_line);
            }
        }
    }
    fn compile_pattern_assignment(&mut self,pattern:&PatternNode,ty:&Type,line:u32){
        match &pattern.kind{
            PatternNodeKind::Name(name) => {
                self.define_name(name.clone(),self.get_size_in_stack_slots(ty),line);
            },
            PatternNodeKind::Tuple(patterns) => {
                if !patterns.is_empty(){
                    let size = self.get_size_in_stack_slots(ty);
                    let Type::Tuple(elements) = ty else {
                        unreachable!()
                    };
                    let mut field_offset = 0;
                    for (pattern,ty) in patterns.iter().zip(elements.iter()){
                        let field_size = self.get_size_in_stack_slots(ty);
                        self.emit_instruction(Instruction::LoadStackTopOffset(size), line);
                        self.emit_load_field(field_offset, field_size, line);
                        self.compile_pattern_assignment(pattern, ty,line);
                        field_offset += field_size;
                    }
                }
                else{
                    self.emit_instruction(Instruction::Pop,line)
                }
            },
            PatternNodeKind::Struct { fields,ty } => {
                todo!("Pattern struct assigmnent")
            },
            PatternNodeKind::Wildcard => {
                self.emit_instruction(Instruction::Pop, line);
            },
            PatternNodeKind::Array(before, ignore, after) if before.is_empty() && after.is_empty() && ignore.is_some() => {
                self.emit_instruction(Instruction::Pop, line);
            },
            PatternNodeKind::Is(name, right_pattern) => {
                self.emit_instruction(Instruction::Copy(1), line);
                self.define_name(name.content.clone(),1,line);
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
                    self.emit_pops(self.get_size_in_stack_slots(&expr.ty), expr.location.end_line);
                }
            },
            TypedStmtNode::ExprWithSemi(expr) => {
                self.compile_expr(expr);
                if expr.ty != Type::Never{
                    self.emit_pops(self.get_size_in_stack_slots(&expr.ty), expr.location.end_line);
                }
            },
            TypedStmtNode::Let { pattern, expr } => {
                self.compile_expr(expr);
                self.compile_pattern_assignment(pattern, &expr.ty,expr.location.end_line);
            },
            TypedStmtNode::Fun { name, function} => {
                    let name= name.content.clone();
                    let index = self.declare_name(name.clone(),1);
                    self.compile_function(function,name.clone(),None);
                    self.emit_define_instruction(index,1,function.body.location.end_line);
                
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
                    self.define_name(method_name, 1,method.function.body.location.end_line);
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
        self.define_name("input".to_string(), 1,1);

        self.load_constant(Constant::NativeFunction(Rc::new(NativeFunction{
            name : "panic".to_string(),
            function : native_panic
        })), 1);
        self.define_name("panic".to_string(), 1,1);
        
        self.load_constant(Constant::NativeFunction(Rc::new(NativeFunction{
            name : "push".to_string(),
            function : native_push
        })), 1);
        self.define_name("push".to_string(), 1,1);

        
        self.load_constant(Constant::NativeFunction(Rc::new(NativeFunction{
            name : "pop".to_string(),
            function : native_pop
        })), 1);
        self.define_name("pop".to_string(), 1,1);

        
        self.load_constant(Constant::NativeFunction(Rc::new(NativeFunction{
            name : "parse_int".to_string(),
            function : native_parse_int
        })), 1);
        self.define_name("parse_int".to_string(), 1,1);
        self.compile_stmts(&stmts);
        let last_line = self.current_chunk.lines.last().copied().unwrap_or(1);
        self.emit_instruction(Instruction::LoadUnit,last_line);
        self.emit_instruction(Instruction::Return,last_line);
        disassemble("<main>", &self.current_chunk,&self.constants);
        Ok(Program{constants:self.constants,chunk:self.current_chunk,names:self.names.into_iter().map(|name| name.into()).collect()})
    }
}