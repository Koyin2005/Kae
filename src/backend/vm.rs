use std::rc::Rc;

use fxhash::FxHashMap;

use crate::backend::disassembly::disassemble_instruction;

use super::{instructions::{Chunk, Constant, Instruction, Program, ProgramMetadata, StructInfo}, objects::{Heap, Object}, values::{Closure, FieldRef, Function, Record, Upvalue, Value, VariantRecord}};

pub const DEBUG_TRACE_EXEC : bool = false;
pub const MAX_STACK_SIZE : usize = 255;
pub const MAX_FRAMES : usize = 64;

pub struct RuntimeError;
#[derive(Default)]
pub struct CallFrame{
    function : Rc<Function>,
    closure : Option<Object>,
    ip : usize,
    bp : usize
}
pub struct VM{
    names : Vec<Rc<str>>,
    stack : Vec<Value>,
    constants : Box<[Constant]>,
    metadata : Box<[ProgramMetadata]>,
    frames : Vec<CallFrame>,
    globals : FxHashMap<usize,Value>,
    open_upvalues : Vec<Object>,
    pub heap : Heap,
}
impl VM{

    pub fn new(program : Program)->Self{
        Self{
            names : program.names,
            open_upvalues : Vec::new(),
            stack:Vec::from_iter(std::iter::repeat(Value::Int(0)).take(program.chunk.locals)),
            constants:program.constants.into_boxed_slice(),
            heap:Heap::default(),
            frames : vec![CallFrame{
                function : Rc::new(Function{
                    name : "<main>".to_string(),
                    chunk : program.chunk,
                    upvalues : Vec::new()
                }),
                closure:None,
                ip : 0,
                bp : 0
            }],
            globals : FxHashMap::default(),
            metadata:program.metadata.into()
        }
    }
    fn push(&mut self,value:Value)->Result<(),RuntimeError>{
        if self.stack.len() >= MAX_STACK_SIZE{
            self.runtime_error("Stack overflow.");
            return Err(RuntimeError);
        }
        self.stack.push(value);
        Ok(())
    }
    fn pop_size(&mut self)->usize{
        let Value::Int(size) = self.pop() else {
            unreachable!("Expected an int.")
        };
        size as usize
    }
    fn pop_n(&mut self,n:usize){
        self.stack.truncate(self.stack.len() - n);
    }
    fn pop(&mut self)->Value{
        self.stack.pop().unwrap()
    }
    fn pop_values(&mut self,values:usize)->Vec<Value>{
        let mut values  = (0..values).map(|_| self.pop()).collect::<Vec<_>>();
        values.reverse();
        values
    }
    fn peek(&self,offset:usize)->Value{
        self.stack[self.stack.len() - offset - 1].clone()
    }
    fn peek_ref(&self,offset:usize)->&Value{
        &self.stack[self.stack.len() - offset - 1]
    }
    fn peek_mut(&mut self,offset:usize)->&mut Value{
        let index = self.stack.len() - offset - 1;
        &mut self.stack[index]
    }
    fn current_chunk(&self)->&Chunk{
        let index = self.frames.len()-1;
        &self.frames[index].function.chunk
    }
    fn current_frame(&self)->&CallFrame{
        let index = self.frames.len()-1;
        &self.frames[index]
    }
    fn current_frame_mut(&mut self)->&mut CallFrame{
        let index = self.frames.len()-1;
        &mut self.frames[index]
    }
    fn read_instruction(&mut self)->Instruction{
        let frame = self.current_frame_mut();
        frame.ip+=1;
        frame.function.chunk.code[frame.ip-1]
    }
    pub fn reset(&mut self,program:Program){
        self.frames = vec![CallFrame{
            function : Rc::new(Function { name: "<main>".to_string(), chunk:program.chunk,upvalues:Vec::new() }),
            closure : None,
            ip : 0,
            bp : 0,
        }];
        self.stack = vec![Value::Int(0); self.current_chunk().locals];
        self.constants = program.constants.into_boxed_slice();
        self.names = program.names;
    }
    fn load_constant(&mut self,index: usize)-> Value{
        match self.constants[index].clone(){
            Constant::Int(int) => Value::Int(int),
            Constant::String(string) => {
                Value::String(Object::new_string(&mut self.heap, string.into()))
            },
            Constant::Float(float) => Value::Float(float),
            Constant::Function(function) => Value::Function(Object::new_function(&mut self.heap, function)),
            Constant::NativeFunction(function) => Value::NativeFunction(Object::new_native_function(&mut self.heap, function))
        }
    }
    fn store_top(&mut self,value:Value){
        let index =self.stack.len() - 1;
        self.stack[index] = value;
    }
    fn push_frame(&mut self,function:Rc<Function>,arg_count:usize,closure:Option<Object>)->Result<(), RuntimeError>{
        let bp = self.stack.len()-arg_count -1;
        self.stack.remove(bp);
        self.stack.extend(std::iter::repeat(Value::Int(0)).take(function.chunk.locals - arg_count));
        self.frames.push(CallFrame{
            closure,
            function,
            ip : 0,
            bp
        });
        if self.frames.len() > MAX_FRAMES{
            self.runtime_error("Exceeded max call frames.");
            return Err(RuntimeError);
        }
        Ok(())
    }
    fn capture_upvalue(&mut self,location:usize)->Object{
        for upvalue in &self.open_upvalues{
            if let Upvalue::Open { location:upvalue_location } = upvalue.as_upvalue(&self.heap){
                if upvalue_location == location{
                    return *upvalue;
                }
            }
        }
        let new_upvalue = Object::new_upvalue(&mut self.heap, Upvalue::Open { location });
        self.open_upvalues.push(new_upvalue);
        new_upvalue
    }
    fn close_upvalues(&mut self,location:usize){
        let mut i = 0;
        while i != self.open_upvalues.len() {
            let upvalue = self.open_upvalues[i];
            let upvalue = upvalue.as_upvalue_mut(&mut self.heap);
            if let Upvalue::Open { location:upvalue_location } = upvalue{
                if *upvalue_location >= location{
                    self.open_upvalues.remove(i);
                    *upvalue = Upvalue::Closed(self.stack[*upvalue_location].clone());

                }
                else{
                    i+=1;
                }
            }
        }
    }
    fn get_ref_mut(&mut self,reference:Value)->&mut Value{
        match reference{
            Value::GlobalAddress(global) => {
                self.globals.get_mut(&global).expect("Should be a valid global")
            },
            Value::StackAddress(address)=> {
                self.stack.get_mut(address).expect("Should be a valid stack address")
            },
            Value::FieldRef(field_ref) => {
                let (Value::Record(record) | Value::VariantRecord(VariantRecord { record_data:record,.. })) = self.get_ref_mut(field_ref.base_ref) else {
                    panic!("Expect a valid record")
                };
                &mut record.fields[field_ref.field_offset]
            },
            Value::IndexRef(index_ref) => {
                let Value::Array(array) = index_ref.base_ref else {
                    panic!("Expect valid array")
                };
                &mut array.as_array_mut(&mut self.heap)[index_ref.field_offset]
            },
            _ => panic!("Cannot get a reference")
        }
    }
    fn get_ref(&self,reference:&Value)->&Value{
        match reference{
            Value::GlobalAddress(global) => {
                self.globals.get(global).expect("Should be a valid global")
            },
            Value::StackAddress(address) => {
                self.stack.get(*address).expect("Should be a valid stack address")
            },
            Value::FieldRef(field_ref) => {
                let (Value::Record(record) | Value::VariantRecord(VariantRecord { record_data:record,.. }))= self.get_ref(&field_ref.base_ref) else {
                    panic!("Expect a valid record")
                };
                &record.fields[field_ref.field_offset]
            },
            Value::IndexRef(index_ref) => {
                let Value::Array(array) = index_ref.base_ref else {
                    panic!("Expect valid array")
                };
                &array.as_array(&self.heap)[index_ref.field_offset]
            },
            _ => panic!("Cannot get a reference got {:?}",reference)
        }
    }
    pub fn runtime_error(&self,message:&str){
        eprintln!("Error : {}",message);
        for frame in self.frames.iter().rev(){
            eprintln!("[line {}] in {}",frame.function.chunk.lines[frame.ip.min(frame.function.chunk.lines.len()-1)],frame.function.name);
        }
    }
    pub fn run(&mut self)->Result<(),RuntimeError>{
        let mut debug_buffer = if DEBUG_TRACE_EXEC { Some(String::new())} else {None};
        while self.current_frame().ip < self.current_chunk().code.len(){
            if DEBUG_TRACE_EXEC{
                for value in self.stack.iter(){
                    print!("[{}] ",value.format(&self.heap));
                }
                println!();
                for value in self.stack.iter(){
                    print!("[{}] ",value.format(&self.heap));
                }
                println!();
                if let Some(debug_buffer) = debug_buffer.as_ref(){
                    println!("{:?}",debug_buffer);
                }
                let instruction = self.current_chunk().code[self.current_frame().ip];
                print!("{} ",self.current_frame().function.name);
                disassemble_instruction(self.current_chunk(), self.current_frame().ip, instruction,&self.constants);
            }
            match self.read_instruction(){
                Instruction::LoadInt(value) => {
                    self.push(Value::Int(value as i64))?;
                },
                Instruction::LoadBool(bool) => {
                    self.push(Value::Bool(bool))?;
                },
                Instruction::LoadUnit => {
                    self.push(Value::Unit)?;
                },
                Instruction::LoadConstant(constant) => {
                    let constant = self.load_constant(constant as usize);
                    self.push(constant)?;
                },
                Instruction::LoadClosure(constant) => {
                    let Constant::Function(function) = self.constants[constant as usize].clone() else {
                        panic!("Expected a function")
                    };
                    let upvalues = function.upvalues.iter().copied().map(|(index,is_local)|{
                        if is_local{
                            self.capture_upvalue(self.current_frame().bp + index)
                        }
                        else{
                            let closure = self.current_frame().closure.expect("Can only capture a closure.");
                            closure.as_closure(&self.heap).upvalues[index]
                        }
                    }).collect();
                    let closure = Value::Closure(Object::new_closure(&mut self.heap, Closure { upvalues, function }));
                    self.push(closure)?;
                },
                Instruction::CloseUpvalue(local) => {
                    self.close_upvalues(self.current_frame().bp + local as usize);
                }
                Instruction::AddInt => {
                    let Value::Int(b) = self.pop() else {
                        panic!("Expected an int.")
                    };
                    let Value::Int(a) = self.peek(0) else {
                        panic!("Expected an int.")
                    };
                    self.store_top(Value::Int(a.overflowing_add(b).0));
                },
                Instruction::SubtractInt => {
                    let Value::Int(b) = self.pop() else {
                        panic!("Expected an int.")
                    };
                    let Value::Int(a) = self.peek(0) else {
                        panic!("Expected an int.")
                    };
                    self.store_top(Value::Int(a.overflowing_sub(b).0));
                },
                Instruction::MultiplyInt => {
                    let Value::Int(b) = self.pop() else {
                        panic!("Expected an int.")
                    };
                    let Value::Int(a) = self.peek(0) else {
                        panic!("Expected an int.")
                    };
                    self.store_top(Value::Int(a.overflowing_mul(b).0));
                },
                Instruction::DivideInt => {
                    let Value::Int(b) = self.pop() else {
                        panic!("Expected an int.")
                    };
                    let Value::Int(a) = self.peek(0) else {
                        panic!("Expected an int.")
                    };
                    if b == 0{
                            self.runtime_error("Division by zero.");
                            return Err(RuntimeError);
                    }
                    self.store_top(Value::Int(a.overflowing_div(b).0));
                },
                Instruction::LesserInt => {
                    let Value::Int(b) = self.pop() else {
                        panic!("Expected an int.")
                    };
                    let Value::Int(a) = self.peek(0) else {
                        panic!("Expected an int.")
                    };
                    self.store_top(Value::Bool(a<b));
                },
                Instruction::GreaterInt => {
                    let Value::Int(b) = self.pop() else {
                        panic!("Expected an int.")
                    };
                    let Value::Int(a) = self.peek(0) else {
                        panic!("Expected an int.")
                    };
                    self.store_top(Value::Bool(a>b));
                },
                Instruction::LesserEqualsInt => {
                    let Value::Int(b) = self.pop() else {
                        panic!("Expected an int.")
                    };
                    let Value::Int(a) = self.peek(0) else {
                        panic!("Expected an int.")
                    };
                    self.store_top(Value::Bool(a<=b));
                },
                Instruction::GreaterEqualsInt => {
                    let Value::Int(b) = self.pop() else {
                        panic!("Expected an int.")
                    };
                    let Value::Int(a) = self.peek(0) else {
                        panic!("Expected an int.")
                    };
                    self.store_top(Value::Bool(a>=b));
                },
                Instruction::NegateInt => {
                    let Value::Int(a) = self.peek(0) else {
                        panic!("Expected an int.")
                    };
                    self.store_top(Value::Int(-a));
                },
                Instruction::AddFloat => {
                    let Value::Float(b) = self.pop() else {
                        panic!("Expected a float.")
                    };
                    let Value::Float(a) = self.peek(0) else {
                        panic!("Expected a float.")
                    };
                    self.store_top(Value::Float(a+b));
                },
                Instruction::SubtractFloat => {
                    let Value::Float(b) = self.pop() else {
                        panic!("Expected a float.")
                    };
                    let Value::Float(a) = self.peek(0) else {
                        panic!("Expected a float.")
                    };
                    self.store_top(Value::Float(a-b));
                },
                Instruction::MultiplyFloat => {
                    let Value::Float(b) = self.pop() else {
                        panic!("Expected a float.")
                    };
                    let Value::Float(a) = self.peek(0) else {
                        panic!("Expected a float.")
                    };
                    self.store_top(Value::Float(a*b));
                },
                Instruction::DivideFloat => {
                    let Value::Float(b) = self.pop() else {
                        panic!("Expected a float.")
                    };
                    let Value::Float(a) = self.peek(0) else {
                        panic!("Expected a float.")
                    };
                    self.store_top(Value::Float(a/b));
                },
                Instruction::LesserFloat => {
                    let Value::Float(b) = self.pop() else {
                        panic!("Expected a float.")
                    };
                    let Value::Float(a) = self.peek(0) else {
                        panic!("Expected a float.")
                    };
                    self.store_top(Value::Bool(a<b));
                },
                Instruction::GreaterFloat => {
                    let Value::Float(b) = self.pop() else {
                        panic!("Expected a float.")
                    };
                    let Value::Float(a) = self.peek(0) else {
                        panic!("Expected a float.")
                    };
                    self.store_top(Value::Bool(a>b));
                },
                Instruction::LesserEqualsFloat => {
                    let Value::Float(b) = self.pop() else {
                        panic!("Expected a float.")
                    };
                    let Value::Float(a) = self.peek(0) else {
                        panic!("Expected a float.")
                    };
                    self.store_top(Value::Bool(a<=b));
                },
                Instruction::GreaterEqualsFloat => {
                    let Value::Float(b) = self.pop() else {
                        panic!("Expected a float.")
                    };
                    let Value::Float(a) = self.peek(0) else {
                        panic!("Expected a float.")
                    };
                    self.store_top(Value::Bool(a>=b));
                },
                Instruction::NegateFloat => {
                    let Value::Float(a) = self.peek(0) else {
                        panic!("Expected a float.")
                    };
                    self.store_top(Value::Float(-a));
                }
                Instruction::Equals => {
                    let b = self.pop();
                    let a = self.peek(0);
                    self.store_top(Value::Bool(a.is_equal(&b, &self.heap)));
                },
                Instruction::NotEquals => {
                    let b = self.pop();
                    let a = self.peek(0);
                    self.store_top(Value::Bool(!a.is_equal(&b, &self.heap)));
                }
                Instruction::Concatenate => {
                    let Value::String(b) = self.pop() else {
                        unreachable!("Expected a string.")
                    };
                    let Value::String(a) = self.pop() else {
                        unreachable!("Expected a string.")
                    }; 
                    let b = b.as_string(&self.heap);
                    let a  = a.as_string(&self.heap);
                    let mut result = String::from(a);
                    result.push_str(b);
                    let result = Object::new_string(&mut self.heap,result.into());
                    self.push(Value::String(result))?;
                }
                Instruction::BuildArray(elements) => {
                    let elements = self.pop_values(elements);
                    let array = Object::new_array(&mut self.heap, elements);
                    self.push(Value::Array(array))?;
                }
                Instruction::LoadFieldRef(field) => {
                    let base_ref = self.pop();
                    self.push(Value::FieldRef(Box::new(FieldRef{
                        base_ref,
                        field_offset:field as usize
                    })))?;
                }
                Instruction::LoadField(field) => {
                    match self.pop(){
                        Value::Record(record) | Value::VariantRecord(VariantRecord { record_data:record,.. }) => {
                            let field_value = record.fields.to_vec().swap_remove(field as usize);
                            self.push(field_value)?;
                        },
                        reference => {
                             let (Value::Record(record) | Value::VariantRecord(VariantRecord { record_data:record,.. })) = self.get_ref(&reference) else {
                                unreachable!("Expected a record.")
                            };
                            self.push(record.fields[field as usize].clone())?;
                        },
                    }

                },
                Instruction::StoreField(field) => {
                    let value = self.pop();
                    match self.peek_mut(0){
                        Value::Record(record) | Value::VariantRecord(VariantRecord { record_data:record,.. })=> {
                            record.fields[field as usize] = value;
                        },
                        reference => {
                            let reference = reference.clone();
                            let (Value::Record(record) | Value::VariantRecord(VariantRecord { record_data:record,.. })) = self.get_ref_mut(reference) else {
                                panic!("Expected a valid record.")
                            };
                            record.fields[field as usize] = value;
                        }
                    }
                },
                Instruction::LoadIndirect => {
                    let reference = self.pop();
                    self.push(self.get_ref(&reference).clone())?;
                },
                Instruction::StoreIndirect => {
                    let value = self.pop();
                    let address = self.peek(0);
                    *self.get_ref_mut(address) = value;
                },  
                Instruction::GetArrayLength => {
                    let Value::Array(array) = self.peek_ref(0) else {
                        unreachable!("Expected an array got {}",self.peek_ref(0).format(&self.heap))
                    };
                    let length = array.as_array(&self.heap).len();
                    self.push(Value::Int(length as i64))?;
                },
                Instruction::StoreLocal(local) => {
                    let value = self.pop();
                    let location = local as usize + self.current_frame().bp;
                    self.stack[location] = value;
                },
                Instruction::LoadLocal(local) => {
                    let location = local as usize + self.current_frame().bp;
                    self.push(self.stack[location].clone())?;
                },
                Instruction::LoadLocalRef(local) => {
                    self.push(Value::StackAddress(self.current_frame().bp + local as usize))?;
                },
                Instruction::LoadGlobal(global) => {
                    self.push(self.globals[&(global as usize)].clone())?;
                },
                Instruction::LoadGlobalRef(global) => {
                    self.push(Value::GlobalAddress(global as usize))?;
                }
                Instruction::StoreGlobal(global) => {
                    let value = self.pop();
                    self.globals.insert(global as usize, value);
                },
                Instruction::LoadUpvalue(upvalue) => {
                    let upvalue = self.current_frame().closure.expect("Can only use upvalues with closure").as_closure(&self.heap).upvalues[upvalue as usize].as_upvalue(&self.heap);
                   
                    self.push(match upvalue {
                        Upvalue::Closed(value) => value,
                        Upvalue::Open { location } => self.stack[location].clone()
                    })?;
                },
                Instruction::StoreUpvalue(upvalue) => {
                    let value = self.pop();
                    let upvalue = self.current_frame().closure.expect("Can only use upvalues with closure").as_closure(&self.heap).upvalues[upvalue as usize].as_upvalue_mut(&mut self.heap);
                    match upvalue{
                        Upvalue::Closed(closed) => *closed = value,
                        Upvalue::Open { location } => self.stack[*location] = value
                    }
                },
                Instruction::LoadIndex => {
                    let Value::Int(index) = self.pop() else {
                        panic!("Expected an int.")
                    };
                    let Value::Array(array) = self.pop() else{
                        panic!("Expected a list.")
                    };
                    let array = array.as_array_mut(&mut self.heap);
                    let len = array.len();
                    if index >= 0 && (index as usize) < len {
                        let value = array[index as usize].clone();
                        self.push(value)?;
                    }
                    else{
                        self.runtime_error(&format!("Index out of range, index was {} but len was {}.",index,len));
                        return Err(RuntimeError);
                    }
                },
                Instruction::StoreIndex => {
                    let value = self.pop();
                    let Value::Int(index) = self.peek(0) else {
                        panic!("Expected an int.")
                    };
                    let Value::Array(array) = self.peek(1) else{
                        panic!("Expected a list.")
                    };
                    let array = array.as_array_mut(&mut self.heap);
                    let len = array.len();
                    if index >= 0 && (index as usize) < len {
                        array[index as usize] = value;
                    }
                    else{
                        self.runtime_error(&format!("Index out of range, index was {} but len was {}.",index,len));
                        return Err(RuntimeError);
                    }
                },
                Instruction::LoadIndexRef => {
                    let Value::Int(index) = self.pop() else {
                        panic!("Expected an int.")
                    };
                    let Value::Array(array) = self.pop() else{
                        panic!("Expected a list.")
                    };
                    let len = array.as_array(&self.heap).len();
                    if index >= 0 && (index as usize) < len {
                        self.push(Value::IndexRef(Box::new(FieldRef { base_ref: Value::Array(array), field_offset: index as usize })))?;
                    }
                    else{
                        self.runtime_error(&format!("Index out of range, index was {} but len was {}.",index,len));
                        return Err(RuntimeError);
                    }
                }
                Instruction::Loop(offset) => {
                    self.current_frame_mut().ip -= offset as usize;
                },
                Instruction::Jump(offset) => {
                    self.current_frame_mut().ip += offset as usize;
                },
                Instruction::JumpIfFalsePeek(offset) => {
                    let Value::Bool(condition) = self.peek(0) else {
                        panic!("Expected bool.")
                    };
                    if !condition{
                        self.current_frame_mut().ip += offset as usize;
                    }
                }
                Instruction::JumpIfFalse(offset) => {
                    let Value::Bool(condition) = self.pop() else {
                        panic!("Expected bool.")
                    };
                    if !condition{
                        self.current_frame_mut().ip += offset as usize;
                    }
                },
                Instruction::JumpIfTrue(offset) => {
                    let Value::Bool(condition) = self.pop() else {
                        panic!("Expected bool.")
                    };
                    if condition{
                        self.current_frame_mut().ip += offset as usize;
                    }
                },
                Instruction::JumpIfFalseAndPop(offset) => {
                    let Value::Bool(condition) = self.pop() else {
                        panic!("Expected bool.")
                    };
                    if !condition{
                        self.current_frame_mut().ip += offset as usize;
                    }
                    self.pop();
                },
                Instruction::Rotate(items) => {
                    let items = items as usize;
                    let start = self.stack.len()-items;
                    let end = self.stack.len();
                    self.stack[start..end].reverse();
                }
                Instruction::Pop => {
                    self.pop();
                },
                Instruction::Copy(offset) => {
                    let offset = (offset - 1) as usize;
                    self.push(self.peek(offset))?;
                },
                Instruction::Print(args) => {
                    for (i,offset) in (0..args).rev().enumerate(){
                        if i > 0{
                            if let Some(debug_buffer) = debug_buffer.as_mut(){
                                debug_buffer.push(' ');
                            }
                            else{
                                print!(" ");
                            }
                        }
                        let value = self.peek(offset as usize);
                        if let Some(debug_buffer) = debug_buffer.as_mut(){
                            debug_buffer.push_str(&value.format(&self.heap));
                        }
                        else{
                            value.print(&self.heap);
                        }
                    }
                    self.pop_n(args as usize);
                    if let Some(debug_buffer)  = debug_buffer.as_mut(){
                        println!("{}",debug_buffer);
                        debug_buffer.clear();
                    }
                    else{
                        println!();
                    }
                },
                Instruction::Call(args) => {
                    let arg_count = args as usize;
                    let function = self.peek(arg_count);
                    match function{
                        Value::NativeFunction(function) => {
                            let args = self.pop_values(arg_count);
                            self.pop();
                            let function = function.as_native_function(&self.heap);
                            let result = (function.function)(self,&args)?;
                            self.push(result)?;
                        },
                        Value::Closure(closure) => {
                            self.push_frame(closure.as_closure(&self.heap).function.clone(), arg_count, Some(closure))?;
                        },
                        Value::Function(function) => {
                            self.push_frame(function.as_function(&self.heap), arg_count, None)?;
                        },
                        value => {
                            panic!("Expect function got {}.",value.format(&self.heap))
                        }
                    }

                },
                Instruction::Return => {
                    let value = self.pop();
                    if let Some(frame) = self.frames.pop(){
                        self.close_upvalues(frame.bp);
                        self.stack.truncate(frame.bp);
                        self.push(value)?;
                    }
                    if self.frames.is_empty(){
                        break;
                    }
                },
                Instruction::PopN(n) => {
                    for _ in 0..n{
                        self.pop();
                    }
                },
                Instruction::LoadStackTopOffset(size) => {
                    self.push(Value::StackAddress(self.stack.len() - size))?;
                },
                Instruction::BuildTuple(element_count) => {
                    let elements = &self.stack[self.stack.len()-element_count..];
                    let elements:Box<[Value]> = Box::from(elements);
                    self.pop_n(element_count);
                    self.push(Value::Tuple(elements))?;
                },
                Instruction::BuildRecord(struct_metadata) => {
                    let ProgramMetadata::Struct(struct_info) = &self.metadata[struct_metadata] else {
                        unreachable!("Expected a struct")
                    };
                    let name = struct_info.name.clone();
                    let fields = struct_info.field_count;
                    self.push(Value::Record(Box::new(Record{
                        name,
                        fields:std::iter::repeat(Value::Int(0)).take(fields).collect()
                    })))?;
                },
                Instruction::BuildVariantRecord(variant_metadata) => {
                    let ProgramMetadata::Variant(variant_info) = &self.metadata[variant_metadata] else {
                        unreachable!("Expected a variant")
                    };
                    let name = variant_info.name.clone();
                    let fields = variant_info.field_count;
                    self.push(Value::VariantRecord(VariantRecord{
                            record_data:Box::new(Record{
                                name,
                                fields:std::iter::repeat(Value::Int(0)).take(fields).collect()
                            }),
                            discriminant:variant_info.discriminant
                        }))?;
                },
                Instruction::UnpackTuple => {
                    let Value::Tuple(elements) = self.pop() else {
                        unreachable!("Expected a tuple")
                    };
                    for element in elements.into_vec().into_iter().rev(){
                        self.push(element)?;
                    }
                }
            }
        }
        Ok(())
    }


}

