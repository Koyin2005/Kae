use std::rc::Rc;

use fxhash::FxHashMap;

use crate::backend::disassembly::disassemble_instruction;

use super::{instructions::{Chunk, Constant, Instruction, Program}, objects::{Heap, Object}, values::{Closure, Function, Record, Upvalue, Value}};

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
            globals : FxHashMap::default()
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
            Constant::String(string) => Value::String(Object::new_string(&mut self.heap, string)),
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
                    print!("[{}] ",value.format(&self.heap,&mut Vec::new()));
                }
                println!();
                for value in self.stack.iter(){
                    print!("[{}] ",value.format(&self.heap,&mut Vec::new()));
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
                        panic!("Expected a string.")
                    };
                    let Value::String(a) = self.peek(0) else {
                        panic!("Expected a string.")
                    };
                    let b = b.as_string(&self.heap);
                    let a = a.as_string(&self.heap);
                    let mut string = String::with_capacity(a.len() + b.len());
                    string.push_str(a);
                    string.push_str(b);
                    let string =Value::String(Object::new_string(&mut self.heap, Rc::from(string)));
                    self.store_top(string);
                }
                Instruction::BuildArray(size) => {
                    let Value::Int(elements) = self.pop() else{
                        unreachable!()
                    };
                    let address = self.heap.allocate(size+1);
                    self.heap.store(address,Value::Int(elements as i64));
                    for i in (1..size+1).rev(){
                        let value = self.pop();
                        self.heap.store(address+i,value);
                    }
                    self.push(Value::HeapAddress(address))?;
                }
                Instruction::BuildTuple(elements) => {
                    let mut elements = std::iter::repeat_with(|| self.pop()).take(elements as usize).collect::<Box<[_]>>();
                    elements.reverse();
                    let tuple = Object::new_tuple(&mut self.heap, &elements);
                    self.push(Value::Tuple(tuple))?;
                },
                Instruction::BuildCaseRecord(fields) => {
                    let Value::Int(field_count) = self.pop() else {
                        panic!("Expected an int for variant field count")
                    };
                    let variant_tag = self.pop();
                    let Value::String(name) = self.pop() else {
                        panic!("Expectd a string")
                    };
                    let field_count = field_count as usize;
                    let mut fields = (0..fields).map(|_| Value::Int(0)).collect::<Box<[Value]>>();
                    fields[0] = variant_tag;
                    let record_object = Object::new_case_record(&mut self.heap, Record{
                        fields,
                        name
                    },field_count);
                    self.push(Value::CaseRecord(record_object))?;
                },
                Instruction::BuildRecord(fields) => {
                    let Value::String(name) = self.pop() else {
                        panic!("Expectd a string")
                    };
                    let record = Record{
                        fields:(0..fields).map(|_| Value::Int(0)).collect(),
                        name
                    };
                    let record = Value::Record(Object::new_record(&mut self.heap, record));
                    self.push(record)?;
                },
                Instruction::LoadFieldRef(field) => {
                    match self.pop(){
                        Value::StackAddress(address) => {
                            self.push(Value::StackAddress(address + field as usize))?;
                        },
                        Value::GlobalAddress(address) => {
                            self.push(Value::GlobalAddress(address + field as usize))?;
                        },
                        Value::HeapAddress(address) => {
                            self.push(self.heap.load(address + field as usize))?;
                        }
                        _ => {
                            panic!("Can't get field of non-record.")
                        }
                    }
                }
                Instruction::LoadField(field) => {
                    match self.pop(){
                        Value::StackAddress(address) => {
                            self.push(self.stack[address + field as usize].clone())?;
                        },
                        Value::GlobalAddress(address) => {
                            self.push(self.globals[&(address + field as usize)].clone())?;
                        },
                        Value::HeapAddress(address) => {
                            self.push(self.heap.load(address + field as usize))?;
                        }
                        _ => {
                            panic!("Can't get field of non-record.")
                        }
                    }

                },
                Instruction::LoadStructField(field,size) => {
                    match self.pop(){
                        Value::StackAddress(address) => {
                            for address in address..address + size{
                                self.push(self.stack[address + field as usize].clone())?;
                            }
                        },
                        Value::GlobalAddress(address) => {
                            for address in address..address + size{
                                self.push(self.globals[&(address + field as usize)].clone())?;
                            }
                        },
                        Value::HeapAddress(address) => {
                            for address in address..address + size{
                                self.push(self.heap.load(address + field as usize))?;
                            }

                        },
                        _ => {
                            panic!("Can't get field of non-record.")
                        }
                    }
                }
                Instruction::StoreField(field) => {
                    let value = self.pop();
                    match self.peek(0){
                        Value::Record(record) => {
                            record.get_record_fields_mut(&mut self.heap)[field as usize] = value;
                        },
                        Value::GlobalAddress(address) => {
                            self.globals.insert(address + field as usize,value);
                        },
                        Value::StackAddress(address) => {
                            self.stack[address + field as usize] = value;
                        },
                        Value::HeapAddress(address) => {
                            self.heap.store(address + field as usize, value);
                        }
                        _ =>  panic!("Can't get field of non-record.")
                    }
                },
                Instruction::StoreStructField(field,size) => {
                    match self.peek(size){
                        Value::Record(record) => {
                            for field in (field as usize..field as usize+size).rev(){
                                let value = self.pop();
                                record.get_record_fields_mut(&mut self.heap)[field] = value;
                            }
                        },
                        Value::GlobalAddress(address) => {
                            for address in (address..address+size).rev(){
                                let value = self.pop();
                                self.globals.insert(address + field as usize,value);
                            }
                        },
                        Value::StackAddress(address) => {
                            for address in (address..address+size).rev(){
                                let value = self.pop();
                                self.stack[address + field as usize] = value;
                            }
                        },
                        Value::HeapAddress(address) => {
                            for address in (address..address+size).rev(){
                                let value = self.pop();
                                self.heap.store(address + field as usize,value);
                            }
                        } 
                        _ =>  panic!("Can't get field of non-record.")
                    }

                }
                Instruction::GetArrayLength => {
                    let Value::HeapAddress(list) = self.pop() else {
                        panic!("Can't get length of non-list")
                    };
                    self.push(self.heap.load(list))?;
                },
                Instruction::StoreLocal(local) => {
                    let value = self.pop();
                    let location = local as usize + self.current_frame().bp;
                    self.stack[location] = value;
                },
                Instruction::StoreLocalStruct(local,size) => {
                    let location = local as usize + self.current_frame().bp;
                    for offset in (0..size).rev(){
                        self.stack[location + offset] = self.pop();
                    }
                },
                Instruction::LoadLocal(local) => {
                    let location = local as usize + self.current_frame().bp;
                    self.push(self.stack[location].clone())?;
                },
                Instruction::LoadLocalStruct(local,size) => {
                    let location = local as usize + self.current_frame().bp;
                    for offset in 0..size{
                        self.push(self.stack[location + offset].clone())?;
                    }
                },
                Instruction::LoadLocalRef(local) => {
                    self.push(Value::StackAddress(self.current_frame().bp + local as usize))?;
                },
                Instruction::LoadGlobal(global) => {
                    self.push(self.globals[&(global as usize)].clone())?;
                },
                Instruction::LoadGlobalStruct(global,size) => {
                    for global in global as usize..global as usize + size{
                        self.push(self.globals[&(global as usize)].clone())?;
                    }
                },
                Instruction::LoadGlobalRef(global) => {
                    self.push(Value::GlobalAddress(global as usize))?;
                }
                Instruction::StoreGlobal(global) => {
                    let value = self.pop();
                    self.globals.insert(global as usize, value);
                },
                Instruction::StoreGlobalStruct(global,size) => {
                    for i in (0..size).rev(){
                        let value = self.pop();
                        self.globals.insert(global as usize + i, value);
                    }
                }
                Instruction::LoadUpvalue(upvalue) => {
                    let upvalue = self.current_frame().closure.expect("Can only use upvalues with closure").as_closure(&self.heap).upvalues[upvalue as usize].as_upvalue(&self.heap);
                   
                    self.push(match upvalue {
                        Upvalue::Closed(value) => value,
                        Upvalue::Open { location } => self.stack[location].clone()
                    })?;
                },
                Instruction::LoadUpvalueStruct(upvalue,size) => {
                    for upvalue in upvalue as usize..upvalue as usize + size{
                        let upvalue = self.current_frame().closure.expect("Can only use upvalues with closure").as_closure(&self.heap).upvalues[upvalue as usize].as_upvalue(&self.heap);
                    
                        self.push(match upvalue {
                            Upvalue::Closed(value) => value,
                            Upvalue::Open { location } => self.stack[location].clone()
                        })?;
                    }
                },
                Instruction::StoreUpvalue(upvalue) => {
                    let value = self.pop();
                    let upvalue = self.current_frame().closure.expect("Can only use upvalues with closure").as_closure(&self.heap).upvalues[upvalue as usize].as_upvalue_mut(&mut self.heap);
                    match upvalue{
                        Upvalue::Closed(closed) => *closed = value,
                        Upvalue::Open { location } => self.stack[*location] = value
                    }
                },
                Instruction::StoreUpvalueStruct(upvalue,size) => {
                    for upvalue in (upvalue as usize..upvalue as usize + size).rev(){
                        let value = self.pop();
                        let upvalue = self.current_frame().closure.expect("Can only use upvalues with closure").as_closure(&self.heap).upvalues[upvalue as usize].as_upvalue_mut(&mut self.heap);
                        match upvalue{
                            Upvalue::Closed(closed) => *closed = value,
                            Upvalue::Open { location } => self.stack[*location] = value
                        }
                    }
                    
                }
                Instruction::LoadIndex(size) => {
                    let Value::Int(index) = self.pop() else {
                        panic!("Expected an int.")
                    };
                    let Value::HeapAddress(list) = self.pop() else{
                        panic!("Expected a list.")
                    };
                    let Value::Int(len) = self.heap.load(list) else{
                        unreachable!()
                    };
                    if 0 <= index && (index as usize)< len as usize{
                        let offset = index as isize * size as isize;
                        for i in 0..size as usize{
                            let value = self.heap.load(list+1+i + offset as usize);
                            self.push(value)?;
                        }
                    }
                    else{
                        self.runtime_error(&format!("Index out of bounds, index was '{}' but length was '{}'.",index,len as usize));
                        return Err(RuntimeError);
                    }
                },
                Instruction::GetTupleElement(index) => {
                    let Value::Tuple(tuple) = self.pop() else{
                        panic!("Expected a tuple.")
                    };
                    let tuple = tuple.as_tuple(&self.heap);
                    self.push(tuple[index as usize].clone())?;
                }
                Instruction::StoreIndex(size) => {
                    let Value::Int(index) = self.peek(size) else {
                        panic!("Expected an int.")
                    };
                    let Value::HeapAddress(list) = self.peek(size+1) else{
                        panic!("Expected a list.")
                    };
                    let Value::Int(len) = self.heap.load(list) else {
                        unreachable!()
                    };
                    if 0 <= index && index< len{
                        for i in (0..size).rev(){
                            let value = self.pop();
                            self.heap.store(list + 1+i, value);
                        }
                    }
                    else{
                        self.runtime_error(&format!("Index out of bounds : index was '{}', but len was '{}'.",index,len));
                        return Err(RuntimeError);
                    }
                },
                Instruction::LoadIndexRef(size) => {
                    let Value::Int(index) = self.pop() else {
                        panic!("Expected an int.")
                    };
                    let Value::HeapAddress(list) = self.pop() else{
                        panic!("Expected a list.")
                    };
                    let Value::Int(len) = self.heap.load(list) else {
                        unreachable!()
                    };
                    if 0 <= index && index< len{
                        self.push(Value::HeapAddress(list + 1 + index as usize * size))?;
                    }
                    else{
                        self.runtime_error(&format!("Index out of bounds : index was '{}', but len was '{}'.",index,len));
                        return Err(RuntimeError);
                    }
                }
                Instruction::UnpackTuple => {
                    let Value::Tuple(tuple) = self.pop() else{
                        panic!("Expected a tuple.")
                    };
                    let tuple = tuple.as_tuple(&self.heap);
                    for element in tuple.iter().rev().cloned().collect::<Vec<Value>>(){
                        self.push(element)?;
                    }
                },
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
                    for offset in (0..args).rev(){
                        if args - offset  -1 > 0{
                            print!(" ");
                        }
                        self.peek(offset as usize).print(&self.heap);
                    }
                    self.stack.truncate(self.stack.len() - args as usize);
                    println!();
                },
                Instruction::PrintValue(after) => {
                    let value = self.pop();
                    if let Some(buffer) = debug_buffer.as_mut(){
                        buffer.push_str(&value.format(&self.heap, &mut Vec::new()));
                        if let Some(after) = after{
                            let after = after as char;
                            if after == '\n'{
                                println!("{}",buffer);
                                buffer.clear();
                            }
                            else{
                                buffer.push(after);
                            }
                        }
                    }
                    else{
                        value.print(&self.heap);
                        if let Some(after) = after{
                            print!("{}",after as char);
                        }
                    }
                },
                Instruction::PrintAscii(byte)=>{
                    if let Some(buffer) = debug_buffer.as_mut(){
                        let byte_char = byte as char;
                        if byte_char == '\n'{
                            println!("{}",buffer);
                            buffer.clear();
                        }
                        else{
                            buffer.push(byte_char);
                        }
                    }
                    else{
                        print!("{}",byte as char);
                    }
                }
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
                            panic!("Expect function got {}.",value.format(&self.heap, &mut Vec::new()))
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
                Instruction::ReturnStruct(size) => {
                    let values = self.pop_values(size);
                    if let Some(frame) = self.frames.pop(){
                        self.close_upvalues(frame.bp);
                        self.stack.truncate(frame.bp);
                        for value in values{
                            self.push(value)?;
                        }
                    }
                    if self.frames.is_empty(){
                        break;
                    }

                }
                Instruction::StackAlloc(size) => {
                    let size = size.unwrap_or_else(|| self.pop_size());
                    let address = self.stack.len();
                    for _ in 0..size{
                        self.stack.push(Value::Int(0));
                    }
                    self.stack.push(Value::StackAddress(address))
                },
                Instruction::PopStruct(size) => {
                    for _ in 0..size{
                        self.pop();
                    }

                },
                Instruction::LoadStackTopOffset(size) => {
                    self.push(Value::StackAddress(self.stack.len() - size))?;
                },
            }
        }
        Ok(())
    }


}

#[cfg(test)]
mod vm_tests{

    use crate::backend::instructions::{Chunk, Instruction, Program};

    use super::VM;

    #[test]
    pub fn test_record(){
        let mut vm = VM::new(Program{ chunk:Chunk{
            code : vec![
                Instruction::BuildRecord(2),
                Instruction::LoadInt(5),
                Instruction::StoreField(0),
                Instruction::LoadInt(10),
                Instruction::StoreField(1),
            ],
            lines : vec![1;5],
            ..Default::default()
        },names:vec![],constants:vec![]});
        let _ = vm.run();
        for value in vm.stack.iter(){
            value.println(&vm.heap);
        }
    }
}