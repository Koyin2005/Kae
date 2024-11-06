use std::rc::Rc;

use fxhash::FxHashMap;

use crate::backend::disassembly::disassemble_instruction;

use super::{instructions::{Chunk, Constant, Instruction}, objects::{Heap, Object}, values::{Function, Value,Record}};

pub const DEBUG_TRACE_EXEC : bool = false;
pub const MAX_STACK_SIZE : usize = 255;
pub const MAX_FRAMES : usize = 64;

pub struct RuntimeError;
#[derive(Default)]
pub struct CallFrame{
    function : Rc<Function>,
    ip : usize,
    bp : usize
}
pub struct VM{
    stack : Vec<Value>,
    frames : Vec<CallFrame>,
    heap : Heap,
    globals : FxHashMap<usize,Value>,
}
impl VM{

    pub fn new(chunk : Chunk)->Self{
        Self{
            stack:Vec::from_iter(std::iter::repeat(Value::Int(0)).take(chunk.locals)),
            heap:Heap::default(),
            frames : vec![CallFrame{
                function : Rc::new(Function{
                    name : "<main>".to_string(),
                    chunk
                }),
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
    fn pop(&mut self)->Value{
        self.stack.pop().unwrap()
    }
    fn peek(&self,offset:usize)->Value{
        self.stack[self.stack.len() - offset - 1]
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
    pub fn reset(&mut self,chunk:Chunk){
        self.frames = vec![CallFrame{
            function : Rc::new(Function { name: "<main>".to_string(), chunk }),
            ip : 0,
            bp : 0,
        }];
        self.stack = vec![Value::Int(0); self.current_chunk().locals];
    }
    fn load_constant(&mut self,index: usize)-> Value{
        match self.current_chunk().constants[index].clone(){
            Constant::Int(int) => Value::Int(int),
            Constant::String(string) => Value::String(Object::new_string(&mut self.heap, string)),
            Constant::Float(float) => Value::Float(float),
            Constant::Function(function) => Value::Function(Object::new_function(&mut self.heap, function))
        }
    }
    fn store_top(&mut self,value:Value){
        let index =self.stack.len() - 1;
        self.stack[index] = value;
    }
    fn runtime_error(&self,message:&str){
        eprintln!("Error : {}",message);
        for frame in self.frames.iter().rev(){
            eprintln!("[line {}] in {}",frame.function.chunk.lines[frame.ip],frame.function.name);
        }
    }
    pub fn run(&mut self)->Result<(),RuntimeError>{
        while self.current_frame().ip < self.current_chunk().code.len(){
            if DEBUG_TRACE_EXEC{
                for value in self.stack.iter(){
                    print!("[{}] ",value.format(&self.heap));
                }
                println!();
                let instruction = self.current_chunk().code[self.current_frame().ip];
                disassemble_instruction(self.current_chunk(), self.current_frame().ip, instruction);
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
                Instruction::BuildList(elements) => {
                    let mut elements = std::iter::repeat_with(|| self.pop()).take(elements as usize).collect::<Vec<_>>();
                    elements.reverse();
                    let tuple = Object::new_list(&mut self.heap, elements);
                    self.push(Value::List(tuple))?;
                }
                Instruction::BuildTuple(elements) => {
                    let mut elements = std::iter::repeat_with(|| self.pop()).take(elements as usize).collect::<Box<[_]>>();
                    elements.reverse();
                    let tuple = Object::new_tuple(&mut self.heap, &elements);
                    self.push(Value::Tuple(tuple))?;
                },
                Instruction::InitRecord(fields) => {
                    let record_object = Object::new_record(&mut self.heap, Record{
                        fields:(0..fields).map(|_| Value::Int(0)).collect()
                    });
                    self.push(Value::Record(record_object))?;
                },
                Instruction::LoadField(field) => {
                    let Value::Record(record) = self.pop() else {
                        panic!("Can't get field of non-record")
                    };
                    let field_value = record.as_record_mut(&mut self.heap).fields[field as usize];
                    self.push(field_value)?;

                },
                Instruction::GetArrayLength => {
                    let Value::List(list) = self.pop() else {
                        panic!("Can't get length of non-list")
                    };
                    let length = list.as_list(&self.heap).len();
                    self.push(Value::Int(length as i64))?;
                },
                Instruction::StoreField(field) => {
                    let value = self.pop();
                    let Value::Record(record) = self.stack[self.stack.len()-1] else {
                        panic!("Can't get field of non-record")
                    };
                    record.as_record_mut(&mut self.heap).fields[field as usize] = value;
                },
                Instruction::StoreLocal(local) => {
                    let value = self.pop();
                    let location = local as usize + self.current_frame().bp;
                    self.stack[location] = value;
                },
                Instruction::LoadLocal(local) => {
                    let location = local as usize + self.current_frame().bp;
                    self.push(self.stack[location])?;
                },
                Instruction::LoadGlobal(global) => {
                    self.push(self.globals[&(global as usize)])?;
                },
                Instruction::StoreGlobal(global) => {
                    let value = self.pop();
                    self.globals.insert(global as usize, value);
                },
                Instruction::LoadIndex => {
                    let Value::Int(index) = self.pop() else {
                        panic!("Expected an int.")
                    };
                    let Value::List(list) = self.pop() else{
                        panic!("Expected a list.")
                    };
                    let list = list.as_list(&self.heap);
                    if 0 <= index && (index as usize)< list.len(){
                        self.push(list[index as usize])?;
                    }
                    else{
                        self.runtime_error("Index out of bounds");
                        return Err(RuntimeError);
                    }
                },
                Instruction::StoreIndex => {
                    let value = self.pop();
                    let Value::Int(index) = self.peek(0) else {
                        panic!("Expected an int.")
                    };
                    let Value::List(list) = self.peek(1) else{
                        panic!("Expected a list.")
                    };
                    let list = list.as_list_mut(&mut self.heap);
                    if 0 <= index && (index as usize)< list.len(){
                        list[index as usize] = value;
                    }
                    else{
                        self.runtime_error("Index out of bounds.");
                        return Err(RuntimeError);
                    }
                }
                Instruction::UnpackTuple => {
                    let Value::Tuple(tuple) = self.pop() else{
                        panic!("Expected a tuple.")
                    };
                    let tuple = tuple.as_tuple(&self.heap);
                    for element in tuple.iter().rev().copied().collect::<Vec<Value>>(){
                        self.push(element)?;
                    }
                },
                Instruction::Loop(offset) => {
                    self.current_frame_mut().ip -= offset as usize;
                },
                Instruction::Jump(offset) => {
                    self.current_frame_mut().ip += offset as usize;
                },
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
                Instruction::Pop => {
                    self.pop();
                },
                Instruction::Copy(offset) => {
                    let offset = (offset - 1) as usize;
                    self.push(self.peek(offset))?;
                }
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
                Instruction::Call(args) => {
                    let arg_count = args as usize;
                    let function = self.peek(arg_count);
                    let Value::Function(function) = function else {
                        panic!("Expect function.")
                    };
                    let function = function.as_function(&self.heap);

                    let bp = self.stack.len() - arg_count - 1;
                    let stack_size = self.stack.len();
                    self.stack.copy_within(bp+1..stack_size, bp);
                    self.pop();

                    self.stack.extend(std::iter::repeat(Value::Int(0)).take(function.chunk.locals - arg_count));
                    self.frames.push(CallFrame{
                        function,
                        ip : 0,
                        bp
                    });
                    if self.frames.len() > MAX_FRAMES{
                        self.runtime_error("Exceeeded max call frames.");
                        return Err(RuntimeError);
                    }
                },
                Instruction::Return => {
                    let value = self.pop();
                    if let Some(frame) = self.frames.pop(){
                        self.stack.truncate(frame.bp);
                        self.push(value)?;
                    }
                    if self.frames.is_empty(){
                        break;
                    }
                },
            }
        }
        Ok(())
    }


}

#[cfg(test)]
mod vm_tests{

    use crate::backend::instructions::{Chunk, Instruction};

    use super::VM;

    #[test]
    pub fn test_record(){
        let mut vm = VM::new(Chunk{
            code : vec![
                Instruction::InitRecord(2),
                Instruction::LoadInt(5),
                Instruction::StoreField(0),
                Instruction::LoadInt(10),
                Instruction::StoreField(1),
            ],
            lines : vec![1;5],
            ..Default::default()
        });
        let _ = vm.run();
        for value in vm.stack.iter(){
            value.println(&vm.heap);
        }
    }
}