use std::{fmt::Display, rc::Rc};

use super::{instructions::Chunk, objects::{Heap, Object}, vm::{RuntimeError, VM}};
#[derive(Clone,Debug,PartialEq,Default)]
pub struct Function{
    pub name : String,
    pub chunk : Chunk,
    pub upvalues : Vec<(usize,bool)>
}

pub type NativeFn = fn(&mut VM,args:&[Value])->Result<Value,RuntimeError>;
#[derive(Clone,Debug,PartialEq)]
pub struct NativeFunction{
    pub name : String,
    pub function : NativeFn
}

#[derive(Clone,Debug,PartialEq,Default)]
pub struct Closure{
    pub upvalues : Box<[Object]>,
    pub function : Rc<Function>
}
#[derive(Debug,Clone,PartialEq)]
pub struct Record{
    pub name : Object,
    pub fields : Box<[Value]>
}

#[derive(Debug,Clone)]
pub enum Upvalue{
    Open{
        location:usize
    },
    Closed(Value)
}
#[derive(Clone,Debug,PartialEq)]
pub enum Value{
    Int(i64),
    Float(f64),
    Bool(bool),
    Tuple(Box<[Value]>),
    StackAddress(usize),
    GlobalAddress(usize),
    HeapAddress(usize),
    Unit,
    Function(Object),
    Closure(Object),
    NativeFunction(Object)
}
impl Value{
    pub fn is_equal(&self,other:&Value,heap:&Heap)->bool{
        match (self,other){
            (Self::Int(int),Self::Int(other)) => int == other,
            (Self::Float(float),Self::Float(other)) => float == other,
            (Self::Bool(bool),Self::Bool(other)) => bool == other,
            (Self::Unit,Self::Unit) => true,
            (Self::Function(object),Self::Function(other)) => object == other,
            (Self::NativeFunction(object),Self::NativeFunction(other)) => object == other,
            (Self::Closure(object),Self::Closure(other)) => object == other,
            (Self::StackAddress(address),Self::StackAddress(other)) => address == other,
            (Self::GlobalAddress(address),Self::GlobalAddress(other)) => address == other,
            (Self::Tuple(elements),Self::Tuple(other)) => elements.iter().zip(other.iter()).all(|(element,other)| element == other),
            _ => false
        }
    }
    pub fn format(& self,heap:&Heap,seen_values : &mut Vec<&Value>)->String{
        match self{
            Value::Bool(bool) => {
                format!("{}",*bool)
            },
            Value::Int(int) => {
                format!("{}",*int)
            },
            Value::Float(float) => {
                format!("{}",*float)
            },
            Value::Closure(closure) => {
                format!("fn<{}>",closure.as_closure(heap).function.name)
            },
            Value::Unit => {
                "()".to_string()
            },
            Value::Tuple(elements) => {
                let mut result = String::from("(");
                for (i,element) in elements.iter().enumerate(){
                    if i>0{
                        result.push(',');
                    }
                    result.push_str(&element.format(heap, seen_values));
                }
                result.push(')');
                result
            },
            Value::Function(object) => {
                format!("fn<{}>",object.as_function(heap).name)
            },
            Value::NativeFunction(object) => {
                format!("native<{}>",object.as_native_function(heap).name)
            },
            Value::StackAddress(address) | Value::HeapAddress(address) | Value::GlobalAddress(address) => {
                format!("*{}",address)
            },
        }
    }
    pub fn print(&self,heap:&Heap){
        print!("{}",self.format(heap,&mut Vec::new()))
    }
    pub fn println(&self,heap:&Heap){
        println!("{}",self.format(heap,&mut Vec::new()))
    }

}
