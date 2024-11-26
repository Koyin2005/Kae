use std::rc::Rc;

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
#[derive(Clone, Copy,Debug,PartialEq)]
pub enum Address{
    Global(usize),
    Stack(usize),
}

#[derive(Clone,Debug,PartialEq)]
pub enum Value{
    Int(i64),
    Float(f64),
    Bool(bool),
    Unit,
    Record(Record),
    CaseRecord(Object),
    Tuple(Object),
    String(Object),
    List(Object),
    Function(Object),
    Closure(Object),
    NativeFunction(Object),
    Address(Address)
}
impl Value{
    pub fn make_case_record(heap:&mut Heap,variant_name:&str,variant_tag:usize,variant_fields : &[Self],total_field_count:usize)->Self{
        assert!(total_field_count>=1);
        let name = Object::new_string(heap, variant_name.into());
        let mut fields = vec![Value::Int(variant_tag as i64)];
        fields.extend_from_slice(variant_fields);
        let padding = total_field_count - fields.len();
        fields.extend(std::iter::repeat(Value::Int(0)).take(padding));
        Value::CaseRecord(Object::new_case_record(heap, Record { name, fields: fields.into_boxed_slice() },variant_fields.len()))
    }
    pub fn is_equal(&self,other:&Value,heap:&Heap)->bool{
        match (self,other){
            (Self::Int(int),Self::Int(other)) => int == other,
            (Self::Float(float),Self::Float(other)) => float == other,
            (Self::Bool(bool),Self::Bool(other)) => bool == other,
            (Self::Unit,Self::Unit) => true,
            (Self::Address(address),Self::Address(other)) => address == other,
            (Self::Record(record),Self::Record(other)) => {
                record == other
            },
            (Self::CaseRecord(record),Self::CaseRecord(other)) => 
                record == other ||
                record.as_record(heap).fields.iter().zip(other.as_record(heap).fields.iter()).all(|(field,other)|{
                    field.is_equal(other, heap)
                }),
            (Self::Tuple(tuple1),Self::Tuple(tuple2)) => {
                let tuple1 = tuple1.as_tuple(heap);
                let tuple2 = tuple2.as_tuple(heap);
                tuple1.len() == tuple2.len() && tuple1.iter().zip(tuple2.iter()).all(|(value1,value2)| value1.is_equal(value2, heap))
            },
            (Self::List(list),Self::List(other)) => {
                if list == other { return  true;}
                let list = list.as_list(heap);
                let other = other.as_list(heap);
                list.len() == other.len() && list.iter().zip(other.iter()).all(|(value1,value2)| value1.is_equal(value2, heap))
            },
            (Self::Function(object),Self::Function(other)) => object == other,
            (Self::String(object),Self::String(other)) => object.as_string(heap) == other.as_string(heap),
            (Self::NativeFunction(object),Self::NativeFunction(other)) => object == other,
            (Self::Closure(object),Self::Closure(other)) => object == other,
            _ => false
        }
    }
    pub fn format(& self,heap:&Heap,seen_values : &mut Vec<&Value>)->String{
        match self{
            Value::Address(address) => {
                format!("*{}",match address{
                    Address::Global(global) => global,
                    Address::Stack(local) => local
                })
            },
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
            Value::CaseRecord(record_object) => {
                let record = record_object.as_record(heap);
                let record_field_count = record_object.get_record_field_count(heap);
                
                String::from("{}")
            }
            Value::Record(record) => {
                let name = Value::String(record.name);
                let mut result = name.format(heap, seen_values);
                if !record.fields.is_empty(){
                    result.push('{');
                    for (i,field) in record.fields.iter().enumerate(){
                        if i>0{
                            result.push(',');
                        }
                        result.push_str(&field.format(heap, seen_values));
                    }
                    result.push('}');
                }
                result
            },
            Value::Tuple(tuple) => {
                let mut result = String::from("(");
                result.push(')');
                result
            },
            Value::String(string) => {
                string.as_string(heap).to_string()
            },
            Value::Unit => {
                "()".to_string()
            },
            Value::List(list) => {
                let mut result = String::from("[");
                result.push(']');
                result
            },
            Value::Function(object) => {
                format!("fn<{}>",object.as_function(heap).name)
            },
            Value::NativeFunction(object) => {
                format!("native<{}>",object.as_native_function(heap).name)
            }
        }
    }
    pub fn print(&self,heap:&Heap){
        print!("{}",self.format(heap,&mut Vec::new()))
    }
    pub fn println(&self,heap:&Heap){
        println!("{}",self.format(heap,&mut Vec::new()))
    }

}
