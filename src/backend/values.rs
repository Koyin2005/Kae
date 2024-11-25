use std::rc::Rc;

use fxhash::FxHashMap;

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
#[derive(Debug,Clone)]
pub struct Record{
    pub name : Object,
    pub fields : Box<[Value]>
}

#[derive(Debug,Clone,Copy)]
pub enum Upvalue{
    Open{
        location:usize
    },
    Closed(Value)
}

#[derive(Clone, Copy,Debug,PartialEq)]
pub struct StackAddress(usize);



#[derive(Clone,Copy,Debug,PartialEq)]
pub enum Value{
    Int(i64),
    Float(f64),
    Bool(bool),
    Unit,
    Record(Object),
    CaseRecord(Object),
    Tuple(Object),
    String(Object),
    List(Object),
    Function(Object),
    Closure(Object),
    NativeFunction(Object)
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
            (Self::Record(record),Self::Record(other))|(Self::CaseRecord(record),Self::CaseRecord(other)) => 
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
    pub fn format(&self,heap:&Heap,seen_values : &mut Vec<Value>)->String{
        fn is_value_recursive(value:&Value,seen_values : &[Value],heap: &Heap)->bool{
            match value{
                Value::CaseRecord(record) | Value::Record(record) if seen_values.contains(value) => {
                    record.as_record(heap).fields.iter().any(|value| is_value_recursive(value, seen_values, heap))
                },
                _ => false
            }
        }
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
            Value::CaseRecord(record_object) => {
                let record = record_object.as_record(heap);
                let mut result = Value::String(record.name).format(heap, seen_values);
                let record_field_count = record_object.get_record_field_count(heap);
                if record_field_count>0{
                    result.push('{');
                    seen_values.push(*self);
                    for (i,field) in record.fields.iter().skip(1).enumerate().take(record_field_count){
                        if i > 0{
                            result.push(',');
                        }
                        if seen_values.contains(field) && is_value_recursive(field, seen_values, heap) {
                            result.push_str("...");
                        }
                        else{
                            result.push_str(&field.format(heap,seen_values));
                        }
                    }
                    result.push('}');
                }
                result
            }
            Value::Record(record) => {
                let record = record.as_record(heap);
                let mut result = format!("{}{{",Value::String(record.name).format(heap, seen_values));
                seen_values.push(*self);
                for (i,field) in record.fields.iter().enumerate(){
                    if i > 0{
                        result.push(',');
                    }
                    if seen_values.contains(field)&& is_value_recursive(field, seen_values, heap) {
                        result.push_str("...");
                    }
                    else{
                        result.push_str(&field.format(heap,seen_values));
                    }
                }
                result.push('}');
                result
            },
            Value::Tuple(tuple) => {
                let mut result = String::from("(");
                let tuple = tuple.as_tuple(heap);
                for (i,value) in tuple.iter().enumerate(){
                    if i>0{
                        result.push(',');
                    }
                    result.push_str(&value.format(heap,seen_values));
                }
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
                let list = list.as_list(heap);
                if seen_values.is_empty()||!seen_values.contains(self){
                    seen_values.push(*self);
                    for (i,value) in list.iter().enumerate(){
                        if i>0{
                            result.push(',');
                        }
                        result.push_str(&value.format(heap,seen_values));
                    }
                }
                else{
                    result.push_str("...");
                }
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

    pub fn deep_copy(&self,heap:&mut Heap,copies : &mut FxHashMap<Object,Value>)->Self{
        match self{
            Self::Int(_)|Self::Bool(_)|Self::Float(_)|Self::Function(_)|Self::NativeFunction(_)|Self::Unit|Self::String(_)|Self::Closure(_) => *self,
            Self::Tuple(tuple_object) => {
                if let Some(value) = copies.get(tuple_object){
                    *value
                }
                else {
                    let tuple = tuple_object.as_tuple(&heap);

                    let mut new_tuple = tuple.to_vec().into_boxed_slice();
                    let new_object = Object::new_tuple(heap, &new_tuple);
                    let value = Self::Tuple(new_object);
                    copies.insert(*tuple_object, value);

                    new_tuple.iter_mut().for_each(|value|{
                        *value = (*value).deep_copy(heap, copies);
                    });
                    value
                }
            },
            Self::List(list_object) => {
                if let Some(value) = copies.get(list_object){
                    *value
                }
                else{
                    let list = list_object.as_list(&heap);
                    let length = list.len();
                    let new_object = Object::new_list(heap, list.to_vec());
                    let value = Self::List(new_object);
                    copies.insert(*list_object, value);

                    for i in 0..length{
                        let value = new_object.as_list(&heap)[i];
                        new_object.as_list_mut(heap)[i] = value.deep_copy(heap, copies);
                    }
                    value
                }
            },
            Self::Record(record_object) => {
                if let Some(value) = copies.get(record_object){
                    *value
                }
                else{
                    let record = record_object.as_record(&heap).clone();
                    let field_count = record.fields.len();
                    let new_record_object = Object::new_record(heap,record);
                    let value = Self::Record(new_record_object);
                    copies.insert(*record_object, value);
                    for i in 0..field_count{
                        let new_value = new_record_object.as_record(&heap).fields[i];
                        new_record_object.get_record_fields_mut(heap)[i] = new_value.deep_copy(heap, copies);
                    }
                    value
                }
            },
            Self::CaseRecord(record_object) => {
                if let Some(value) = copies.get(record_object){
                    *value
                }
                else{
                    let record = record_object.as_record(&heap).clone();
                    let field_count = record_object.get_record_field_count(&heap);
                    let new_record_object = Object::new_case_record(heap,record,field_count);
                    let value = Self::CaseRecord(new_record_object); 
                    copies.insert(*record_object, value);
                    for i in 0..field_count{
                        let new_value = new_record_object.as_record(&heap).fields[i];
                        new_record_object.get_record_fields_mut(heap)[i] = new_value.deep_copy(heap, copies);
                    }
                    value
                }
            }
        }
    }
}
