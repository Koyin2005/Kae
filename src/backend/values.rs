use super::{instructions::Chunk, objects::{Heap, Object}, vm::{RuntimeError, VM}};
#[derive(Clone,Debug,PartialEq,Default)]
pub struct Function{
    pub name : String,
    pub chunk : Chunk
}

pub type NativeFn = fn(&mut VM,args:&[Value])->Result<Value,RuntimeError>;
#[derive(Clone,Debug,PartialEq)]
pub struct NativeFunction{
    pub name : String,
    pub function : NativeFn
}

#[derive(Clone,Debug,PartialEq,Default)]
pub struct Closure{
    pub environment : Box<[Value]>,
    pub function : Function
}
#[derive(Debug,Clone)]
pub struct Record{
    pub name : Object,
    pub fields : Box<[Value]>
}






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
            (Self::Record(record),Self::Record(other)) => 
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
            Value::CaseRecord(record_object) => {
                let record = record_object.as_record(heap);
                let mut result = format!("{}",Value::String(record.name).format(heap, seen_values));
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
}
