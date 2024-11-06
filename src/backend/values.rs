use super::{instructions::Chunk, objects::{Heap, Object}};
#[derive(Clone,Debug,PartialEq,Default)]
pub struct Function{
    pub name : String,
    pub chunk : Chunk
}

#[derive(Clone,Debug,PartialEq,Default)]
pub struct Closure{
    pub environment : Box<[Value]>,
    pub function : Function
}
#[derive(Debug,Clone)]
pub struct Record{
    pub fields : Box<[Value]>
}



#[derive(Clone,Copy,Debug,PartialEq)]
pub enum Value{
    Int(i64),
    Float(f64),
    Bool(bool),
    Unit,
    Record(Object),
    Tuple(Object),
    String(Object),
    List(Object),
    Function(Object)
}
impl Value{
    pub fn is_equal(&self,other:&Value,heap:&Heap)->bool{
        match (self,other){
            (Self::Int(int),Self::Int(other)) => int == other,
            (Self::Float(float),Self::Float(other)) => float == other,
            (Self::Bool(bool),Self::Bool(other)) => bool == other,
            (Self::Record(record),Self::Record(other)) => record.as_record(heap).fields.iter().zip(other.as_record(heap).fields.iter()).all(|(field,other)|{
                field.is_equal(other, heap)
            }),
            (Self::Unit,Self::Unit) => true,
            (Self::Tuple(tuple1),Self::Tuple(tuple2)) => {
                let tuple1 = tuple1.as_tuple(heap);
                let tuple2 = tuple2.as_tuple(heap);
                tuple1.len() == tuple2.len() && tuple1.iter().zip(tuple2.iter()).all(|(value1,value2)| value1.is_equal(value2, heap))
            },
            (Self::List(list),Self::List(other)) => {
                let list = list.as_list(heap);
                let other = other.as_list(heap);
                list.len() == other.len() && list.iter().zip(other.iter()).all(|(value1,value2)| value1.is_equal(value2, heap))
            },
            (Self::Function(object),Self::Function(other)) => object == other,
            (Self::String(object),Self::String(other)) => object.as_string(heap) == other.as_string(heap),
            _ => false
        }
    }
    pub fn format(&self,heap:&Heap)->String{
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
            Value::Record(record) => {
                let mut result = String::from("{");
                let record = record.as_record(heap);
                for (i,field) in record.fields.iter().enumerate(){
                    if i > 0{
                        result.push(',');
                    }
                    result.push_str(&field.format(heap));
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
                    result.push_str(&value.format(heap));
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
                for (i,value) in list.iter().enumerate(){
                    if i>0{
                        result.push(',');
                    }
                    result.push_str(&value.format(heap));
                }
                result.push(']');
                result
            },
            Value::Function(object) => {
                format!("fn<{}>",object.as_function(heap).name)
            }
        }
    }
    pub fn print(&self,heap:&Heap){
        print!("{}",self.format(heap))
    }
    pub fn println(&self,heap:&Heap){
        println!("{}",self.format(heap))
    }
}
