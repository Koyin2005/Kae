use std::rc::Rc;

use crate::backend::objects::records::Record;

use super::values::{Function, Value};
pub mod records;

#[derive(Clone,Copy,Debug,Hash,PartialEq)]
pub struct Object(usize);


impl Object{
    pub fn as_function_ref(self,heap:&Heap)->&Function{
        let ObjectType::Function(function) = heap.get_object(self) else {
            panic!("Can't use object as function.")
        };
        function
    }
    pub fn as_function(self,heap:&Heap)->Rc<Function>{
        let ObjectType::Function(function) = heap.get_object(self) else {
            panic!("Can't use object as function.")
        };
        function.clone()
    }
    pub fn as_record_mut(self,heap:&mut Heap)->&mut Record{
        let ObjectType::Record(record) = heap.get_object_mut(self) else{
            panic!("Can't use object as record")
        };
        record
    }
    pub fn as_record(self,heap:&Heap)->&Record{
        let ObjectType::Record(record) = heap.get_object(self) else{
            panic!("Can't use object as record")
        };
        record
    }
    pub fn as_string(self,heap:&Heap)->&str{
        let ObjectType::String(string) = heap.get_object(self) else {
            panic!("Can't use object as string")
        };
        string
    }
    pub fn as_tuple(self,heap:&Heap)->&[Value]{
        let ObjectType::Tuple(tuple) = heap.get_object(self) else {
            panic!("Can't use object as tuple")
        };
        tuple
    }
    pub fn as_list_mut(self,heap:&mut Heap)->&mut Vec<Value>{
        let ObjectType::List(list) = heap.get_object_mut(self) else{
            panic!("Can't use object as list")
        };
        list
    }
    pub fn as_list(self,heap:& Heap)->&[Value]{
        let ObjectType::List(list) = heap.get_object(self) else{
            panic!("Can't use object as list")
        };
        list
    }
    pub fn new_function(heap:&mut Heap,function:Rc<Function>)->Self{
        heap.alloc(ObjectType::Function(function))
    }
    pub fn new_string(heap:&mut Heap,string:Rc<str>)->Self{
        heap.alloc(ObjectType::String(string))
    }
    pub fn new_record(heap:&mut Heap,record:Record)->Self{
        heap.alloc(ObjectType::Record(record))
    }
    pub fn new_tuple(heap:&mut Heap,values:&[Value]) -> Self{
        heap.alloc(ObjectType::Tuple(values.to_vec().into_boxed_slice()))
    }
    pub fn new_list(heap:&mut Heap,values:Vec<Value>) -> Self{
        heap.alloc(ObjectType::List(values))
    }
}
pub enum ObjectType{
    Record(Record),
    String(Rc<str>),
    Tuple(Box<[Value]>),
    List(Vec<Value>),
    Function(Rc<Function>)
}


struct GcObject{
    _is_marked : bool,
    data : ObjectType
}
#[derive(Default)]
pub struct Heap{
    objects : Vec<Option<GcObject>>
}
impl Heap{
    pub fn get_object_mut(&mut self,object:Object)->&mut ObjectType{
        &mut self.objects[object.0].as_mut().unwrap().data
    }
    pub fn get_object(&self,object:Object)->&ObjectType{
        &self.objects[object.0].as_ref().unwrap().data
    }


    pub fn alloc(&mut self,object:ObjectType)->Object{
        self.objects.push(Some(GcObject{_is_marked:false,data:object}));
        Object(self.objects.len()-1)
    }
}