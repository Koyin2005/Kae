use std::rc::Rc;

use super::values::{Closure, Function, NativeFunction, Record, Upvalue, Value};

#[derive(Clone,Copy,Debug,Hash,PartialEq,Eq)]
pub struct Object(usize);


impl Object{
    pub fn as_function_ref(self,heap:&Heap)->&Function{
        let ObjectType::Function(function) = heap.get_object(self) else {
            panic!("Can't use object as function.")
        };
        function
    }
    pub fn as_closure(self,heap:& Heap)->&Closure{
        let ObjectType::Closure(closure) = heap.get_object(self) else {
            panic!("Can't use object as closure.")
        };
        closure
    }
    pub fn as_native_function(self,heap:&Heap)->&NativeFunction{
        let ObjectType::NativeFunction(function) = heap.get_object(self) else {
            panic!("Can't use object as native function.")
        };
        function
    }
    pub fn try_as_function(self,heap:&Heap)->Option<Rc<Function>>{
        let ObjectType::Function(function) = heap.get_object(self) else {
            return None;
        };
        Some(function.clone())
    }
    pub fn as_function(self,heap:&Heap)->Rc<Function>{
        let ObjectType::Function(function) = heap.get_object(self) else {
            panic!("Can't use object as function.")
        };
        function.clone()
    }
    pub fn get_record_fields_mut(self,heap:&mut Heap)->&mut [Value]{
        let (ObjectType::Record(record) | ObjectType::CaseRecord(_, record)) = heap.get_object_mut(self) else{
            panic!("Can't use object as record")
        };
        &mut record.fields
    }
    pub fn as_record(self,heap:&Heap)->&Record{
        let (ObjectType::Record(record)|ObjectType::CaseRecord(_, record)) = heap.get_object(self) else{
            panic!("Can't use object as record")
        };
        record
    }
    pub fn get_record_field_count(self,heap:&Heap)->usize{
        let ObjectType::CaseRecord(field_count, _) = heap.get_object(self) else{
            panic!("Can't use object as case record")
        };
        *field_count
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
    pub fn as_upvalue(self,heap:& Heap)->Upvalue{
        let ObjectType::Upvalue(upvalue) = heap.get_object(self) else {
            panic!("Can't use object as upvalue")
        };
        upvalue.clone()
    }
    pub fn as_upvalue_mut(self,heap:&mut Heap)->&mut Upvalue{
        let ObjectType::Upvalue(upvalue) = heap.get_object_mut(self) else {
            panic!("Can't use object as upvalue")
        };
        upvalue
    }
    pub fn new_native_function(heap:&mut Heap,function:Rc< NativeFunction>)->Self{
        heap.alloc(ObjectType::NativeFunction(function))
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
    pub fn new_case_record(heap:&mut Heap,record:Record,variant_field_count:usize)->Self{
        heap.alloc(ObjectType::CaseRecord(variant_field_count,record))
    }
    pub fn new_tuple(heap:&mut Heap,values:&[Value]) -> Self{
        heap.alloc(ObjectType::Tuple(values.to_vec().into_boxed_slice()))
    }
    pub fn new_list(heap:&mut Heap,values:Vec<Value>) -> Self{
        heap.alloc(ObjectType::List(values))
    }
    pub fn new_closure(heap:&mut Heap,closure:Closure)->Self{
        heap.alloc(ObjectType::Closure(closure))
    }
    pub fn new_upvalue(heap:&mut Heap,upvalue:Upvalue)->Self{
        heap.alloc(ObjectType::Upvalue(upvalue))
    }
}
pub enum ObjectType{
    Record(Record),
    CaseRecord(usize,Record),
    String(Rc<str>),
    Tuple(Box<[Value]>),
    List(Vec<Value>),
    Function(Rc<Function>),
    NativeFunction(Rc<NativeFunction>),
    Closure(Closure),
    Upvalue(Upvalue)
}


struct GcObject{
    _is_marked : bool,
    data : ObjectType
}
#[derive(Default)]
pub struct Heap{
    objects : Vec<Option<GcObject>>,
    data : Vec<Option<Value>>
}

impl Heap{
    pub fn new_string(&mut self,string:&str)->usize{
        
        let chars = string.chars().into_iter().collect::<Vec<_>>();
        let address = self.allocate(chars.len()+1);
        self.store(address, Value::Int(chars.len() as i64));
        for (i,value) in chars.into_iter().enumerate(){
            self.store(address+1+i, Value::Int(value as i64));
        }
        address
    }
    pub fn read_string(&self,address:usize)->String{
        
        let Value::Int(length) = self.load(address) else {
            panic!("Expected a valid length")
        };
        let length = length as usize;
        let mut string = String::new();
        for i in 0..length{
            let Value::Int(char) = self.load(address+1+i) else {
                panic!("Expected an int")
            };
            string.push(char::from_u32(char as u32).expect("Should only have valid chars"));
        }
        string
    }
    pub fn allocate(&mut self,size:usize)->usize{
        let address = self.data.len();
        self.data.extend(std::iter::repeat(Some(Value::Int(0))).take(size));
        address
    }
    pub fn store(&mut self,address:usize,value:Value){
        self.data[address] = Some(value);
    }
    pub fn load(&self,address:usize)->Value{
        self.data[address].clone().expect("Read from invalid address")
    }
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