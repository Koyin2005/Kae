use std::{io::stdin, rc::Rc};

use super::{objects::Object, values::Value, vm::{RuntimeError, VM}};

pub fn native_input(vm:&mut VM,_:&[Value])->Result<Value,RuntimeError>{
    let mut result = String::new();
    match stdin().read_line(&mut result){
        Ok(_) => {
            Ok(Value::String(Object::new_string(&mut vm.heap,Rc::from(result.trim()))))
        },
        Err(err) =>{
            vm.runtime_error(&format!("{}",err));
            Err(RuntimeError)
        }
    }
}


pub fn native_panic(vm:&mut VM,args:&[Value])->Result<Value,RuntimeError>{
    let Value::String(string) = args[0] else {
        panic!("Expected a string.")
    };
    vm.runtime_error(string.as_string(&vm.heap));
    Err(RuntimeError)
}


pub fn native_print_string(vm:&mut VM,args:&[Value])->Result<Value,RuntimeError>{
    let Value::HeapAddress(string_address) = args[0] else {
        panic!("Expected an address")
    };

    let Value::Int(length) = vm.heap.load(string_address) else {
        panic!("Expected a valid length")
    };
    let length = length as usize;
    let mut string = String::new();
    for i in 0..length{
        let Value::Int(char) = vm.heap.load(string_address+1+i) else {
            panic!("Expected an int")
        };
        string.push(char::from_u32(char as u32).expect("Should only have valid chars"));
    }
    print!("{}",string);
    Ok(Value::Unit)
    
}