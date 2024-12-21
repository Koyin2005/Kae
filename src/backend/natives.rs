use std::{io::stdin, rc::Rc};

use super::{objects::Object, values::Value, vm::{RuntimeError, VM}};

pub fn native_input(vm:&mut VM,_:&[Value])->Result<Value,RuntimeError>{
    let mut result = String::new();
    match stdin().read_line(&mut result){
        Ok(_) => {
            Ok(Value::HeapAddress(vm.heap.new_string(&result.trim())))
        },
        Err(err) =>{
            vm.runtime_error(&format!("{}",err));
            Err(RuntimeError)
        }
    }
}


pub fn native_panic(vm:&mut VM,args:&[Value])->Result<Value,RuntimeError>{
    let Value::HeapAddress(string) = args[0] else {
        panic!("Expected a string.")
    };

    vm.runtime_error(&vm.heap.read_string(string));
    Err(RuntimeError)
}


pub fn native_print_string(vm:&mut VM,args:&[Value])->Result<Value,RuntimeError>{
    let Value::HeapAddress(string_address) = args[0] else {
        panic!("Expected a string")
    };
    let string = vm.heap.read_string(string_address);
    print!("{}",string);
    Ok(Value::Unit)
    
}