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
    vm.runtime_error(&format!("{}",string.as_string(&vm.heap)));
    Err(RuntimeError)
}


pub fn native_push(vm:&mut VM,args:&[Value])->Result<Value,RuntimeError>{
    let Value::List(list) = args[0] else {
        panic!("Expected a list.")
    };
    list.as_list_mut(&mut vm.heap).push(args[1]);
    Ok(Value::Unit)
}

pub fn native_pop(vm:&mut VM,args:&[Value])->Result<Value,RuntimeError>{
    let Value::List(list) = args[0] else {
        panic!("Expected a list.")
    };
    if let Some(value) = list.as_list_mut(&mut vm.heap).pop(){
        Ok(value)
    }
    else{
        vm.runtime_error("Can't pop from an empty list.");
        Err(RuntimeError)
    }
}

pub fn native_parse_int(vm:&mut VM,args:&[Value])->Result<Value,RuntimeError>{
    let Value::String(string) = args[0] else {
        panic!("Expected a string.")
    };
    let number = string.as_string(&vm.heap).parse().ok();
    let (variant_name,variant_tag,fields) = if let Some(int) = number{
        ("Some",0,vec![Value::Int(int)])
    }
    else{
        ("None",1,vec![])
    };
    Ok(Value::make_case_record(&mut vm.heap, variant_name, variant_tag,&fields , 2))
    
}