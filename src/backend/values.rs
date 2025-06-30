use std::rc::Rc;

use fxhash::FxHashSet;

use super::{
    instructions::Chunk,
    objects::{Heap, Object},
    vm::{RuntimeError, VM},
};
#[derive(Clone, Debug, PartialEq, Default)]
pub struct Function {
    pub name: String,
    pub chunk: Chunk,
    pub upvalues: Vec<(usize, bool)>,
}

pub type NativeFn = fn(&mut VM, args: &[Value]) -> Result<Value, RuntimeError>;
#[derive(Clone, Debug, PartialEq)]
pub struct NativeFunction {
    pub name: String,
    pub function: NativeFn,
}

#[derive(Clone, Debug, PartialEq, Default)]
pub struct Closure {
    pub upvalues: Box<[Object]>,
    pub function: Rc<Function>,
}
#[derive(Debug, Clone, PartialEq)]
pub struct Record {
    pub name: String,
    pub fields: Box<[Value]>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct VariantRecord {
    pub discriminant: usize,
    pub record_data: Box<Record>,
}

#[derive(Debug, Clone)]
pub enum Upvalue {
    Open { location: usize },
    Closed(Value),
}
#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Int(i64),
    Float(f64),
    Bool(bool),
    Tuple(Box<[Value]>),
    Record(Box<Record>),
    VariantRecord(VariantRecord),
    StackAddress(usize),
    GlobalAddress(usize),
    FieldRef(Box<FieldRef>),
    IndexRef(Box<FieldRef>),
    Unit,
    Function(Object),
    Closure(Object),
    NativeFunction(Object),
    String(Object),
    Array(Object),
}
#[derive(Clone, Debug, PartialEq)]
pub struct FieldRef {
    pub base_ref: Value,
    pub field_offset: usize,
}
impl Value {
    pub fn is_equal(&self, other: &Value, heap: &Heap) -> bool {
        match (self, other) {
            (Self::Int(int), Self::Int(other)) => int == other,
            (Self::Float(float), Self::Float(other)) => float == other,
            (Self::Bool(bool), Self::Bool(other)) => bool == other,
            (Self::Unit, Self::Unit) => true,
            (Self::Function(object), Self::Function(other)) => object == other,
            (Self::NativeFunction(object), Self::NativeFunction(other)) => object == other,
            (Self::Closure(object), Self::Closure(other)) => object == other,
            (Self::StackAddress(address), Self::StackAddress(other)) => address == other,
            (Self::GlobalAddress(address), Self::GlobalAddress(other)) => address == other,
            (Self::Tuple(elements), Self::Tuple(other)) => elements
                .iter()
                .zip(other.iter())
                .all(|(element, other)| element == other),
            (Self::String(string), Self::String(other)) => {
                string.as_string(heap) == other.as_string(heap)
            }
            _ => false,
        }
    }

    pub fn format(&self, heap: &Heap) -> String {
        self.format_recursive(heap, &mut FxHashSet::default())
    }
    fn format_recursive(&self, heap: &Heap, seen_objects: &mut FxHashSet<Object>) -> String {
        match self {
            Value::FieldRef(..) => String::from("*field_ref"),
            Value::IndexRef(..) => String::from("*index_ref"),
            Value::Bool(bool) => {
                format!("{}", *bool)
            }
            Value::Int(int) => {
                format!("{}", *int)
            }
            Value::Float(float) => {
                format!("{}", *float)
            }
            Value::Closure(closure) => {
                format!("fn<{}>", closure.as_closure(heap).function.name)
            }
            Value::Unit => "()".to_string(),
            Value::Tuple(elements) => {
                let mut result = String::from("(");
                for (i, element) in elements.iter().enumerate() {
                    if i > 0 {
                        result.push(',');
                    }
                    result.push_str(&&element.format_recursive(heap, seen_objects));
                }
                result.push(')');
                result
            }
            Value::Record(record) => {
                let mut result = format!("{}{{", record.name);
                for (i, element) in record.fields.iter().enumerate() {
                    if i > 0 {
                        result.push(',');
                    }
                    result.push_str(&element.format_recursive(heap, seen_objects));
                }
                result.push('}');
                result
            }
            Value::VariantRecord(record) => {
                let mut result = format!("{}{{", record.record_data.name);
                for (i, element) in record.record_data.fields.iter().enumerate() {
                    if i > 0 {
                        result.push(',');
                    }
                    result.push_str(&element.format_recursive(heap, seen_objects));
                }
                result.push('}');
                result
            }
            Value::Function(object) => {
                format!("fn<{}>", object.as_function(heap).name)
            }
            Value::NativeFunction(object) => {
                format!("native<{}>", object.as_native_function(heap).name)
            }
            Value::StackAddress(address) | Value::GlobalAddress(address) => {
                format!("*{}", address)
            }
            Value::String(string) => {
                format!("{}", string.as_string(heap))
            }
            Value::Array(array_object) => {
                let mut result = String::from("[");
                let is_recursive = seen_objects.contains(array_object);
                let elements = array_object.as_array(heap);
                seen_objects.insert(*array_object);
                if !is_recursive {
                    for (i, element) in elements.into_iter().enumerate() {
                        if i > 0 {
                            result.push(',');
                        }
                        result.push_str(&element.format_recursive(heap, seen_objects));
                    }
                } else {
                    result.push_str("...");
                }
                result.push(']');
                result
            }
        }
    }
    pub fn print(&self, heap: &Heap) {
        print!("{}", self.format_recursive(heap, &mut FxHashSet::default()))
    }
    pub fn println(&self, heap: &Heap) {
        println!("{}", self.format_recursive(heap, &mut FxHashSet::default()))
    }
}
