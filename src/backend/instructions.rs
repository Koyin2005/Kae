use std::{fmt::Display, rc::Rc};

use super::values::{Function, NativeFunction};

#[derive(Clone, Copy,Debug,PartialEq)]
pub enum Instruction {
    LoadUnit,
    LoadBool(bool),
    LoadInt(i16),
    LoadConstant(u16),

    LoadClosure(u16),
    CloseUpvalue(u16),

    LoadLocal(u16),
    LoadLocalStruct(u16,usize),
    LoadLocalRef(u16),

    StoreLocal(u16),
    StoreLocalStruct(u16,usize),
    
    StoreGlobal(u16),
    StoreGlobalStruct(u16,usize),

    LoadGlobal(u16),
    LoadGlobalStruct(u16,usize),
    LoadGlobalRef(u16),

    LoadField(u16),
    LoadStructField(u16,usize),
    LoadFieldRef(u16),
    StoreField(u16),
    StoreStructField(u16,usize),

    LoadUpvalue(u16),
    LoadUpvalueStruct(u16,usize),
    
    StoreUpvalue(u16),
    StoreUpvalueStruct(u16,usize),

    UnpackTuple,

    AddInt,
    SubtractInt,
    MultiplyInt,
    DivideInt,
    LesserInt,
    GreaterInt,
    LesserEqualsInt,
    GreaterEqualsInt,
    NegateInt,

    AddFloat,
    SubtractFloat,
    MultiplyFloat,
    DivideFloat,
    LesserFloat,
    GreaterFloat,
    LesserEqualsFloat,
    GreaterEqualsFloat,
    NegateFloat,

    Equals,
    NotEquals,
    
    Concatenate,

    LoadIndex,
    StoreIndex,

    BuildRecord(u16),
    BuildCaseRecord(u16),
    BuildTuple(u16),
    BuildList(u16),

    GetArrayLength,
    GetTupleElement(u16),
    
    Jump(u16),
    Loop(u16),

    JumpIfFalsePeek(u16),
    JumpIfFalse(u16),
    JumpIfTrue(u16),

    
    JumpIfFalseAndPop(u16),
    PrintValue(Option<u8>),
    PrintAscii(u8),
    Rotate(u16),
    Print(u16),
    Call(u16),

    LoadStackTopOffset(usize),
    StackAlloc(Option<usize>),
    ReturnStruct(usize),
    Return,
    Pop,
    PopStruct(usize),
    Copy(u16)
}
#[derive(Clone,Debug,PartialEq)]
pub enum Constant{
    String(Rc<str>),
    Float(f64),
    Int(i64),
    Function(Rc<Function>),
    NativeFunction(Rc<NativeFunction>),
    
}
impl Display for Constant{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Float(float) => {
                write!(f,"{}",float)
            },
            Self::Int(int) => {
                write!(f,"{}",int)
            },
            Self::Function(function) => {
                write!(f,"fn<{}>",function.name)
            },
            Self::NativeFunction(function) => {
                write!(f,"native<{}>",function.name)
            },
            Self::String(string) => {
                write!(f,"{:?}",string)
            }
        }
    }
}

#[derive(Default,Clone,Debug,PartialEq)]
pub struct Program{
    pub constants : Vec<Constant>,
    pub names : Vec<Rc<str>>,
    pub chunk : Chunk
}
#[derive(Default,Clone,Debug,PartialEq)]
pub struct Chunk{
    pub code : Vec<Instruction>,
    pub lines : Vec<u32>,
    pub locals : usize

}
