use std::rc::Rc;

use super::values::Function;

#[derive(Clone, Copy,Debug,PartialEq)]
pub enum Instruction {
    LoadUnit,
    LoadBool(bool),
    LoadInt(i16),
    LoadConstant(u16),

    LoadLocal(u16),
    StoreLocal(u16),
    StoreGlobal(u16),
    LoadGlobal(u16),
    LoadField(u16),
    StoreField(u16),
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
    InitRecord(u16),
    BuildTuple(u16),
    BuildList(u16),

    GetArrayLength,
    GetStringLength,
    
    Jump(u16),
    Loop(u16),
    JumpIfFalse(u16),
    JumpIfTrue(u16),

    Print(u16),
    Call(u16),
    Return,
    Pop,
    Copy(u16),
}
#[derive(Clone,Debug,PartialEq)]
pub enum Constant{
    String(Rc<str>),
    Float(f64),
    Int(i64),
    Function(Rc<Function>)
    
}
#[derive(Default,Clone,Debug,PartialEq)]
pub struct Chunk{
    pub code : Vec<Instruction>,
    pub constants : Vec<Constant>,
    pub lines : Vec<u32>,
    pub locals : usize

}