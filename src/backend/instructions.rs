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
    LoadLocalRef(u16),

    StoreLocal(u16),
    
    StoreGlobal(u16),

    LoadGlobal(u16),
    LoadGlobalRef(u16),

    LoadField(u16),
    LoadFieldRef(u16),
    StoreField(u16),

    LoadUpvalue(u16),
    
    StoreUpvalue(u16),
    LoadIndirect,
    StoreIndirect,
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

    LoadIndexRef,
    BuildArray(usize),

    GetArrayLength,
    
    Jump(u16),
    Loop(u16),

    JumpIfFalsePeek(u16),
    JumpIfFalse(u16),
    JumpIfTrue(u16),

    
    JumpIfFalseAndPop(u16),
    Rotate(u16),
    Print(u16),
    Call(u16),

    LoadStackTopOffset(usize),
    Return,
    Pop,
    PopN(usize),
    Copy(u16),

    BuildTuple(usize),
    UnpackTuple,

    BuildRecord(usize),
    BuildVariantRecord(usize)

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
    pub metadata : Vec<ProgramMetadata>,
    pub chunk : Chunk
}
#[derive(Default,Clone,Debug,PartialEq)]
pub struct Chunk{
    pub code : Vec<Instruction>,
    pub lines : Vec<u32>,
    pub locals : usize

}


#[derive(Clone,Debug,PartialEq)]
pub enum ProgramMetadata {
    Struct(StructInfo),
    Variant(VariantInfo)
}

#[derive(Default,Clone,Debug,PartialEq)]
pub struct StructInfo{
    pub name : String,
    pub field_count : usize
}



#[derive(Default,Clone,Debug,PartialEq)]
pub struct VariantInfo{
    pub name : String,
    pub field_count : usize,
    pub discriminant : usize
}