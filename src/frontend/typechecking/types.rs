use std::fmt::Display;

use indexmap::IndexMap;

use super::{generics::substitute,  typechecker::GenericTypeId};



#[derive(Clone, Copy,PartialEq, Eq,Debug,Default)]
pub struct StructId(usize);

#[derive(Clone)]
pub struct StructField{
    pub name : String,
    pub field_type : Type
}
#[derive(Clone)]
pub struct Struct{
    pub fields : Vec<(String,Type)>
}

impl Struct{
    pub fn get_field(&self,name:&str)->Option<(usize,&Type)>{
        self.fields.iter().enumerate().filter_map(|(index,field)| if field.0 == name { Some((index,&field.1))} else {None}).next()
    }
    pub fn add_fields(&mut self,fields:impl Iterator<Item = (String,Type)>){
        self.fields.extend(fields);
    }
}

#[derive(Clone,Default)]
pub struct Structs{
    structs : Vec<Struct>,
    next_struct_id : StructId,
}
impl Structs{
    
    pub fn define_struct(&mut self,fields : impl Iterator<Item = (String,Type)>)->StructId{
        let id = self.next_struct_id;
        self.structs.push(Struct{
            fields : fields.collect()
        });
        self.next_struct_id = StructId(id.0+1);
        id
    }
    pub fn get_struct_info(&self,id:&StructId) ->Option<&Struct>{
        self.structs.get(id.0)
    }
    pub fn update_struct_info(&mut self,id:&StructId,mut update : impl FnMut(&mut Struct)){
        update(self.structs.get_mut(id.0).expect("Cannot get struct id without creating a struct"));
    }
}

#[derive(Debug,Clone, Copy,PartialEq,Eq)]
pub struct EnumId(usize);

#[derive(Clone)]
pub struct EnumVariant{
    pub discrim : usize,
    pub name : String,
    pub fields : Vec<(String,Type)>,
}
#[derive(Clone)]
pub struct Enum{
    pub name : String,
    pub variants : Vec<EnumVariant>
}
#[derive(Clone,Default)]
pub struct Enums{
    enums : Vec<Enum>
}
impl Enums{
    pub fn define_enum(&mut self,name:String,variants : Vec<EnumVariant> )->EnumId{
        self.enums.push(Enum { name,variants });
        EnumId(self.enums.len()-1)
    }
    pub fn get_enum(&self,enum_id:EnumId)->&Enum{
        &self.enums[enum_id.0]
    }
    pub fn update_enum(&mut self,enum_id:EnumId,mut update : impl FnMut(&mut Enum)){
        update(&mut self.enums[enum_id.0]);
    }
}

#[derive(Default,Clone)]
pub struct TypeContext{
    pub structs : Structs,
    pub enums : Enums
}
#[derive(Clone, Copy,PartialEq, Eq,Debug)]
pub struct FunctionId(usize);


impl FunctionId{
    pub const DEFAULT : Self = FunctionId(0);

    pub fn next(&self)->Self{
        Self(self.0+1)
    }
}

impl Default for FunctionId{
    fn default() -> Self {
        Self::DEFAULT
    }
}

pub type GenericArgs = IndexMap<GenericTypeId,Type>;

#[derive(Clone,Debug)]
pub enum Type {
    Int,
    Float,
    Bool,
    String,
    Never,
    Unit,
    Array(Box<Type>),
    Tuple(Vec<Type>),
    Function{
        generic_args : GenericArgs,
        params : Vec<Type>, 
        return_type : Box<Type>
    },
    Param{
        name : String,
        index : GenericTypeId,
    },
    Struct{
        generic_args :  GenericArgs,
        id : StructId,
        name : String,
    },
    Enum{
        generic_args : GenericArgs,
        id : EnumId,
        name : String
    },
    EnumVariant{
        generic_args : GenericArgs,
        id : EnumId,
        name : String,
        variant_index : usize,
    },
    Unknown,

}
impl PartialEq for Type{
    fn eq(&self, other: &Self) -> bool {
        match (self,other){
            (Type::Int,Type::Int)|
            (Type::Float,Type::Float)|
            (Type::String,Type::String)|
            (Type::Bool,Type::Bool)|
            (Type::Unit,Type::Unit)|
            (Type::Never,Type::Never) => true,
            (Type::Array(self_elements),Type::Array(other_elements)) => self_elements == other_elements,
            (Type::Param { name, index },Type::Param { name:other_name, index:other_index }) => 
                name == other_name && index == other_index,
            (Type::Function { generic_args, params, return_type },Type::Function { generic_args:other_generic_args, params:other_params, return_type:other_return_type }) => {
                    if generic_args.is_empty() && other_generic_args.is_empty(){
                        return params.iter().zip(other_params.iter()).all(|(param,other_param)| param == other_param) && return_type == other_return_type;
                    }
                    params.iter().map(|ty| substitute(ty.clone(), generic_args)).zip(other_params.iter().map(|ty| substitute(ty.clone(), other_generic_args))).all(|(ty,other)| ty == other) &&
                    substitute(*return_type.clone(), generic_args) == substitute(*other_return_type.clone(), other_generic_args)
            },
            (Type::Tuple(elements),Type::Tuple(other_elements)) => elements == other_elements,
            (Type::Struct { generic_args, id, .. },Type::Struct { generic_args:other_generic_args, id:other_id,.. }) => {
                id == other_id && generic_args.values().zip(other_generic_args.values()).all(|(arg,other_arg)| arg == other_arg)
            },
            (Type::Enum { id, .. },Type::Enum { id:other_id,.. }) => id == other_id,
            
            (Type::EnumVariant { id, variant_index,.. },Type::EnumVariant { id:other_id,variant_index:other_index,.. }) => 
                id == other_id && variant_index == other_index,
            (_,_) => false
        }
    }
}
impl Type{
    pub fn is_variant_of(&self,other:&Type)->bool{
        match (self,other){
            (Type::EnumVariant { id:other_id,.. },Type::Enum { id, .. }) => id == other_id,
            _ => false
        }
    }
    pub fn get_field_index(&self,field_name:&str,type_context:&TypeContext)->Option<usize>{
        match (self,field_name){
            (Type::Struct { id, .. },field_name) => {
                type_context.structs.get_struct_info(id)
                    .and_then(|struct_| struct_.get_field(field_name)
                    .map(|(index,_)| {
                        index
                }))
            },
            (Type::EnumVariant { id,  variant_index,.. },field_name) => {
                type_context.enums.get_enum(*id).variants[*variant_index].fields.iter().position(|(field,_)| field ==  field_name).map(|index| index+1)
                    
            }
            _ => None
        }

    }
    pub fn get_field(&self,field_name:&str,type_context:&TypeContext)->Option<Type>{
        match (self,field_name){
            (Type::Array(..),"length") => Some(Type::Int),
            (Type::Struct { generic_args, id, .. },field_name) => {
                type_context.structs.get_struct_info(id)
                    .and_then(|struct_| struct_.get_field(field_name)
                    .map(|(_,ty)| {
                        let ty = ty.clone();
                        if !generic_args.is_empty() { substitute(ty, generic_args)} else { ty }
                }))
            },
            (Type::EnumVariant { id,  variant_index,generic_args,.. },field_name) => {
                type_context.enums.get_enum(*id).variants[*variant_index].fields.iter().find(|(field,_)| field ==  field_name).map(|(_,ty)| 
                   if !generic_args.is_empty() {substitute(ty.clone(), generic_args)} else { ty.clone()})
                    
            }
            _ => None
        }
    }
    pub fn is_unknown(&self)->bool{
        match self{
            Type::Unknown => true,
            Type::Array(element) => element.is_unknown(),
            Type::Tuple(elements) => elements.iter().any(|ty| ty.is_unknown()),
            Type::Function { params, return_type,.. } => params.iter().any(|ty| ty.is_unknown()) || return_type.is_unknown(),
            _ => false
        }
    }

    pub fn get_generic_args(&self)->Option<GenericArgs>{
        match self{
            Type::Function { generic_args, .. } => {
                if generic_args.is_empty() { None} else {
                    Some(generic_args.clone())
                }
            },
            _ => None
        }
    }

    pub fn is_closed(&self)->bool{
        match self{
            Type::Array(element_type) => element_type.is_closed(),
            Type::Param{..} => false,
            Type::Tuple(elements) => elements.iter().all(|ty| ty.is_closed()),
            Type::Function { generic_args, params, return_type } => 
                generic_args.values().all(|ty| ty.is_closed()) && params.iter().all(|param| param.is_closed()) && return_type.is_closed(),
            Type::Struct { generic_args, ..} => generic_args.values().all(|ty| ty.is_closed()),
            _ => true,
        }
    }

}

fn fmt_generic_args(f:&mut std::fmt::Formatter<'_>,generic_args:&GenericArgs)->std::fmt::Result{
    if !generic_args.is_empty(){
        write!(f,"[")?;
        for (i,arg) in generic_args.values().enumerate(){
            if i>0{
                write!(f,",")?;
            }
            write!(f,"{}",arg)?;
        }
        write!(f,"]")
    }
    else{
        Ok(())
    }
}
impl Display for Type{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self{
            Type::Int => write!(f,"int"),
            Type::Float => write!(f,"float"),
            Type::String => write!(f,"string"),
            Type::Bool => write!(f,"bool"),
            Type::Never => write!(f,"never"),
            Type::Unit => write!(f,"()"),
            Type::Array(element) => write!(f,"[{}]",element),
            Type::Tuple(elements) => {
                write!(f,"(")?;
                for (i,ty) in elements.iter().enumerate(){
                    if i>0{
                        write!(f,",")?;
                    }
                    write!(f,"{}",ty)?;
                }
                write!(f,")")
            },
            Type::Function { params, return_type,.. } => {
                write!(f,"(")?;
                for (i,param) in params.iter().enumerate(){
                    if i>0{
                        write!(f,",")?;
                    }
                    write!(f,"{}",param)?;
                }
                write!(f,")->{}",return_type)
            },
            Type::Param { name ,..} => write!(f,"{}",name),
            Type::Unknown => write!(f,"_"),
            Type::Enum {name,generic_args,.. } => {
                write!(f,"{}",name)?;
                fmt_generic_args(f, generic_args)
            },
            Type::EnumVariant {name,generic_args,.. } => {
                write!(f,"{}",name)?;
                fmt_generic_args(f, generic_args)
            }
            Type::Struct { generic_args, name,.. } => {
                write!(f,"{}",name)?;
                fmt_generic_args(f, generic_args)
            }
        }
    }
}