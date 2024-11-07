use indexmap::IndexMap;

use super::{typechecker::GenericTypeId, types::{FunctionId, Type}};


pub enum ValueKind{
    Variable,
    Function
}
#[derive(Clone)]
struct Variable{
    ty : Type
}
#[derive(Clone)]
struct Function{
    id : FunctionId,
    generic_types : IndexMap<GenericTypeId,Type>,
    param_types : Vec<Type>,
    return_type : Type
}

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
            fields : fields.map(|(name,ty)| {
                (name, ty )
            }).collect()
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
#[derive(Clone)]
pub struct Environment{
    current_variables : Vec<IndexMap<String,Variable>>,
    current_types : Vec<IndexMap<String,Type>>,
    current_functions : Vec<IndexMap<String,Function>>,
}
impl Default for Environment{
    fn default() -> Self {
        Self { current_variables: vec![IndexMap::new()], current_types:vec![IndexMap::new()], current_functions: vec![IndexMap::new()] }
    }
}
impl Environment{
    pub fn begin_scope(&mut self){
        self.current_functions.push(IndexMap::new());
        self.current_types.push(IndexMap::new());
        self.current_functions.push(IndexMap::new());
    }
    pub fn add_variable(&mut self,name:String,ty:Type){
         self.current_variables.last_mut().unwrap().insert(name, Variable{ty});
    }

    pub fn add_variables(&mut self,variables : impl Iterator<Item = (String,Type)>){
        for (name,ty) in variables{
            self.add_variable(name, ty);
        }
    }

    pub fn add_function(&mut self,name:String,param_types:Vec<Type>,return_type : Type,id : FunctionId){
        self.current_functions.last_mut().unwrap().insert(name, Function { id, param_types, return_type ,generic_types:IndexMap::new()});
    }

    pub fn add_generic_function(&mut self,name:String,param_types:Vec<Type>,return_type : Type,id : FunctionId,generic_params : impl Iterator<Item = (GenericTypeId,Type)>){
        self.current_functions.last_mut().unwrap().insert(name, Function { id, param_types, return_type ,generic_types:generic_params.collect()});
    }
    pub fn get_variable(&self,name:&str)->Option<&Type>{
        self.current_variables.iter().rev().filter_map(|vars| vars.get(name).map(|Variable { ty,.. }| ty)).next()
    }
    pub fn get_function_id(&self,name:&str)->Option<FunctionId>{
        self.current_functions.last().unwrap().get(name).map(|Function { id,..}|{
            *id
        })
    }
    pub fn get_function_type(&self,name:&str)->Option<Type>{
        self.current_functions.iter().rev().filter_map(|funcs| funcs.get(name).map(|Function { generic_types, param_types, return_type,.. }|{
            Type::Function { generic_args:generic_types.clone(), params: param_types.clone(), return_type: Box::new(return_type.clone()) }
        })).next()
    }
    pub fn add_type(&mut self,name:String,ty:Type){
        self.current_types.last_mut().unwrap().insert(name, ty);
    }
    pub fn get_type(&self,name:&str)->Option<&Type>{
        self.current_types.iter().rev().filter_map(|types| types.get(name)).next()
    }

}