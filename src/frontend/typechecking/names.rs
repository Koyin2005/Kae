use indexmap::IndexMap;
use super::types::{FunctionId, Type};


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
    generic_types : Vec<Type>,
    param_types : Vec<Type>,
    return_type : Type
}
#[derive(Clone)]
struct Method{
    name : String,
    generic_types : Vec<Type>,
    param_types : Vec<Type>,
    return_type : Type
}
#[derive(Clone)]
pub struct Environment{
    current_variables : Vec<IndexMap<String,Variable>>,
    current_types : Vec<IndexMap<String,Type>>,
    current_functions : Vec<IndexMap<String,Function>>,
    current_associations : Vec<IndexMap<Type,Vec<Method>>>,
}
impl Default for Environment{
    fn default() -> Self {
        Self { current_variables: vec![IndexMap::new()], current_types:vec![IndexMap::new()], current_functions: vec![IndexMap::new()],current_associations:vec![IndexMap::new()] }
    }
}
impl Environment{
    pub fn begin_scope(&mut self){
        self.current_functions.push(IndexMap::new());
        self.current_types.push(IndexMap::new());
        self.current_functions.push(IndexMap::new());
        self.current_associations.push(IndexMap::new());
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
        self.current_functions.last_mut().unwrap().insert(name, Function { id, param_types, return_type ,generic_types:Vec::new()});
    }

    pub fn add_generic_function(&mut self,name:String,param_types:Vec<Type>,return_type : Type,id : FunctionId,generic_params : impl Iterator<Item = Type>){
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
    pub fn is_type_in_local_scope(&self,name:&str)->bool{
        self.current_types.last().is_some_and(|types| types.contains_key(name))
    }

    pub fn add_method(&mut self,ty:Type,name:String,param_types:Vec<Type>,return_type : Type){
        todo!()
    }
    

}