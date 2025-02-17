use std::{collections::HashMap, fmt::Debug, hash::Hash};

use indexmap::IndexMap;
use super::types::Type;

pub trait Identifier : Clone + Copy + Hash + PartialEq + Eq + Debug {}
#[derive(Clone, Copy,Hash,PartialEq, Eq, Debug)]
pub enum DefId{
    Function(FunctionId),
    Variable(VariableId)
}

#[derive(Clone, Copy,PartialEq, Eq,Debug,Hash)]
pub struct FunctionId(u32);

#[derive(Clone, Copy,Hash,PartialEq, Eq,Debug)]
pub struct VariableId(u32);
#[derive(Debug,Clone, Copy,PartialEq, Eq,Hash)]
pub struct GenericParamIndex(pub u32);
impl Identifier for FunctionId{}
impl Identifier for VariableId{}

#[derive(Default)]
pub struct Identifiers{
    variable_names : Vec<String>,
    function_names : Vec<String>
}
impl Identifiers{
    pub fn define_variable(&mut self,name : String)->VariableId{
        let id = self.variable_names.len() as u32;
        self.variable_names.push(name);
        VariableId(id)
    }
    pub fn define_function(&mut self,name : String)->FunctionId{
        let id = self.function_names.len() as u32;
        self.function_names.push(name);
        FunctionId(id)
    }

    pub fn get_variable_name(&self,id:VariableId)->&str{
        &self.variable_names[id.0 as usize]
    }
    pub fn get_function_name(&self,id:FunctionId)->&str{
        &self.function_names[id.0 as usize]
    }

}
#[derive(Clone,Hash,PartialEq, Eq,Debug)]
pub struct Binding{
    pub id : DefId,
    pub ty : Type
}
pub enum ValueKind{
    Variable,
    Function
}
#[derive(Clone)]
pub struct Variable{
    pub ty : Type,
    pub by_ref : bool,
    pub id : VariableId
}
#[derive(Clone)]
pub struct Function{
    pub id : FunctionId,
    pub is_generic : bool,
    pub generic_types : Vec<Type>,
    pub param_types : Vec<Type>,
    pub return_type : Type
}
pub struct Parameter{
    pub is_by_ref : bool,
    pub ty : Type
}

#[derive(Clone)]
pub struct FunctionSignature{
    pub generic_types : Vec<Type>,
    pub param_types : Vec<Type>,
    pub return_type : Type
}

#[derive(Clone)]
pub struct Method{
    pub name : String,
    pub self_param_info : Option<bool>,
    pub generic_types : Option<Vec<Type>>,
    pub param_types : Vec<Type>,
    pub return_type : Type
}

#[derive(Clone,)]
pub struct Scope{
    variables : IndexMap<String,Variable>,
    types : IndexMap<String,Type>,
    functions : IndexMap<String,Function>,
}
impl Default for Scope{
    fn default() -> Self {
        Self { 
            variables: IndexMap::new(), 
            types: IndexMap::new(), 
            functions: IndexMap::new()
        }
    }
}
#[derive(Clone,Default)]
pub struct Environment{
    global_scope : Scope,
    scopes : Vec<Scope>,
    methods : IndexMap<Type,HashMap<String,Method>>,
    generic_params : Vec<String>
}

impl Environment{
    pub fn add_generic_param(&mut self,name:String)->GenericParamIndex{
        let index = self.generic_params.len() as u32;
        self.generic_params.push(name);
        GenericParamIndex(index)
    }
    pub fn remove_generic_params(&mut self,param_count:usize){
        self.generic_params.truncate(self.generic_params.len() - param_count);
    }
    pub fn get_generic_param(&self,name:&str)->Option<GenericParamIndex>{
        self.generic_params.iter().enumerate().rev().find(|(_,param_name)| *param_name == name).map(|(i,_)| GenericParamIndex(i as u32))
    }
    pub fn begin_scope(&mut self){
        self.scopes.push(Scope::default());
    }
    pub fn end_scope(&mut self){
        self.scopes.pop();
    }
    fn current_scope_mut(&mut self)->&mut Scope{
        self.scopes.last_mut().unwrap_or_else(|| &mut self.global_scope)
    }
    fn current_scope(&self)->&Scope{
        self.scopes.last().unwrap_or_else(|| &self.global_scope)
    }
    fn traverse_scopes<T>(&self,f:impl Fn(&Scope)->Option<&T>)->Option<&T>{
        self.scopes.iter().rev().filter_map(|scope| f(scope)).next().or_else(|| f(&self.global_scope))
    }
    pub fn add_variable(&mut self,name:String,ty:Type,by_ref : bool,id:VariableId){
         self.current_scope_mut().variables.insert(name, Variable{ty,by_ref,id});
    }
    pub fn add_function(&mut self,name:String,function : Function){
        self.current_scope_mut().functions.insert(name, function);
    }
    pub fn get_variable(&self,name:&str)->Option<&Variable>{
        self.traverse_scopes(|scope|{
            scope.variables.get(name)
        })
    }
    pub fn get_function(&self,name:&str)->Option<&Function>{
        self.traverse_scopes(|scope|{
            scope.functions.get(name)
        })
    }
    pub fn get_function_by_id(&self,id:FunctionId)->Option<&Function>{
        self.traverse_scopes(|scope| scope.functions.values().find(|function| function.id == id))
    }
    pub fn add_type(&mut self,name:String,ty:Type){
        self.current_scope_mut().types.insert(name, ty);
    }
    pub fn get_type(&self,name:&str)->Option<&Type>{
        self.traverse_scopes(|scope| scope.types.get(name))
    }
    pub fn is_type_in_local_scope(&self,name:&str)->bool{
        self.current_scope().types.get(name).is_some()
    }
    pub fn is_function_in_local_scope(&self,name:&str)->bool{
        self.current_scope().functions.get(name).is_some()
    }

    pub fn add_method(&mut self,ty:Type,name:String,method : Method)->bool{
        self.methods.entry(ty).or_insert(HashMap::new()).insert(name, method).is_none()
    }

    pub fn get_method(&self,ty:&Type,name:&str)->Option<&Method>{
        self.methods.get(ty).and_then(|methods|{
            methods.get(name)
        })
    }
    

}