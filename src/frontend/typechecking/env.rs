use fxhash::FxHashMap;


use crate::{identifiers::VariableIndex, identifiers::FuncIndex};

use super::types::Type;
pub struct Environment{
    variable_types : FxHashMap<VariableIndex,Type>,
    function_types : FxHashMap<FuncIndex,Type>
}

impl Environment{
    pub fn new()->Self{
        Environment{
            variable_types : FxHashMap::default(),
            function_types: FxHashMap::default()
        }
    }
    pub fn define_variable_type(&mut self,variable:VariableIndex,ty:Type){
        self.variable_types.insert(variable, ty);
    }
    pub fn define_function_type(&mut self,function:FuncIndex,ty:Type){
        self.function_types.insert(function, ty);
    }
    pub fn get_variable_type(&self,variable:VariableIndex)->Type{
        self.variable_types[&variable].clone()
    }
    pub fn get_function_type(&self,function:FuncIndex)->Type{
        self.function_types[&function].clone()
    }
}