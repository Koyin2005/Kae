use fxhash::FxHashMap;

use crate::{frontend::typechecking::types::Type, identifiers::VariableIndex};

pub struct TypeEnv{
    variables : FxHashMap<VariableIndex,Type>
}

impl TypeEnv{
    pub fn new() -> Self{
        Self { variables: FxHashMap::default() }
    }

    pub fn define_variable_type(&mut self,variable: VariableIndex,ty : Type){
        self.variables.insert(variable, ty);
    }
    pub fn get_variable_type(&self,variable: VariableIndex) -> Type{
        self.variables.get(&variable).cloned().unwrap_or(Type::Error)
    }
}