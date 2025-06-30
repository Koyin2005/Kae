use fxhash::FxHashMap;

use crate::{frontend::typechecking::types::Type, identifiers::VariableIndex};

pub struct SelfType(pub Type);
pub struct TypeEnv {
    variables: FxHashMap<VariableIndex, Type>,
    self_ty: Option<SelfType>,
}
impl Default for TypeEnv {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeEnv {
    pub fn new() -> Self {
        Self {
            variables: FxHashMap::default(),
            self_ty: None,
        }
    }
    pub fn set_self_type(&mut self, ty: Option<SelfType>) -> Option<SelfType> {
        std::mem::replace(&mut self.self_ty, ty)
    }
    pub fn get_self_type(&self) -> Option<&SelfType> {
        self.self_ty.as_ref()
    }
    pub fn define_variable_type(&mut self, variable: VariableIndex, ty: Type) {
        self.variables.insert(variable, ty);
    }
    pub fn get_variable_type(&self, variable: VariableIndex) -> Type {
        self.variables
            .get(&variable)
            .cloned()
            .unwrap_or(Type::Error)
    }
}
