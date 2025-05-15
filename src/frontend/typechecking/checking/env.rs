use fxhash::FxHashMap;

use crate::{frontend::{ast_lowering::hir::DefId, typechecking::types::{generics::GenericArgs, Type}}, identifiers::VariableIndex};

#[derive(Clone)]
pub struct TraitConstraint{
    pub id : DefId,
    pub generic_args : GenericArgs
}
pub enum SelfType {
    Ty(Type),
    Trait(TraitConstraint)
}
impl SelfType{
    pub fn as_ty(&self) -> Option<&Type>{
        match self{
            Self::Ty(ty) => Some(ty),
            Self::Trait(_) => None
        }
        
    }
    pub fn as_trait(&self) -> Option<&TraitConstraint>{
        match self{
            Self::Ty(_) => None,
            Self::Trait(trait_) => Some(trait_)
        }
        
    }
}
pub struct TypeEnv{
    variables : FxHashMap<VariableIndex,Type>,
    generic_constraints : Vec<Option<TraitConstraint>>,
    self_ty : Option<SelfType>
}

impl TypeEnv{
    pub fn new() -> Self{
        Self {
             variables: FxHashMap::default(),
             generic_constraints : Vec::new(),
             self_ty : None
        }
    }
    pub fn set_self_type(&mut self,ty:Option<SelfType>) -> Option<SelfType>{
        std::mem::replace(&mut self.self_ty, ty)
    }
    pub fn get_self_type(&self) -> Option<&SelfType>{
        self.self_ty.as_ref()
    }
    pub fn get_generic_constraint_at(&self,param_index:u32) -> Option<&TraitConstraint>{
        (&self.generic_constraints[param_index as usize]).as_ref()
    }
    pub fn generic_constraint_count(&self) -> usize{
        self.generic_constraints.len()
    }
    pub fn truncate_generic_constraints(&mut self,count:usize){
        self.generic_constraints.truncate(count);
    }
    pub fn add_generic_constraint(&mut self,constraint:Option<TraitConstraint>){
        self.generic_constraints.push(constraint);
    }
    pub fn define_variable_type(&mut self,variable: VariableIndex,ty : Type){
        self.variables.insert(variable, ty);
    }
    pub fn get_variable_type(&self,variable: VariableIndex) -> Type{
        self.variables.get(&variable).cloned().unwrap_or(Type::Error)
    }
}