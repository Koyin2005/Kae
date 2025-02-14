use std::{collections::{HashMap, HashSet}, marker::PhantomData};

use super::{parsing::ast::NodeId, typechecking::types::Type};

pub mod resolver;

trait IntoIndex : Copy{
    fn new(index:usize)-> Self;
    fn as_index(&self) -> usize;
}
#[derive(Default,Debug)]
pub struct Fields{
    pub info : IndexVec<FieldIndex,FieldInfo>,
    pub names : HashMap<String,FieldIndex>
}
#[derive(Debug)]
pub struct FieldInfo{
    pub name : String,
    pub ty : Type
}
#[derive(Default,Debug)]
pub struct VariantInfo{
    pub name : String,
    pub(super) fields : Fields
}

#[derive(Default,Debug)]
pub struct EnumInfo{
    pub name : String,
    variants : IndexVec<VariantIndex,VariantInfo>,
    pub(super) variant_names : HashMap<String,VariantIndex>
}
#[derive(Debug)]
pub struct StructInfo{
    pub name : String,
    pub(super) fields : Fields
}
#[derive(Debug,Clone)]
pub struct FunctionParamInfo(pub Type);
#[derive(Debug)]
pub struct FunctionInfo{
    pub params : Vec<FunctionParamInfo>,
    pub return_type : Type
}
#[derive(Default,Debug)]
pub struct NameContext{

    function_info : IndexVec<FuncIndex,FunctionInfo>,
    struct_info : IndexVec<StructIndex,StructInfo>, 
    enum_info : IndexVec<EnumIndex,EnumInfo>,


    struct_id_map : HashMap<NodeId,StructIndex>,
    enum_id_map : HashMap<NodeId,EnumIndex>,
    function_id_map : HashMap<NodeId,FuncIndex>,
    variable_id_type_map : HashMap<NodeId,Type>
}

#[derive(Debug)]
struct IndexVec<Index,Value> where Index : IntoIndex{
    data : Vec<Value>,
    _phantom : PhantomData<Index>
}
impl<Index:IntoIndex,Value> Default for IndexVec<Index,Value>{
    fn default() -> Self {
        Self { data: Default::default(), _phantom: Default::default()  }
    }
}
impl<Index:IntoIndex,Value> IndexVec<Index,Value>{
    fn new()->Self{
        Self { data: Vec::new(), _phantom: PhantomData }
    }
    fn push(&mut self,val:Value)->Index{
        let index = Index::new(self.data.len());
        self.data.push(val);
        index
    }
    fn get(&self,index:Index) -> Option<&Value>{
        self.data.get(index.as_index())
    }
    fn get_mut(&mut self,index:Index) -> Option<&mut Value>{
        self.data.get_mut(index.as_index())
    }
    fn iter(&self)->IndexVecIter<'_,Index,Value>{
        IndexVecIter { index_vec: self, index: 0 }
    }
}

impl<Index:IntoIndex,Value> FromIterator<Value> for IndexVec<Index,Value>{
    fn from_iter<T: IntoIterator<Item = Value>>(iter: T) -> Self {
        Self { data: iter.into_iter().collect(), _phantom: PhantomData }
    }
}
struct IndexVecIter<'a,I:IntoIndex,V>{
    index_vec : &'a IndexVec<I,V>,
    index : usize
}
impl<'a,Index:IntoIndex,Value> Iterator for IndexVecIter<'a,Index,Value>{
    type Item =  &'a Value;
    fn next(&mut self)->Option<Self::Item>{
        let index = Index::new(self.index);
        let item = self.index_vec.get(index);
        self.index += 1;
        item
    }
} 

macro_rules! define_id {
    ($id:ident) => {
        #[derive(Clone, Copy,PartialEq,Eq,Hash,Debug)]
        pub struct $id(usize);
        impl IntoIndex for $id{
            fn new(index:usize)-> Self{
                Self(index)
            }
            fn as_index(&self) -> usize {
                self.0
            }
        }
    };
}

define_id!(StructIndex);
define_id!(EnumIndex);
define_id!(FuncIndex);
define_id!(VariantIndex);
define_id!(FieldIndex);