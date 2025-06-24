use std::{marker::PhantomData, ops::{Index, IndexMut}};


pub trait IntoIndex : Copy{
    fn new(index:u32)-> Self;
    fn as_index(&self) -> u32;
}
#[derive(Debug)]
pub struct IndexVec<Index,Value> where Index : IntoIndex{
    data : Vec<Value>,
    _phantom : PhantomData<Index>
}
impl<Index:IntoIndex,Value> Default for IndexVec<Index,Value>{
    fn default() -> Self {
        Self { data: Default::default(), _phantom: Default::default()  }
    }
}
impl<Index:IntoIndex,Value> IndexVec<Index,Value>{
    pub fn new()->Self{
        Self::with_capacity(0)
    }
    pub fn from(value:Value, len: usize) -> Self where Value:Clone{
        Self { data: vec![value;len], _phantom: PhantomData }
    }
    pub fn last(&self) -> Option<&Value>{
        self.data.last()
    }
    pub fn last_mut(&mut self) -> Option<&mut Value>{
        self.data.last_mut()
    }
    pub fn last_index(&self) -> Option<Index>{
        let last = (self.len() as u32).checked_sub(1)?;
        Some(Index::new(last))
    }
    pub fn with_capacity(capacity:usize) -> Self{
        Self { data: Vec::with_capacity(capacity), _phantom: PhantomData }
    }
    pub fn push(&mut self,val:Value)->Index{
        let index = Index::new(self.data.len() as u32);
        self.data.push(val);
        index
    }
    pub fn get(&self,index:Index) -> Option<&Value>{
        self.data.get(index.as_index() as usize)
    }
    pub fn get_mut(&mut self,index:Index) -> Option<&mut Value>{
        self.data.get_mut(index.as_index() as usize)
    }
    pub fn retain_mut(&mut self,mut f:impl FnMut(Index,&mut Value) -> bool){
        let mut index:u32 = 0;
        self.data.retain_mut(|val|{
            let should_retain = f(Index::new(index),val);
            index += 1;
            should_retain
        });
    }
    pub fn index_value_iter(&self)->impl '_ + std::iter::Iterator<Item = (Index,&'_ Value)>{
        self.data.iter().enumerate().map(|(i,value)| (Index::new(i as u32),value))
    }
    pub fn index_value_iter_mut(&mut self)->impl '_ + std::iter::Iterator<Item = (Index,&'_ mut Value)>{
        self.data.iter_mut().enumerate().map(|(i,value)| (Index::new(i as u32),value))
    }
    pub fn iter(&self)->IndexVecIter<'_,Index,Value>{
        IndexVecIter { iter : self.data.iter(),phantom:PhantomData}
    }
    pub fn iter_mut(&mut self)->IndexVecIterMut<'_,Index,Value>{
        IndexVecIterMut { iter : self.data.iter_mut(),phantom:PhantomData}
    }
    pub fn indices(&self) -> impl Iterator<Item = Index>{
        (0..self.len()).map(|i| Index::new(i as u32))
    }
    pub fn is_empty(&self) -> bool{ self.data.is_empty() }
    pub fn len(&self)->usize{
        self.data.len()
    }
}
impl<Index:IntoIndex,Value:Clone> Clone for IndexVec<Index,Value>{
    fn clone(&self) -> Self {
        Self { data: self.data.clone(), _phantom: PhantomData }
    }
}

impl <Index:IntoIndex,Value> IntoIterator for IndexVec<Index,Value>{
    type IntoIter = std::vec::IntoIter<Value>;
    type Item = Value;
    fn into_iter(self) -> Self::IntoIter {
        self.data.into_iter()
    }
}
impl<Index:IntoIndex,Value> FromIterator<Value> for IndexVec<Index,Value>{
    fn from_iter<T: IntoIterator<Item = Value>>(iter: T) -> Self {
        Self { data: iter.into_iter().collect(), _phantom: PhantomData }
    }
}
impl<I:IntoIndex,V> Index<I> for IndexVec<I,V>{
    type Output = V;
    fn index(&self, index: I) -> &Self::Output {
        &self.data[index.as_index() as usize]
    }
}
impl<I:IntoIndex,V> IndexMut<I> for IndexVec<I,V>{
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        &mut self.data[index.as_index() as usize]
    }
}
pub struct IndexVecIter<'a,I:IntoIndex,V>{
    iter : std::slice::Iter<'a,V>,
    phantom : PhantomData<I>
}

pub struct IndexVecIterMut<'a,I:IntoIndex,V>{
    iter : std::slice::IterMut<'a,V>,
    phantom : PhantomData<I>
}

impl<I:IntoIndex,T> ExactSizeIterator for IndexVecIterMut<'_,I,T>{
    
}
impl<'a,Index:IntoIndex,Value> Iterator for IndexVecIterMut<'a,Index,Value>{
    type Item =  &'a mut Value;
    fn next(&mut self)->Option<Self::Item>{
        self.iter.next()
    }
    fn size_hint(&self) -> (usize,Option<usize>){
        self.iter.size_hint()
    }
} 
impl<'a,Index:IntoIndex,Value> DoubleEndedIterator for IndexVecIterMut<'a,Index,Value>{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back()
    }
}

impl<I:IntoIndex,T> ExactSizeIterator for IndexVecIter<'_,I,T>{
    
}
impl<'a,Index:IntoIndex,Value> Iterator for IndexVecIter<'a,Index,Value>{
    type Item =  &'a Value;
    fn next(&mut self)->Option<Self::Item>{
        self.iter.next()
    }
    fn size_hint(&self) -> (usize,Option<usize>){
        self.iter.size_hint()
    }
} 
impl<'a,Index:IntoIndex,Value> DoubleEndedIterator for IndexVecIter<'a,Index,Value>{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back()
    }
}
#[macro_export]
macro_rules! define_id {
    ($id:ident) => {
        #[derive(Clone, Copy,PartialEq,Eq,Hash,Debug,Ord,PartialOrd)]
        pub struct $id(u32);
        impl $crate::data_structures::IntoIndex for $id{
            fn new(index:u32)-> Self{
                Self(index)
            }
            fn as_index(&self) -> u32 {
                self.0
            }
        }
    };
    ($id:ident,$comment:meta) => {
        #[$comment]
        #[derive(Clone, Copy,PartialEq,Eq,Hash,Debug,Ord,PartialOrd)]
        pub struct $id(u32);
        impl $crate::data_structures::IntoIndex for $id{
            fn new(index:u32)-> Self{
                Self(index)
            }
            fn as_index(&self) -> u32 {
                self.0
            }
        }
    };
}
