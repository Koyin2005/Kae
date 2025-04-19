use super::Type;
#[derive(Clone,Debug,PartialEq)]
pub struct GenericArgs(Vec<Type>);

impl GenericArgs{
    pub fn new_empty() -> Self{
        Self(Vec::new())
    }
    pub fn new(args : Vec<Type>) -> Self{
        GenericArgs(args)
    }

    pub fn is_empty(&self) -> bool{
        self.0.is_empty()
    }
    pub fn expect(&self,index : usize) -> Type{
        self.0[index].clone()
    }

    pub fn get(&self,index : usize) -> Option<Type>{
        self.0.get(index).cloned()
    }
    pub fn iter(&self) -> GenericArgsIter<'_>{
       GenericArgsIter(self.0.iter())
    }
    pub fn len(&self) -> usize{
        self.0.len()
    }
}


pub struct GenericArgsIter<'a>(std::slice::Iter<'a,Type>);

impl<'a> Iterator for GenericArgsIter<'a>{
    type Item = &'a Type;
    fn next(&mut self) -> Option<Self::Item>{
        self.0.next()
    }
}