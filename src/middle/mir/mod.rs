use std::{fmt::Display, hash::Hash};

use crate::{data_structures::{IndexVec, IntoIndex}, define_id, frontend::{ast_lowering::hir::{BinaryOp, BuiltinKind, DefId, UnaryOp}, typechecking::{context::TypeContext, types::{generics::GenericArgs, subst::{Subst, TypeSubst}, Type}}}, 
    identifiers::{BodyIndex, FieldIndex, SymbolIndex, VariantIndex}};

pub mod debug;
pub mod passes;
pub mod basic_blocks;
pub mod traversal;
pub mod visitor;
pub mod dominator;
#[derive(Clone,Debug,PartialEq,Hash)]
pub enum FunctionKind {
    Anon(DefId),
    Normal(DefId),
    Variant(DefId),
    Builtin(BuiltinKind)
}
#[derive(Clone,Debug,PartialEq)]
pub enum ConstantKind {
    Int(i64),
    Bool(bool),
    String(SymbolIndex),
    ZeroSized,
    Float(f64),
    Function(FunctionKind,GenericArgs),
    Aggregrate(AggregrateConstant)
}
impl Hash for ConstantKind{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self{
            Self::Bool(value) => {
                0.hash(state);
                value.hash(state)
            },
            Self::Float(value) => {
                1.hash(state);
                value.to_bits().hash(state)
            },
            Self::Function(kind,args) => { 2.hash(state); kind.hash(state);args.hash(state);},
            Self::Int(value) => {3.hash(state);value.hash(state)},
            Self::String(index) => {4.hash(state);index.hash(state)},
            Self::ZeroSized => 5.hash(state),
            Self::Aggregrate(aggregate_constant) => {
                6.hash(state);
                for constant in aggregate_constant.fields(){
                    constant.hash(state);
                }
            }
        }
    }
}
#[derive(Clone, Copy,Debug,PartialEq,PartialOrd)]
pub enum ConstantNumber{
    Float(f64),
    Int(i64)
}
impl From<ConstantNumber> for Constant{
    fn from(value: ConstantNumber) -> Self {
        match value{
            ConstantNumber::Float(value) => Self { ty: Type::Float, kind: ConstantKind::Float(value) },
            ConstantNumber::Int(value) => Self { ty: Type::Int, kind: ConstantKind::Int(value) }
        }
    }
}
#[derive(Clone,Debug,PartialEq,Hash)]
pub enum AggregrateConstant {
    Array(Box<[Constant]>),
    Tuple(Box<[Constant]>)
}
impl AggregrateConstant{
    fn fields(&self) -> &[Constant]{
        match self{
            Self::Array(fields) | Self::Tuple(fields) => &fields
        }
    }
}
#[derive(Clone,Debug,PartialEq,Hash)]
pub struct  Constant {
    pub ty : Type,
    pub kind : ConstantKind
}
impl Constant{
    pub fn is_float(&self) -> bool{
        matches!(self.kind,ConstantKind::Float(_))
    }
    pub fn eval_to_scalar(&self) -> Option<u128>{
        match self.kind{
            ConstantKind::Float(value) => Some(value.to_bits() as u128),
            ConstantKind::Bool(value) => Some(value as u128),
            ConstantKind::Int(value) => Some(u64::from_ne_bytes(value.to_ne_bytes()) as u128),
            _ => None
        }
    }
    pub fn as_number(&self) -> Option<ConstantNumber>{
        match self.kind{
            ConstantKind::Float(value) => Some(ConstantNumber::Float(value)),
            ConstantKind::Int(value) => Some(ConstantNumber::Int(value)),
            _ => None
        }
    }
}
impl From<bool> for Constant{
    fn from(value: bool) -> Self {
        Constant { ty: Type::Bool, kind: ConstantKind::Bool(value) }
    }
}
pub enum StatementOrTerminator<'a>{
    Statement(&'a Stmt),
    Terminator(&'a Terminator)
}
pub struct Block {
    pub stmts : Vec<Stmt>,
    pub terminator : Option<Terminator>
}
impl Block{
    pub fn expect_terminator(&self) -> &Terminator{
        self.terminator.as_ref().expect("The terminator should be assigned")
    }
    pub fn expect_terminator_mut(&mut self) -> &mut Terminator{
        self.terminator.as_mut().expect("The terminator should be assigned")
    }
}
#[derive(Clone, Copy,PartialEq,Eq,PartialOrd,Ord,Hash,Debug)]
pub struct Location{
    pub basic_block: BlockId,
    pub statement_index: usize
}
impl Location{
    pub fn new(block_id: BlockId, statement_index: usize) -> Self{
        Self { basic_block: block_id, statement_index }
    }
    pub fn next(self) -> Self{
        Self { basic_block: self.basic_block, statement_index: self.statement_index+1 }
    }
}
#[derive(Clone,PartialEq,Debug)]
pub enum PlaceProjection {
    Field(FieldIndex),
    Variant(SymbolIndex,VariantIndex),
    Index(Local),
    ConstantIndex(u64)
}
#[derive(Clone,PartialEq,Debug)]
pub struct Place{
    pub local : Local,
    pub projections : Box<[PlaceProjection]>
}
impl Place{

    pub fn as_local(&self) -> Option<Local>{
        self.projections.is_empty().then_some(self.local)
    }
    pub fn project(self, projection : PlaceProjection) -> Self{
        Self { local: self.local, projections: self.projections.into_vec().into_iter().chain(std::iter::once(projection)).collect() }
    }

    pub fn type_of(&self,ctxt:&TypeContext,body: &Body) -> Type{
        let mut ty = body.locals[self.local].ty.clone();
        let mut projection_iter = self.projections.iter().peekable();
        while let Some(projection) =  projection_iter.next(){
            match projection {
                &PlaceProjection::Field(field) => {
                    ty = ty.field(ctxt, field).expect("This type should have a field");
                    
                },
                &PlaceProjection::Variant(_,variant_index) => {
                    if let Some(&&PlaceProjection::Field(field)) = projection_iter.peek(){
                        let (generic_args,id,_) = ty.as_adt().expect("There should be a def id for enums");
                        ty = TypeSubst::new(generic_args).instantiate_type(&ctxt.get_variant_by_index(id, variant_index).fields[field.as_index() as usize]);
                        projection_iter.next();
                    }
                },
                PlaceProjection::Index(_) | PlaceProjection::ConstantIndex(_) => {
                    ty = ty.index_of().expect("This type should be indexable");
                }
            }
        }
        ty
    }
}
#[derive(Clone)]
pub enum RValue {
    Use(Operand),
    Binary(BinaryOp,Box<(Operand,Operand)>),
    Unary(UnaryOp,Operand),
    Call(Operand,Box<[Operand]>),
    Array(Type,Box<[Operand]>),
    Adt(Box<(DefId,GenericArgs,Option<VariantIndex>)>,IndexVec<FieldIndex,Operand>),
    Tuple(Box<[Type]>,Box<[Operand]>),
    Len(Place),
    Tag(Place)
}
#[derive(Clone,Debug)]
pub enum Operand {
    Constant(Constant),
    Load(Place)
}
impl Operand{
    pub fn as_place(&self) -> Option<&Place>{
        match self{
            Self::Constant(_) => None,
            Self::Load(place) => Some(place)
        }
    }
    pub fn as_constant(&self) -> Option<&Constant>{
        match self{
            Self::Constant(constant) => Some(constant),
            Self::Load(_) => None
        }
    }
}
#[derive(Clone)]
pub enum Stmt{
    Assign(Place,RValue),
    Print(Box<[Operand]>),
    Nop
}
#[derive(Clone)]
pub enum AssertKind {
    ArrayBoundsCheck(Operand,Operand),
    DivisionByZero(Operand),
}
#[derive(Clone)]
pub enum Terminator {
    Goto(BlockId),
    Switch(Operand,Box<[(u128,BlockId)]>,BlockId),
    Assert(Operand,AssertKind,BlockId),
    Return,
    Unreachable
}
impl Terminator{
    fn successors_mut<'a>(&'a mut self) -> Box<[&'a mut BlockId]>{
        match self{
            Self::Assert(_,_, block_id) | Self::Goto(block_id) => Box::new([block_id]),
            Self::Return | Self::Unreachable => Box::new([]),
            Self::Switch(_,targets,default) => {
                targets.iter_mut().map(|(_,target)| target).chain(std::iter::once(default)).collect()
            }
        }
    }
}
define_id!(Local);
define_id!(BlockId);
impl BlockId{
    pub const START_BLOCK : BlockId = BlockId(0);
}
impl Local{
    pub const RETURN_PLACE : Local = Local(0);
}
impl From<Local> for Place{
    fn from(value: Local) -> Self {
        Place { local: value, projections: Box::new([]) }
    }
}
impl Display for BlockId{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("bb{}",self.0))
    }
}
pub struct LocalInfo{
    pub ty : Type
}
pub enum BodyKind {
    Anonymous,
    Function,
    Constructor
}
pub struct BodySource{
    pub id : DefId,
    pub kind : BodyKind,
    pub params : Vec<Type>,
    pub return_type : Type
}
pub struct Body{
    pub source : BodySource,
    pub locals : IndexVec<Local,LocalInfo>,
    pub blocks : IndexVec<BlockId,Block>
}
impl Body{
    pub fn at_location(&self, location: Location) -> StatementOrTerminator{
        let block = &self.blocks[location.basic_block];
        if let Some(stmt) = block.stmts.get(location.statement_index){
            StatementOrTerminator::Statement(stmt)
        }
        else{
            StatementOrTerminator::Terminator(block.expect_terminator())
        }
    }
}

pub struct Mir{
    pub bodies : IndexVec<BodyIndex,Body>
}