use std::{cell::Cell, collections::BTreeMap};

use fxhash::{FxHashMap, FxHashSet};
use indexmap::IndexMap;

use crate::{data_structures::{IndexVec, IntoIndex}, frontend::{ast_lowering::{hir::Ident, SymbolIndex, SymbolInterner}, parsing::ast::{self, NodeId, ParsedAssignmentTargetKind}, tokenizing::SourceLocation, }, identifiers::{GenericParamIndex, VariableIndex}};

use super::hir::{GenericOwner, PrimitiveType};
use crate::identifiers::{EnumIndex, FieldIndex, FuncIndex, ImplIndex, StructIndex, VariantIndex,ScopeIndex};

pub struct ResolutionError;
#[derive(Clone,Debug,PartialEq,Eq,Copy)]
pub enum Type {
    Struct(StructIndex),
    Enum(EnumIndex),
    PrimitiveType(PrimitiveType),
}
#[derive(Debug,PartialEq,Eq)]
pub enum VariableUse {
    Local,
    Global,
    Upvar
}
#[derive(Debug,PartialEq,Eq )]
pub enum ResolutionResult {
    Variable(VariableIndex,VariableUse),
    Function(FuncIndex),
    Type(Type),
    None
}
#[derive(Default,Debug,Clone,PartialEq)]
enum ScopeKind{
    #[default]
    Normal,
    Function
}
#[derive(Default,Clone,Debug)]
pub struct Scope{
    functions : FxHashMap<SymbolIndex,FuncIndex>,
    types : FxHashMap<SymbolIndex,Type>,
    variables : FxHashMap<SymbolIndex,VariableIndex>,
    pub prev_scope : Option<ScopeIndex>,
    kind : ScopeKind
}
impl Scope{
    fn new_with_prev_scope(scope:ScopeIndex,kind:ScopeKind)->Self{
        Self { functions: Default::default(), types: Default::default(), variables: Default::default(), prev_scope: Some(scope), kind }
    }
    pub fn new_global_scope()->Self{
        Self { functions: Default::default(), types: Default::default(), variables: Default::default(), prev_scope: None, kind:ScopeKind::Normal }
    }
}
impl Scope{
    pub fn define_variable(&mut self,index:SymbolIndex,variable:VariableIndex){
        self.variables.insert(index, variable);
    }
    fn define_function(&mut self,index:SymbolIndex,func:FuncIndex)->bool{
        if let Some(old_func) = self.functions.insert(index, func){
            self.functions.insert(index, old_func);
            return false;
        }
        true
    }
    fn define_type(&mut self,index:SymbolIndex,ty:Type)->bool{
        if let Some(old_ty) = self.types.insert(index, ty){
            self.types.insert(index, old_ty);
            return false;
        }
        true
    }
    pub fn get_type(&self,index:SymbolIndex,scopes:&IndexVec<ScopeIndex,Scope>)->ResolutionResult{
        let result = if let Some(ty) = self.types.get(&index){
            ResolutionResult::Type(*ty)
        }
        else {
            ResolutionResult::None
        };
        if result != ResolutionResult::None{
            return result;
        }
        let mut prev_scope = self.prev_scope;
        while let Some(scope) =  prev_scope{
            let current_scope = &scopes[scope];
            let result = if let Some(ty) = current_scope.types.get(&index){
                ResolutionResult::Type(*ty)
            }
            else{
                ResolutionResult::None
            };
            if result != ResolutionResult::None{
                return result;
            }
            prev_scope = current_scope.prev_scope;
        } 
        result  
    }
    pub fn get_value(scope:ScopeIndex,index:SymbolIndex,scopes:&IndexVec<ScopeIndex,Scope>)->ResolutionResult{
        let mut next_scope = Some(scope);
        let mut is_upvar = false;
        while let Some(scope) = next_scope{
            let current_scope = &scopes[scope];
            let result = if let Some(variable) = current_scope.variables.get(&index){
                ResolutionResult::Variable(
                    *variable,
                    if current_scope.prev_scope.is_none() { 
                        VariableUse::Global
                    } 
                    else if is_upvar{
                        VariableUse::Upvar
                    }
                    else{
                        VariableUse::Local 
                    }
                )
            }
            else if let Some(function) = current_scope.functions.get(&index){
                ResolutionResult::Function(*function)
            }
            else {
                ResolutionResult::None
            };
            if result != ResolutionResult::None{
                return result;
            }
            is_upvar |= current_scope.kind == ScopeKind::Function;
            next_scope = current_scope.prev_scope;
        }
        ResolutionResult::None
    }
}
pub struct Record{
    pub name : Ident,
    pub fields : IndexVec<FieldIndex,Ident>
}
pub struct NamesFound{
    pub(super) variables : IndexVec<VariableIndex,(ScopeIndex,usize,Ident)>,
    pub(super) variable_defs: FxHashMap<NodeId,VariableIndex>,
    pub(super) all_scopes : IndexVec<ScopeIndex,Scope>,
    pub(super) scope_map : FxHashMap<NodeId,ScopeIndex>,
    pub(super) variable_def_map : FxHashMap<NodeId,Vec<VariableIndex>>,
    pub(super) structs : IndexVec<StructIndex,Record>,
    pub(super) enum_defs : IndexVec<EnumIndex,(Ident,IndexVec<VariantIndex,Record>,FxHashMap<SymbolIndex,VariantIndex>)>,
    pub(super) functions : IndexVec<FuncIndex,Ident>,
    pub(super) generics : FxHashMap<GenericOwner,IndexVec<GenericParamIndex,Ident>>,
    pub(super) items : IndexMap<NodeId,Item>,
}
pub struct ItemsToLower<'a>{
    pub(super) impls : IndexVec<ImplIndex,&'a ast::Impl>,
    pub(super) items : IndexMap<NodeId,Item>,

}
pub struct NameFinder<'a,'b>{
    info : NamesFound,
    items_to_lower : ItemsToLower<'a>,
    current_scope : ScopeIndex,
    interner:&'b mut SymbolInterner,
    next_local_variable:usize,
    prev_last_local_variables:Vec<usize>,
    had_error : Cell<bool>
}
impl<'a,'b> NameFinder<'a,'b>{
    pub fn new(interner:&'b mut SymbolInterner)->Self{
        let mut scopes = IndexVec::new();
        let global_scope = scopes.push(Scope::new_global_scope());
        Self { 
            next_local_variable:0,
            items_to_lower:ItemsToLower{
                impls: IndexVec::new(), 
                items: IndexMap::new(), 
            },
            info : NamesFound{
                variables:IndexVec::new(),
                all_scopes: scopes ,
                scope_map:FxHashMap::default(),
                variable_def_map:FxHashMap::default(),
                variable_defs:FxHashMap::default(),
                items: IndexMap::new(), 
                structs: IndexVec::default(), 
                enum_defs: IndexVec::default(), 
                functions: IndexVec::new(), 
                generics : FxHashMap::default()

            },
            current_scope:global_scope , 
            interner,
            prev_last_local_variables:Vec::new(),
            had_error:false.into()
        }
    }
    fn error(&self,message:String,span:SourceLocation){
        self.had_error.set(true);
        eprintln!("Error on line {}: {}",span.start_line,message);
    }
    fn define_bindings(&mut self,base_pattern_id:NodeId,bindings:&BTreeMap<NodeId,Ident>,seen_symbols:&BTreeMap<SymbolIndex,NodeId>){
        let mut all_variables = Vec::new();
        for (node,&ident) in bindings{
            if seen_symbols.get(&ident.index).is_some_and(|node_id| node_id != node){
                self.error(format!("Repeated binding '{}'.",self.interner.get(ident.index)),ident.span);
                continue;
            }
            let index = self.info.variables.push((self.current_scope,self.next_local_variable,ident));
            all_variables.push(index);
            self.info.variable_defs.insert(*node, index);
            self.next_local_variable+=1;
        }
        self.info.variable_def_map.insert(base_pattern_id, all_variables);

    }
    fn get_current_scope_mut(&mut self)->&mut Scope{
        &mut self.info.all_scopes[self.current_scope]
    }
    fn begin_scope(&mut self,id:NodeId,kind:ScopeKind){
        self.current_scope = self.info.all_scopes.push(Scope::new_with_prev_scope(self.current_scope,kind));
        self.info.scope_map.insert(id, self.current_scope);
    }
    fn end_scope(&mut self){
        self.current_scope = self.info.all_scopes[self.current_scope].prev_scope.expect("Any popped scopes must have prev scope");
    }
    fn find_names_in_stmts(&mut self,stmts:&'a [ast::StmtNode]){
        for stmt in stmts{
            self.find_names_in_stmt(stmt);
        }
    }
    fn find_names_in_expr(&mut self,expr:&'a ast::ExprNode){
        let id = expr.id;
        match &expr.kind {
            ast::ExprNodeKind::Array(elements) | ast::ExprNodeKind::Print(elements) | ast::ExprNodeKind::Tuple(elements) => elements.iter().for_each(|element|{
                self.find_names_in_expr(element);
            }), 
            ast::ExprNodeKind::BinaryOp { op:_, left, right } | 
            ast::ExprNodeKind::Logical { op:_, left, right } | 
            ast::ExprNodeKind::Index { lhs:left, rhs:right }|
            ast::ExprNodeKind::While { condition:left, body:right } => {
                self.find_names_in_expr(left);
                self.find_names_in_expr(right);
            },
            ast::ExprNodeKind::Unary { op:_, operand:expr } | ast::ExprNodeKind::Grouping(expr) | ast::ExprNodeKind::Property(expr,_ ) => self.find_names_in_expr(expr),
            ast::ExprNodeKind::Call { callee:first, args } | ast::ExprNodeKind::MethodCall { receiver:first, method:_, args } =>{
                self.find_names_in_expr(first);
                 args.iter().for_each(|arg|{
                    self.find_names_in_expr(arg);
                })
            },
            ast::ExprNodeKind::If { condition, then_branch, else_branch }=>{
                self.find_names_in_expr(condition);
                self.find_names_in_expr(then_branch);
                if let Some(else_branch) = else_branch.as_ref(){
                    self.find_names_in_expr(else_branch);
                }
            },
            ast::ExprNodeKind::Return(expr) => if let Some(expr) = expr { self.find_names_in_expr(expr);},
            ast::ExprNodeKind::Match { matchee, arms } => {
                self.find_names_in_expr(matchee);
                for arm in arms{
                    self.begin_scope(arm.id,ScopeKind::Normal);
                    let mut bindings = BTreeMap::new();
                    let mut seen_symbols = BTreeMap::new();
                    self.find_names_in_pattern(&arm.pattern,&mut bindings, &mut seen_symbols);
                    self.define_bindings(arm.pattern.id,&bindings, &seen_symbols);
                    self.find_names_in_expr(&arm.expr);
                    self.end_scope();
                }
            },
            ast::ExprNodeKind::Block { stmts, expr } => {
                self.begin_scope(id,ScopeKind::Normal);
                self.find_names_in_stmts(&stmts);
                if let Some(expr) = expr{
                    self.find_names_in_expr(expr);
                }
                self.end_scope();
            },
            ast::ExprNodeKind::Assign { lhs, rhs } => {
                match &lhs.kind{
                    ParsedAssignmentTargetKind::Field { lhs, field:_ } => self.find_names_in_expr(lhs),
                    ParsedAssignmentTargetKind::Index { lhs, rhs } => {
                        self.find_names_in_expr(lhs);
                        self.find_names_in_expr(rhs);
                    },
                    ParsedAssignmentTargetKind::Name(_) => ()
                }
                self.find_names_in_expr(rhs);
            },
            ast::ExprNodeKind::Function(function) => {
                self.find_names_in_function(id,function);
            }
            ast::ExprNodeKind::StructInit { path:_, fields } => fields.iter().for_each(|(_,expr)| self.find_names_in_expr(expr)),
            //Ignore any expressions that can't introduce new names or that make use of names
            ast::ExprNodeKind::Literal(_) | ast::ExprNodeKind::TypenameOf(_) | ast::ExprNodeKind::Get(_) | ast::ExprNodeKind::GetPath(_) => ()
        }
    }
    fn find_names_in_pattern(&mut self,pattern:&'a ast::ParsedPatternNode,bindings:&mut BTreeMap<NodeId,Ident>,seen_symbols:&mut BTreeMap<SymbolIndex,NodeId>,){
        let id = pattern.id;
        match &pattern.kind{
            ast::ParsedPatternNodeKind::Name(name) => {
                let index = self.interner.intern(name.clone());
                bindings.insert(id,Ident { index, span:pattern.location });
                seen_symbols.entry(index).or_insert(pattern.id);
            },
            ast::ParsedPatternNodeKind::Is(name, pattern) => {
                let ident = self.interner.intern_symbol(name.clone());
                bindings.insert(id,ident);
                seen_symbols.entry(ident.index).or_insert(pattern.id);
                self.find_names_in_pattern(pattern, bindings,seen_symbols);
            },
            ast::ParsedPatternNodeKind::Struct { path:_, fields } => {
                fields.iter().for_each(|(_,pattern)|{
                    self.find_names_in_pattern(pattern, bindings,seen_symbols);
                });
            },
            ast::ParsedPatternNodeKind::Tuple(elements) => elements.iter().for_each(|element|{
                self.find_names_in_pattern(element, bindings,seen_symbols);
            }),
            ast::ParsedPatternNodeKind::Wildcard | ast::ParsedPatternNodeKind::Literal(_) => ()
        }
    }
    fn find_generic_params(&mut self,owner:GenericOwner,generic_params:Option<&'a ast::ParsedGenericParams>){
        let mut seen_generic_params = FxHashSet::default();
        let generic_params = if let Some(generic_params) = generic_params { 
            generic_params.0.iter().filter_map(|param| {
                let index = self.interner.intern(param.0.clone().content);
                if !seen_generic_params.insert(index){
                    self.error(format!("Repeated generic param '{}'.",self.interner.get(index)), param.0.location);
                    None
                }
                else{
                    Some(Ident { index, span:param.0.location })
                }
            }).collect() 
        }
        else {
            IndexVec::new()
        };
        self.info.generics.insert(owner,generic_params);
    }
    fn find_names_in_function(&mut self,id:NodeId,function:&'a ast::ParsedFunction){
        self.begin_scope(id,ScopeKind::Function);
        self.prev_last_local_variables.push(std::mem::replace(&mut self.next_local_variable,0));
        let mut bindings = BTreeMap::new();
        let mut seen_symbols = BTreeMap::new();
        for param in &function.params{
            self.find_names_in_pattern(&param.pattern, &mut bindings,&mut seen_symbols);
            self.define_bindings(param.pattern.id,&bindings, &seen_symbols);
            bindings.clear();
        }
        self.find_names_in_expr(&function.body);
        self.next_local_variable = self.prev_last_local_variables.pop().expect("Any popped scopes must have prev scope");
        self.end_scope();
    }
    fn find_fields(&mut self,fields:&[(ast::Symbol,ast::ParsedType)]) -> IndexVec<FieldIndex,Ident>{
        fields.iter().map(|(field,_)|{
            let field = self.interner.intern_symbol(field.clone());
            field
        }).collect()
    }
    fn find_names_in_stmt(&mut self,stmt:&'a ast::StmtNode){
        match stmt {
            ast::StmtNode::Enum(enum_def) => {
                let name = self.interner.intern_symbol(enum_def.name.clone());
                let mut seen_variants = FxHashMap::default();
                let variants = {
                    enum_def.variants.iter().enumerate().filter_map(|(i,variant)|{
                        let name = self.interner.intern_symbol(variant.name.clone());
                        let fields = self.find_fields(&variant.fields);
                        if let Some(old_variant) = seen_variants.insert(name.index,VariantIndex::new(i as u32)){
                            self.error(format!("Repeated variant '{}'.",variant.name.content), name.span);
                            seen_variants.insert(name.index, old_variant);
                            return None;
                        }
                        Some(Record{
                            name,
                            fields
                        })
                    }).collect()
                };
                let enum_index = self.info.enum_defs.push((name,variants,seen_variants));
                self.info.items.insert(enum_def.id, Item::Enum(enum_index));
                self.find_generic_params(GenericOwner::Enum(enum_index), enum_def.generic_params.as_ref());
                let index = self.interner.intern(enum_def.name.content.clone());
                if !self.get_current_scope_mut().define_type(index,Type::Enum(enum_index)){
                    self.error(format!("Repeated type '{}'.",enum_def.name.content), enum_def.name.location);
                }
            },
            ast::StmtNode::Struct(struct_def) => {
                let name = self.interner.intern_symbol(struct_def.name.clone());
                let fields = self.find_fields(&struct_def.fields);
                let struct_index = self.info.structs.push(Record { name, fields});
                self.info.items.insert(struct_def.id, Item::Struct(struct_index));
                let index = self.interner.intern(struct_def.name.content.clone());
                self.find_generic_params(GenericOwner::Struct(struct_index), struct_def.generic_params.as_ref());
                if !self.get_current_scope_mut().define_type(index,Type::Struct(struct_index)){
                    self.error(format!("Repeated type '{}'.",struct_def.name.content), struct_def.name.location);
                }

            },
            ast::StmtNode::Expr { expr, has_semi:_ } => {
                self.find_names_in_expr(&expr);
            },
            ast::StmtNode::Let { id:_, pattern, expr, ty:_ } => {
                let mut bindings = BTreeMap::new();
                let mut seen_symbols = BTreeMap::new();
                self.find_names_in_pattern(pattern, &mut bindings,&mut seen_symbols);
                self.define_bindings(pattern.id,&bindings, &seen_symbols);
                self.find_names_in_expr(expr);
            },
            ast::StmtNode::Fun(function_def) => {
                let index = self.info.functions.push(self.interner.intern_symbol(function_def.name.clone()));
                self.info.items.insert(function_def.id, Item::Function(index));
                self.find_generic_params(GenericOwner::Function(index),function_def.generic_params.as_ref());
                self.find_names_in_function(function_def.id,&function_def.function);
                let symbol = self.interner.intern(function_def.name.content.clone());
                if !self.get_current_scope_mut().define_function(symbol,index){
                    self.error(format!("Repeated function '{}'.",function_def.name.content), function_def.name.location);
                }
            },
            ast::StmtNode::Impl(impl_) => {
                let index = self.items_to_lower.impls.push(impl_);
                self.items_to_lower.items.insert(impl_.id, Item::Impl(index));
                for method in &impl_.methods{
                    self.find_names_in_function(method.id,&method.function);
                }
            }
        }
    }
    pub fn find_names(mut self,stmts:&'a [ast::StmtNode]) -> Result<(NamesFound,ItemsToLower<'a>),ResolutionError>{
        self.find_names_in_stmts(stmts);
        if self.had_error.get(){
            return Err(ResolutionError);
        }
        Ok((self.info,self.items_to_lower))
    }
}
#[derive(Debug,Clone)]
pub enum Item {
    Function(FuncIndex),
    Variant(EnumIndex,VariantIndex),
    Enum(EnumIndex),
    Struct(StructIndex),
    Impl(ImplIndex)
}
