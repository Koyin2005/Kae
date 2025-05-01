use std::{cell::Cell, collections::BTreeMap};

use fxhash::{FxHashMap, FxHashSet};
use crate::{
    data_structures::IndexVec, 
    frontend::{ast_lowering::{hir::Ident, SymbolIndex, SymbolInterner}, 
    parsing::ast::{self, NodeId, ParsedAssignmentTargetKind}, tokenizing::SourceLocation, }, 
    identifiers::VariableIndex, GlobalSymbols
};

use super::{hir::{BuiltinKind, DefId, DefIdMap, DefIdProvider, DefKind, PrimitiveType, Resolution}, scope::{NameSpaces, Scope, ScopeKind}};

pub struct Record{
    pub name : Ident,
    pub fields : Vec<Ident>
}
pub type NodeMap<T> = FxHashMap<NodeId,T>;
pub struct NamesFound{
    pub(super) variables : IndexVec<VariableIndex,(usize,Ident)>,
    pub(super) variable_defs: FxHashMap<NodeId,VariableIndex>,
    pub(super) scope_map : FxHashMap<NodeId,Option<Scope>>,
    pub(super) variable_def_map : FxHashMap<NodeId,Vec<VariableIndex>>,
    pub(super) structs : DefIdMap<Record>,
    pub(super) enum_defs : DefIdMap<(Ident,Vec<(DefId,Record)>)>,
    pub(super) generics : DefIdMap<Vec<(DefId,Ident)>>,
    pub(super) node_to_def_map : NodeMap<DefId>,
    pub(super) name_map : DefIdMap<Ident>,
}
impl NamesFound{
    pub fn expect_def_id_with_message(&self,node:NodeId,msg:&str) -> DefId{
        self.node_to_def_map.get(&node).copied().expect(msg)
    }
}
pub struct NameScopes{
    pub(super) namespaces : NameSpaces,
    pub(super) base_scope : Scope
}
pub struct NameFinder<'b>{
    info : NamesFound,
    scopes : Vec<Scope>,
    interner:&'b mut SymbolInterner,
    next_local_variable:usize,
    prev_last_local_variables:Vec<usize>,
    def_ids : &'b mut DefIdProvider,
    had_error : Cell<bool>,
    namespaces : NameSpaces,
    global_symbols : &'b GlobalSymbols
}
impl<'b,'a> NameFinder<'b>{
    pub fn new(interner:&'b mut SymbolInterner,def_id_provider:&'b mut DefIdProvider,symbols:&'b GlobalSymbols)->Self{
        let mut scopes = Vec::new();
        scopes.push(Scope::new(ScopeKind::Normal));
        Self { 
            next_local_variable:0,
            info : NamesFound{
                name_map:DefIdMap::new(),
                variables:IndexVec::new(),
                scope_map:FxHashMap::default(),
                variable_def_map:FxHashMap::default(),
                variable_defs:FxHashMap::default(),
                node_to_def_map: NodeMap::default(), 
                structs: DefIdMap::new(), 
                enum_defs: DefIdMap::new(),
                generics : DefIdMap::new(),

            },
            global_symbols:symbols,
            namespaces : NameSpaces::new(),
            scopes,
            interner,
            prev_last_local_variables:Vec::new(),
            had_error:false.into(),
            def_ids:def_id_provider
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
            let index = self.info.variables.push((self.next_local_variable,ident));
            all_variables.push(index);
            self.info.variable_defs.insert(*node, index);
            self.next_local_variable+=1;
        }
        self.info.variable_def_map.insert(base_pattern_id, all_variables);

    }
    fn get_current_scope_mut(&mut self)->&mut Scope{
        self.scopes.last_mut().expect("Should be at least 1 scope")
    }
    fn begin_scope(&mut self,kind:ScopeKind){
        self.scopes.push(Scope::new(kind));
    }
    fn pop_scope(&mut self) ->Scope{
        self.scopes.pop().expect("There should be at least one scope")
    }
    fn end_scope(&mut self,id:NodeId){
        let scope = self.pop_scope();
        self.info.scope_map.insert(id,Some(scope));
    }
    fn add_node_to_def(&mut self,id:NodeId,def_id:DefId){
        self.info.node_to_def_map.insert(id, def_id);
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
                    self.begin_scope(ScopeKind::Normal);
                    let mut bindings = BTreeMap::new();
                    let mut seen_symbols = BTreeMap::new();
                    self.find_names_in_pattern(&arm.pattern,&mut bindings, &mut seen_symbols);
                    self.define_bindings(arm.pattern.id,&bindings, &seen_symbols);
                    self.find_names_in_expr(&arm.expr);
                    self.end_scope(arm.id);
                }
            },
            ast::ExprNodeKind::Block { stmts, expr } => {
                self.begin_scope(ScopeKind::Normal);
                self.find_names_in_stmts(&stmts);
                if let Some(expr) = expr{
                    self.find_names_in_expr(expr);
                }
                self.end_scope(id);
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
            ast::ExprNodeKind::Literal(_) | ast::ExprNodeKind::TypenameOf(_) | ast::ExprNodeKind::GetPath(_) => ()
        }
    }
    fn find_names_in_pattern(&mut self,pattern:&'a ast::ParsedPatternNode,bindings:&mut BTreeMap<NodeId,Ident>,seen_symbols:&mut BTreeMap<SymbolIndex,NodeId>,){
        let id = pattern.id;
        match &pattern.kind{
            &ast::ParsedPatternNodeKind::Name(name) => {
                bindings.insert(id,Ident { index:name, span:pattern.location });
                seen_symbols.entry(name).or_insert(pattern.id);
            },
            &ast::ParsedPatternNodeKind::Is(name, ref pattern) => {
                let ident = name.into();
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
            ast::ParsedPatternNodeKind::Wildcard | ast::ParsedPatternNodeKind::Literal(_) | ast::ParsedPatternNodeKind::Path(_) => ()
        }
    }
    fn find_generic_params(&mut self,owner:DefId,generic_params:Option<&'a ast::ParsedGenericParams>)->Option<NodeId>{
        let mut seen_generic_params = FxHashSet::default();
        let (generic_params,id) = if let Some(generic_params) = generic_params { 
            self.begin_scope(ScopeKind::Type);
            let params = generic_params.1.iter().filter_map(|param| {
                let index = param.0.content;
                if !seen_generic_params.insert(index){
                    self.error(format!("Repeated generic param '{}'.",self.interner.get(index)), param.0.location);
                }
                let id = self.def_ids.next();
                self.get_current_scope_mut().add_binding(index,Resolution::Definition(DefKind::Param,id));
                Some((id,Ident { index, span:param.0.location }))
                
            }).collect();
            (params,Some(generic_params.0))
        }
        else {
            (Vec::new(),None)
        };
        self.info.generics.insert(owner,generic_params);
        id
    }
    fn find_names_in_function(&mut self,id:NodeId,function:&'a ast::ParsedFunction){
        self.begin_scope(ScopeKind::Function);
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
        self.end_scope(id);
    }
    fn find_fields(&mut self,fields:&[(ast::Symbol,ast::ParsedType)]) -> Vec<Ident>{
        fields.iter().map(|&(field,_)|{
            let field = field.into();
            field
        }).collect()
    }
    fn find_names_in_stmt(&mut self,stmt:&'a ast::StmtNode){
        match stmt {
            ast::StmtNode::Enum(enum_def) => {
                let enum_def_id = self.def_ids.next();
                let name = enum_def.name.into();
                self.info.node_to_def_map.insert(enum_def.id, enum_def_id);
                self.info.name_map.insert(enum_def_id, name);
                let generics_id = self.find_generic_params(enum_def_id, enum_def.generic_params.as_ref());
                self.begin_scope(ScopeKind::Type);
                let variants = 
                    enum_def.variants.iter().map(|variant|{
                        let id = self.def_ids.next();
                        let name = variant.name.into();
                        let fields = self.find_fields(&variant.fields);
                        self.info.name_map.insert(id, name);
                        if !self.get_current_scope_mut().add_binding(name.index, Resolution::Definition(DefKind::Variant, id)).is_none(){
                            self.error(format!("Repeated variant '{}'.",self.interner.get(variant.name.content)), name.span);
                        }
                        (id,Record{
                            name,
                            fields
                        })
                    }).collect();
                self.info.enum_defs.insert(enum_def_id,(name,variants));
                let name_scope = self.pop_scope();
                if let Some(id) = generics_id{
                    self.end_scope(id);
                }
                self.namespaces.define_namespace(Resolution::Definition(DefKind::Enum, enum_def_id),name_scope);
                let index = enum_def.name.content;
                if !self.get_current_scope_mut().add_binding(index,Resolution::Definition(DefKind::Enum, enum_def_id)).is_none(){
                    self.error(format!("Repeated item '{}'.",self.interner.get(enum_def.name.content)), enum_def.name.location);
                }
            },
            ast::StmtNode::Struct(struct_def) => {
                let struct_def_id = self.def_ids.next();
                let name = struct_def.name.into();
                let generics_id = self.find_generic_params(struct_def_id, struct_def.generic_params.as_ref());
                let fields = self.find_fields(&struct_def.fields);
                if let Some(id) = generics_id{
                    self.end_scope(id);
                }
                self.info.structs.insert(struct_def_id,Record { name, fields});
                self.add_node_to_def(struct_def.id, struct_def_id);
                self.info.name_map.insert(struct_def_id, name);
                let index = struct_def.name.content;
                if !self.get_current_scope_mut().add_binding(index,Resolution::Definition(DefKind::Struct, struct_def_id)).is_none(){
                    self.error(format!("Repeated item '{}'.",self.interner.get(struct_def.name.content)), struct_def.name.location);
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
                let func_def_id = self.def_ids.next();
                self.add_node_to_def(function_def.id, func_def_id);
                self.info.name_map.insert(func_def_id, function_def.name.into());
                let generics_id = self.find_generic_params(func_def_id,function_def.generic_params.as_ref());
                self.find_names_in_function(function_def.id,&function_def.function);
                if let Some(id) = generics_id{
                    self.end_scope(id);
                }
                let symbol = function_def.name.content;
                if !self.get_current_scope_mut().add_binding(symbol,Resolution::Definition(DefKind::Function,func_def_id)).is_none(){
                    self.error(format!("Repeated item '{}'.",self.interner.get(function_def.name.content)), function_def.name.location);
                }
            },
            ast::StmtNode::Impl(impl_) => {
                let impl_id = self.def_ids.next();
                self.add_node_to_def(impl_.id,impl_id);
                self.begin_scope(ScopeKind::Type);
                let self_symbol = self.global_symbols.upper_self_symbol();
                self.get_current_scope_mut().add_binding(self_symbol,Resolution::SelfType);
                for method in &impl_.methods{
                    let function = &method.function;
                    let method_id = self.def_ids.next();
                    self.add_node_to_def(method.id, method_id);
                    self.info.name_map.insert(method_id, method.name.into());
                    let generics_id = self.find_generic_params(method_id,method.generic_params.as_ref());
                    self.find_names_in_function(method.id,&function);
                    if let Some(id) = generics_id{
                        self.end_scope(id);
                    }
                }
                self.end_scope(impl_.id);
            }
        }
    }
    pub fn find_names(mut self,stmts:&'a [ast::StmtNode]) -> Result<(NamesFound,NameScopes),()>{
        {
            let int_symbol = self.interner.intern("int".to_string());
            let float_symbol = self.interner.intern("float".to_string());
            let bool_symbol = self.interner.intern("bool".to_string());
            let never_symbol = self.interner.intern("never".to_string());
            let string_symbol = self.interner.intern("string".to_string());
            let panic_symbol = self.interner.intern("panic".to_string());
            let root_scope = self.get_current_scope_mut();
            root_scope.add_binding(int_symbol, Resolution::Primitive(PrimitiveType::Int));
            root_scope.add_binding(float_symbol, Resolution::Primitive(PrimitiveType::Float));
            root_scope.add_binding(bool_symbol, Resolution::Primitive(PrimitiveType::Bool));
            root_scope.add_binding(never_symbol, Resolution::Primitive(PrimitiveType::Never));
            root_scope.add_binding(string_symbol, Resolution::Primitive(PrimitiveType::String));
            root_scope.add_binding(panic_symbol, Resolution::Builtin(BuiltinKind::Panic));
        }
        self.find_names_in_stmts(stmts);
        if self.had_error.get(){
            return Err(());
        }
        let root_scope = self.pop_scope();
        Ok((self.info,NameScopes{
            base_scope:root_scope,
            namespaces:self.namespaces,
        }))
    }
}
#[derive(Debug,Clone)]
pub enum Item {
    Function(DefId),
    Variant(DefId),
    Enum(DefId),
    Struct(DefId),
    Impl(DefId),
    Method(DefId)
}
