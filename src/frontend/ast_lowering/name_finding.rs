use std::{cell::Cell, collections::BTreeMap};

use fxhash::{FxHashMap, FxHashSet};
use crate::{
    data_structures::IndexVec, errors::ErrorReporter, frontend::{ast_lowering::{hir::Ident, SymbolIndex, SymbolInterner}, 
    parsing::ast::{self, ExprNode, FunctionSig, Impl, NodeId}, tokenizing::SourceLocation, }, identifiers::VariableIndex, GlobalSymbols
};

use super::{hir::{BuiltinKind, DefId, DefIdMap, DefIdProvider, DefKind, PrimitiveType, Resolution},scope::{NameSpaces, Scope, ScopeId, ScopeKind, ScopeTree}};

pub struct Record{
    pub name : Ident,
    pub fields : Vec<Ident>
}
pub type NodeMap<T> = FxHashMap<NodeId,T>;

pub struct NamesFound{
    pub(super) variables : IndexVec<VariableIndex,(usize,Ident)>,
    pub(super) variable_defs: FxHashMap<NodeId,VariableIndex>,
    pub(super) scope_map : FxHashMap<NodeId,Vec<ScopeId>>,
    pub(super) variable_def_map : FxHashMap<NodeId,Vec<VariableIndex>>,
    pub(super) structs : DefIdMap<Record>,
    pub(super) enum_defs : DefIdMap<(Ident,Vec<(DefId,Record)>)>,
    pub(super) generics : DefIdMap<Vec<(DefId,Ident)>>,
    pub(super) node_to_def_map : NodeMap<DefId>,
    pub(super) name_map : DefIdMap<Ident>,
}
impl NamesFound{
    pub fn expect_base_scope_for(&self, node: NodeId) -> ScopeId{
        self.scope_map.get(&node).expect("Expected scopes for node id ").last().copied().expect("Expect base scope")
    }
    pub fn expect_def_id_with_message(&self,node:NodeId,msg:&str) -> DefId{
        self.node_to_def_map.get(&node).copied().expect(msg)
    }
}
pub struct NameScopes{
    pub(super) namespaces : NameSpaces,
    pub(super) scope_tree : ScopeTree
}
pub struct NameFinder<'b>{
    info : NamesFound,
    interner:&'b mut SymbolInterner,
    next_local_variable:usize,
    prev_last_local_variables:Vec<usize>,
    def_ids : &'b mut DefIdProvider,
    namespaces : NameSpaces,
    current_scope : ScopeId,
    global_symbols : &'b GlobalSymbols,
    pub(super) impl_map : Vec<(&'b Impl,Vec<DefId>)>,
    error_reporter : ErrorReporter,
    scope_tree : ScopeTree
}
impl<'b,'a:'b> NameFinder<'b>{
    pub fn new(interner:&'b mut SymbolInterner,def_id_provider:&'b mut DefIdProvider,symbols:&'b GlobalSymbols)->Self{
        let global_scope = {
            let int_symbol = interner.intern("int".to_string());
            let float_symbol = interner.intern("float".to_string());
            let bool_symbol = interner.intern("bool".to_string());
            let never_symbol = interner.intern("never".to_string());
            let string_symbol = interner.intern("string".to_string());
            let panic_symbol = interner.intern("panic".to_string());
            let mut root_scope = Scope::new(ScopeKind::Normal);
            root_scope.add_binding(int_symbol, Resolution::Primitive(PrimitiveType::Int));
            root_scope.add_binding(float_symbol, Resolution::Primitive(PrimitiveType::Float));
            root_scope.add_binding(bool_symbol, Resolution::Primitive(PrimitiveType::Bool));
            root_scope.add_binding(never_symbol, Resolution::Primitive(PrimitiveType::Never));
            root_scope.add_binding(string_symbol, Resolution::Primitive(PrimitiveType::String));
            root_scope.add_binding(panic_symbol, Resolution::Builtin(BuiltinKind::Panic));
            root_scope
        };
        Self { 
            error_reporter:ErrorReporter::new(true),
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
            
                impl_map : Vec::new(),
            scope_tree : ScopeTree::new(global_scope),
            current_scope : ScopeId::GLOBAL_SCOPE,
            global_symbols:symbols,
            namespaces : NameSpaces::new(),
            interner,
            prev_last_local_variables:Vec::new(),
            def_ids:def_id_provider
        }
    }
    fn error(&self,message:String,span:SourceLocation){
        self.error_reporter.emit(message, span);
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
        self.scope_tree.get_scope_mut(self.current_scope)
    }
    fn begin_scope(&mut self,kind:ScopeKind){
        let (_,new_scope) = self.scope_tree.add_scope(Scope::new(kind),self.current_scope);
        self.current_scope = new_scope;
    }
    fn pop_scope(&mut self) ->ScopeId{
        let Some(parent) = self.scope_tree.get_parent(self.current_scope) else {
            unreachable!("Cannot pop a scope if there is only global scope left")
        };
        let old_scope = self.current_scope;
        self.current_scope = parent;
        old_scope
    }
    fn end_scope(&mut self,id:NodeId){
        let scope = self.pop_scope();
        self.info.scope_map.entry(id).or_insert(Vec::new()).push(scope);
    }
    fn add_node_to_def(&mut self,id:NodeId,def_id:DefId){
        self.info.node_to_def_map.insert(id, def_id);
    }
    fn find_names_in_stmts(&mut self,stmts:&'a [ast::StmtNode]){
        for stmt in stmts{
            self.find_names_in_stmt(stmt);
        }
    }
    fn find_names_in_expr(&mut self,expr:&'b ast::ExprNode){
        let id = expr.id;
        match &expr.kind {
            ast::ExprNodeKind::Array(elements) | ast::ExprNodeKind::Print(elements) | ast::ExprNodeKind::Tuple(elements) => elements.iter().for_each(|element|{
                self.find_names_in_expr(element);
            }), 
            ast::ExprNodeKind::BinaryOp { op:_, left, right } | 
            ast::ExprNodeKind::Logical { op:_, left, right } | 
            ast::ExprNodeKind::While { condition:left, body:right } | 
            ast::ExprNodeKind::Index { lhs:left, rhs:right } => {
                self.find_names_in_expr(left);
                self.find_names_in_expr(right);
            },
            ast::ExprNodeKind::Unary { op:_, operand:expr } | ast::ExprNodeKind::Grouping(expr) | ast::ExprNodeKind::Property(expr,_ ) | ast::ExprNodeKind::Instantiate { lhs:expr, args:_ } => 
                self.find_names_in_expr(expr),
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
                self.find_names_in_expr(lhs);
                self.find_names_in_expr(rhs);
            },
            ast::ExprNodeKind::Function(sig,body) => {
                self.find_names_in_function(id,sig,Some(body));
            }
            ast::ExprNodeKind::StructInit { path:_, fields } => fields.iter().for_each(|(_,expr)| self.find_names_in_expr(expr)),
            //Ignore any expressions that can't introduce new names or that make use of names
            ast::ExprNodeKind::Literal(_) | ast::ExprNodeKind::TypenameOf(_) | ast::ExprNodeKind::GetPath(_) => ()
        }
    }
    fn find_names_in_pattern(&mut self,pattern:&'a ast::ParsedPatternNode,bindings:&mut BTreeMap<NodeId,Ident>,seen_symbols:&mut BTreeMap<SymbolIndex,NodeId>){
        let id = pattern.id;
        match &pattern.kind{
            &ast::ParsedPatternNodeKind::Name(name) => {
                bindings.insert(id,Ident { index:name, span:pattern.location });
                seen_symbols.entry(name).or_insert(pattern.id);
            },
            &ast::ParsedPatternNodeKind::Is(name, ref pattern) => {
                let ident = name.into();
                bindings.insert(id,ident);
                seen_symbols.entry(ident.index).or_insert(id);
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
            ast::ParsedPatternNodeKind::Wildcard | ast::ParsedPatternNodeKind::Literal(_) | ast::ParsedPatternNodeKind::Path(_) | ast::ParsedPatternNodeKind::Infer(_) => ()
        }
    }
    fn find_generic_params(&mut self,owner:DefId,generic_params:Option<&'b ast::ParsedGenericParams>){
        let mut seen_generic_params = FxHashSet::default();
        let generic_params = if let Some(generic_params) = generic_params {
            let params = generic_params.1.iter().filter_map(|param| {
                let index = param.0.content;
                if !seen_generic_params.insert(index){
                    self.error(format!("Repeated generic param '{}'.",self.interner.get(index)), param.0.location);
                }
                let id = self.def_ids.next();
                self.get_current_scope_mut().add_binding(index,Resolution::Definition(DefKind::Param,id));
                Some((id,Ident { index, span:param.0.location }))
                
            }).collect();
            params
        }
        else {
            Vec::new()
        };
        self.info.generics.insert(owner,generic_params);
    }
    fn find_names_in_function(&mut self,id:NodeId,sig:&'b FunctionSig,body:Option<&'b ExprNode>){
        self.begin_scope(ScopeKind::Function(id));
        self.prev_last_local_variables.push(std::mem::replace(&mut self.next_local_variable,0));
        let mut bindings = BTreeMap::new();
        let mut seen_symbols = BTreeMap::new();
        for param in &sig.params{
            self.find_names_in_pattern(&param.pattern, &mut bindings,&mut seen_symbols);
            self.define_bindings(param.pattern.id,&bindings, &seen_symbols);
            bindings.clear();
        }
        if let Some(body) = body{
            self.find_names_in_expr(&body);
        }
        self.next_local_variable = self.prev_last_local_variables.pop().expect("Any popped scopes must have prev scope");
        self.end_scope(id);
    }
    fn find_fields(&mut self,fields:&[(ast::Symbol,ast::ParsedType)]) -> Vec<Ident>{
        fields.iter().map(|&(field,_)|{
            let field = field.into();
            field
        }).collect()
    }
    fn find_names_in_method(&mut self, method_id: NodeId, name: ast::Symbol, generic_params:Option<&'b ast::ParsedGenericParams>, sig: &'b FunctionSig, method_body: Option<&'b ExprNode>) -> DefId{
        let method_def_id = self.def_ids.next();
        self.add_node_to_def(method_id, method_def_id);
        self.info.name_map.insert(method_def_id, name.into());
        self.begin_scope(ScopeKind::AssocItem(method_def_id));
        self.find_generic_params(method_def_id,generic_params);
        self.find_names_in_function(method_id,&sig,method_body);
        self.end_scope(method_id);
        method_def_id
    }
    fn find_names_in_item(&mut self,item:&'a ast::Item){
        match item{
            ast::Item::Enum(enum_def) => {
                let enum_def_id = self.def_ids.next();
                let name = enum_def.name.into();
                self.info.node_to_def_map.insert(enum_def.id, enum_def_id);
                self.info.name_map.insert(enum_def_id, name);
                self.begin_scope(ScopeKind::Type(enum_def.id));
                self.find_generic_params(enum_def_id, enum_def.generic_params.as_ref());
                let variants = 
                    enum_def.variants.iter().map(|variant|{
                        let id = self.def_ids.next();
                        let name = variant.name.into();
                        let fields = self.find_fields(&variant.fields);
                        self.info.name_map.insert(id, name);
                        if self.get_current_scope_mut().add_binding(name.index, Resolution::Definition(DefKind::Variant, id)).is_some(){
                            self.error(format!("Repeated variant '{}'.",self.interner.get(variant.name.content)), name.span);
                        }
                        (id,Record{
                            name,
                            fields
                        })
                    }).collect();
                self.info.enum_defs.insert(enum_def_id,(name,variants));
                let name_scope = self.current_scope;
                self.end_scope(enum_def.id);
                self.namespaces.define_namespace(Resolution::Definition(DefKind::Enum, enum_def_id),name_scope);
                let index = enum_def.name.content;
                if self.get_current_scope_mut().add_binding(index,Resolution::Definition(DefKind::Enum, enum_def_id)).is_some(){
                    self.error(format!("Repeated item '{}'.",self.interner.get(enum_def.name.content)), enum_def.name.location);
                }
            },
            ast::Item::Struct(struct_def) => {
                let struct_def_id = self.def_ids.next();
                let name = struct_def.name.into();
                self.begin_scope(ScopeKind::Type(struct_def.id));
                self.find_generic_params(struct_def_id, struct_def.generic_params.as_ref());
                let fields = self.find_fields(&struct_def.fields);
                self.info.structs.insert(struct_def_id,Record { name, fields});
                self.add_node_to_def(struct_def.id, struct_def_id);
                self.info.name_map.insert(struct_def_id, name);
                let index = struct_def.name.content;
                let name_scope = self.current_scope;
                self.end_scope(struct_def.id);
                if !self.get_current_scope_mut().add_binding(index,Resolution::Definition(DefKind::Struct, struct_def_id)).is_none(){
                    self.error(format!("Repeated item '{}'.",self.interner.get(struct_def.name.content)), struct_def.name.location);
                }
                self.namespaces.define_namespace(Resolution::Definition(DefKind::Struct, struct_def_id),name_scope);
            },
            ast::Item::Fun(function_def) => {
                let func_def_id = self.def_ids.next();
                self.add_node_to_def(function_def.id, func_def_id);
                let proto = &function_def.function.proto;
                self.info.name_map.insert(func_def_id, proto.name.into());

                self.begin_scope(ScopeKind::Item(func_def_id));
                self.find_generic_params(func_def_id,proto.generic_params.as_ref());
                self.find_names_in_function(function_def.id,&proto.sig,Some(&function_def.function.body));
                self.end_scope(function_def.id);
                let symbol = proto.name.content;
                if !self.get_current_scope_mut().add_binding(symbol,Resolution::Definition(DefKind::Function,func_def_id)).is_none(){
                    self.error(format!("Repeated item '{}'.",self.interner.get(proto.name.content)), proto.name.location);
                }
            },
            ast::Item::Impl(impl_) => {
                let impl_def_id = self.def_ids.next();
                self.add_node_to_def(impl_.id,impl_def_id);
                self.begin_scope(ScopeKind::Item(impl_def_id));
                self.find_generic_params(impl_def_id,impl_.generic_params.as_ref());
                let self_symbol = self.global_symbols.upper_self_symbol();
                self.get_current_scope_mut().add_binding(self_symbol,Resolution::SelfType);
                let mut methods = Vec::new();
                for method in &impl_.methods{
                    let method_def_id = self.find_names_in_method(method.id,method.function.proto.name,method.function.proto.generic_params.as_ref(),&method.function.proto.sig,Some(&method.function.body));
                    methods.push(method_def_id);
                }
                self.end_scope(impl_.id);
                self.impl_map.push((impl_,methods));
            },
        }
    }
    fn find_names_in_stmt(&mut self,stmt:&'a ast::StmtNode){
        match stmt{
            ast::StmtNode::Let { id:_, pattern, expr, ty:_ } => {
                let mut bindings = BTreeMap::new();
                let mut seen_symbols = BTreeMap::new();
                self.find_names_in_pattern(pattern, &mut bindings,&mut seen_symbols);
                self.define_bindings(pattern.id,&bindings, &seen_symbols);
                self.find_names_in_expr(expr);

            },
            ast::StmtNode::Expr { expr, has_semi:_ } => {
                self.find_names_in_expr(&expr);
            },
            ast::StmtNode::Item(item) => {
                self.find_names_in_item(item);
            },
        }
    }
    pub fn find_names(mut self,items:&'b [ast::Item]) -> Result<(NamesFound,NameScopes),()>{
        for item in items{
            self.find_names_in_item(item);
        }
        if self.error_reporter.error_occurred(){
            return Err(());
        }
        Ok((self.info,NameScopes{
            scope_tree:self.scope_tree,
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
