use crate::identifiers::SymbolIndex;
use super::{ hir::Resolution, scope::{NameSpaces, Scope}};

pub struct Resolver{
    scopes : Vec<Scope>,
    name_spaces : NameSpaces,

}
impl Resolver{
    pub fn new(name_spaces:NameSpaces) -> Self{
        Self { scopes:vec![], name_spaces}
    }
    pub fn push_scope(&mut self,scope:Scope){
        self.scopes.push(scope);
    }
    pub fn current_scope(&self) -> &Scope{
        self.scopes.last().expect("Should be a scope")
    }
    pub fn current_scope_mut(&mut self) -> &mut Scope{
        self.scopes.last_mut().expect("Should be a scope")
    }
    pub fn pop_scope(&mut self){
        self.scopes.pop();
    }
    pub fn resolve_path(&self,path:impl Iterator<Item = SymbolIndex>) -> Vec<Resolution>{
        let mut path_iter = path;
        let mut prev_res: Option<Resolution> = None;
        let mut segments = Vec::new();
        while let Some(name) = path_iter.next() {
                if let Some(res) = prev_res{
                    if let Some(res) = self.name_spaces.get_namespace(res).and_then(|scope| scope.get_binding(name)){
                        segments.push(res);
                        prev_res = Some(res);
                    }
                    else{
                        break;
                    }
                } 
                else if let Some(res) = self.scopes.iter().rev().filter_map(|scope| scope.get_binding(name)).next(){
                    segments.push(res);
                    prev_res = Some(res);
                }
                else{
                    break;
                } 
            
        }
        segments

    }
}

#[cfg(test)]
mod test{
    use crate::{frontend::ast_lowering::{hir::{DefId, DefIdProvider, DefKind, Resolution}, scope::{NameSpaces, Scope, ScopeKind}, SymbolInterner}, identifiers::SymbolIndex};

    use super::Resolver;

    fn init<const N:usize,const ID_COUNT:usize>(names_to_intern:[&str;N]) -> (SymbolInterner,[DefId;ID_COUNT],[SymbolIndex;N]){
        let mut ids = DefIdProvider::new();
        let mut interner = SymbolInterner::new();
        let ids = std::array::from_fn(|_| ids.next());
        let names = std::array::from_fn(|index| interner.intern(names_to_intern[index].to_string()));
        (interner,ids,names)
    }
    #[test]
    fn test_resolve(){
        /*
        {
            enum A{
                B
            }
            A::B
        }
         */
        let (_,[enum_a_id,variant_b_id],[a_index,b_index]) = init(["A","B"]);
        let mut namespaces = NameSpaces::new();
        let mut enum_a_scope = Scope::new(ScopeKind::Type);
        enum_a_scope.add_binding(b_index, Resolution::Definition(DefKind::Variant, variant_b_id));
        namespaces.define_namespace(Resolution::Definition(DefKind::Enum, enum_a_id), enum_a_scope);
        let resolver = {
            let mut resolver = Resolver::new(namespaces );
            resolver.push_scope({
                let mut scope = Scope::new(ScopeKind::Normal);
                scope.add_binding(a_index, Resolution::Definition(DefKind::Enum, enum_a_id));
                scope
            });
            resolver
        };
        let resolutions = resolver.resolve_path(vec![a_index,b_index].into_iter());
        assert_eq!(resolutions,vec![Resolution::Definition(DefKind::Enum, enum_a_id),Resolution::Definition(DefKind::Variant, variant_b_id)]);
    }
    #[test]
    fn test_functions(){
        /*

            fun f(){
                g();
            }
            fun g(){
                f();
            }
         */

        let (_,[func_f_id,func_g_id],[f_index,g_index]) = init(["f","g"]);
        let name_spaces = NameSpaces::new();
        let mut scope = Scope::new(ScopeKind::Normal);
        scope.add_binding(f_index, Resolution::Definition(DefKind::Function, func_f_id));
        scope.add_binding(g_index, Resolution::Definition(DefKind::Function, func_g_id));

        let mut resolver = Resolver::new(name_spaces);
        resolver.push_scope(scope);
        resolver.push_scope(Scope::new(ScopeKind::Function));
        assert_eq!(resolver.resolve_path(vec![g_index].into_iter()),vec![Resolution::Definition(DefKind::Function,func_g_id)]);
        resolver.pop_scope();

        resolver.push_scope(Scope::new(ScopeKind::Function));
        assert_eq!(resolver.resolve_path(vec![f_index].into_iter()),vec![Resolution::Definition(DefKind::Function,func_f_id)]);
        resolver.pop_scope();

    }
}