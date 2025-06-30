use super::{
    hir::Resolution,
    scope::{NameSpaces, Scope, ScopeId, ScopeTree},
};
use crate::identifiers::SymbolIndex;

pub struct Resolver {
    scope_tree: ScopeTree,
    name_spaces: NameSpaces,
    current_scope: ScopeId,
}
impl Resolver {
    pub fn new(name_spaces: NameSpaces, scope_tree: ScopeTree) -> Self {
        Self {
            scope_tree,
            name_spaces,
            current_scope: ScopeId::GLOBAL_SCOPE,
        }
    }
    pub fn namespaces(&mut self) -> &mut NameSpaces {
        &mut self.name_spaces
    }
    pub fn into_namespaces_and_tree(self) -> (NameSpaces, ScopeTree) {
        (self.name_spaces, self.scope_tree)
    }
    pub fn current_scope_id(&self) -> ScopeId {
        self.current_scope
    }
    pub fn scopes(&self) -> &ScopeTree {
        &self.scope_tree
    }
    pub fn set_current_scope(&mut self, new_scope: ScopeId) {
        self.current_scope = new_scope;
    }
    pub fn current_scope(&self) -> &Scope {
        self.scope_tree.get_scope(self.current_scope)
    }
    pub fn current_scope_mut(&mut self) -> &mut Scope {
        self.scope_tree.get_scope_mut(self.current_scope)
    }
    pub fn resolve_path(&self, path: impl Iterator<Item = SymbolIndex>) -> Vec<Resolution> {
        let mut path_iter = path;
        let mut prev_res: Option<Resolution> = None;
        let mut segments = Vec::new();
        while let Some(name) = path_iter.next() {
            if let Some(res) = prev_res {
                if let Some(res) = self
                    .name_spaces
                    .get_namespace(res)
                    .and_then(|&scope| self.scope_tree.resolve_ident(name, scope))
                {
                    segments.push(res);
                    prev_res = Some(res);
                } else {
                    break;
                }
            } else if let Some(res) = self.scope_tree.resolve_ident(name, self.current_scope) {
                segments.push(res);
                prev_res = Some(res);
            } else {
                break;
            }
        }
        segments
    }
}

#[cfg(test)]
mod test {
    use crate::{
        frontend::ast_lowering::{
            SymbolInterner,
            hir::{DefId, DefIdProvider, DefKind, Resolution},
            scope::{NameSpaces, Scope, ScopeId, ScopeKind, ScopeTree},
        },
        identifiers::SymbolIndex,
    };

    use super::Resolver;

    fn init<const N: usize, const ID_COUNT: usize>(
        names_to_intern: [&str; N],
    ) -> (SymbolInterner, [DefId; ID_COUNT], [SymbolIndex; N]) {
        let mut ids = DefIdProvider::new();
        let mut interner = SymbolInterner::new();
        let ids = std::array::from_fn(|_| ids.next());
        let names =
            std::array::from_fn(|index| interner.intern(names_to_intern[index].to_string()));
        (interner, ids, names)
    }

    #[test]
    fn test_simple() {
        let (_, [a_id], [a_symbol]) = init(["A"]);

        let mut global_scope = Scope::new(ScopeKind::Normal);
        global_scope.add_binding(a_symbol, Resolution::Definition(DefKind::Struct, a_id));
        let mut scope_tree = ScopeTree::new(global_scope);
        let (_, current_scope) =
            scope_tree.add_scope(Scope::new(ScopeKind::Normal), ScopeId::GLOBAL_SCOPE);
        let (_, current_scope) = scope_tree.add_scope(Scope::new(ScopeKind::Normal), current_scope);
        let (_, current_scope) = scope_tree.add_scope(Scope::new(ScopeKind::Normal), current_scope);
        let (_, current_scope) = scope_tree.add_scope(Scope::new(ScopeKind::Normal), current_scope);
        let mut resolver = Resolver::new(NameSpaces::new(), scope_tree);
        resolver.set_current_scope(current_scope);
        assert_eq!(
            resolver.resolve_path(vec![a_symbol].into_iter()),
            vec![Resolution::Definition(DefKind::Struct, a_id)]
        );
    }
}
