use fxhash::FxHashMap;

use crate::{frontend::parsing::ast::NodeId, identifiers::SymbolIndex};

use super::hir::{DefId, Resolution};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ScopeKind {
    Normal,
    Function(NodeId),
    Type(NodeId),
    Item(DefId),
    AssocItem(DefId),
}
#[derive(Debug)]
pub struct Scope {
    bindings: FxHashMap<SymbolIndex, Resolution>,
    kind: ScopeKind,
}

impl Scope {
    pub fn new(kind: ScopeKind) -> Self {
        Self {
            bindings: FxHashMap::default(),
            kind,
        }
    }
    pub fn kind(&self) -> ScopeKind {
        self.kind
    }
    pub fn add_binding(&mut self, id: SymbolIndex, res: Resolution) -> Option<Resolution> {
        self.bindings.insert(id, res)
    }

    pub fn get_binding(&self, id: SymbolIndex) -> Option<Resolution> {
        self.bindings.get(&id).copied()
    }

    pub fn bindings_iter<'a>(
        &'a self,
    ) -> impl Iterator<Item = (SymbolIndex, Resolution)> + use<'a> {
        self.bindings.iter().map(|(symbol, res)| (*symbol, *res))
    }
}

#[derive(Debug)]
pub struct NameSpaces {
    names_to_scopes: FxHashMap<Resolution, ScopeId>,
}
impl Default for NameSpaces {
    fn default() -> Self {
        Self::new()
    }
}
impl NameSpaces {
    pub fn new() -> Self {
        Self {
            names_to_scopes: FxHashMap::default(),
        }
    }
    pub fn define_namespace(&mut self, name: Resolution, scope: ScopeId) {
        self.names_to_scopes.insert(name, scope);
    }
    pub fn get_namespace(&self, name: Resolution) -> Option<&ScopeId> {
        self.names_to_scopes.get(&name)
    }
    pub fn expect_namespace(&self, name: Resolution) -> &ScopeId {
        self.get_namespace(name)
            .unwrap_or_else(|| panic!("There should be a namespace for '{name:?}'"))
    }
}
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ScopeId(usize);
impl ScopeId {
    pub const GLOBAL_SCOPE: ScopeId = ScopeId(0);
}
#[derive(Debug)]
struct LocalScope {
    parent: ScopeId,
    scope: Scope,
}
#[derive(Debug)]
pub struct ScopeTree {
    global_scope: Scope,
    all_scopes: Vec<LocalScope>,
}

impl ScopeTree {
    pub fn new(global: Scope) -> Self {
        Self {
            global_scope: global,
            all_scopes: vec![],
        }
    }
    pub fn get_child_scopes(&self, parent_scope: ScopeId) -> Vec<ScopeId> {
        self.all_scopes
            .iter()
            .enumerate()
            .filter_map(|(i, scope)| {
                if scope.parent == parent_scope {
                    Some(ScopeId(i + 1))
                } else {
                    None
                }
            })
            .collect()
    }
    pub fn add_scope(&mut self, scope: Scope, parent: ScopeId) -> (&mut Scope, ScopeId) {
        self.all_scopes.push(LocalScope { parent, scope });
        let id = ScopeId(self.all_scopes.len());
        (
            &mut self
                .all_scopes
                .last_mut()
                .expect("I literally just added a scope")
                .scope,
            id,
        )
    }
    pub fn get_scope_mut(&mut self, scope: ScopeId) -> &mut Scope {
        if scope == ScopeId::GLOBAL_SCOPE {
            &mut self.global_scope
        } else {
            &mut self.all_scopes[scope.0 - 1].scope
        }
    }
    pub fn get_scope(&self, scope: ScopeId) -> &Scope {
        if scope == ScopeId::GLOBAL_SCOPE {
            &self.global_scope
        } else {
            &self.all_scopes[scope.0 - 1].scope
        }
    }
    pub fn get_parent(&self, scope: ScopeId) -> Option<ScopeId> {
        if scope == ScopeId::GLOBAL_SCOPE {
            None
        } else {
            Some(self.all_scopes[scope.0 - 1].parent)
        }
    }
    pub fn resolve_ident(&self, ident: SymbolIndex, mut scope: ScopeId) -> Option<Resolution> {
        loop {
            let Some(res) = self.get_scope(scope).get_binding(ident) else {
                if let Some(parent) = self.get_parent(scope) {
                    scope = parent;
                    continue;
                } else {
                    break None;
                }
            };
            break Some(res);
        }
    }
}
