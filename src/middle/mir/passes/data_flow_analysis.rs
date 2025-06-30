use std::collections::{VecDeque, hash_map::Entry};

use fxhash::{FxHashMap, FxHashSet};

use crate::{
    data_structures::IndexVec,
    define_id,
    frontend::typechecking::context::TypeContext,
    identifiers::{FieldIndex, VariantIndex},
    middle::mir::{
        BlockId, Body, Local, Location, Place, PlaceProjection, Stmt, Terminator,
        basic_blocks::BasicBlockInfo,
        traversal,
        visitor::{PlaceContext, Visitor},
    },
};

pub trait Analysis: Sized {
    type Domain: JoinLattice + Clone;
    fn initialize_entry_block(&mut self, _state: &mut Self::Domain, _body: &Body) {}
    fn perform_statement_effect(&mut self, stmt: &Stmt, state: &mut Self::Domain);
    fn perform_terminator_effect(
        &mut self,
        terminator: &Terminator,
        _state: &mut Self::Domain,
    ) -> Box<[BlockId]> {
        terminator.successors()
    }
    fn bottom_value(&self) -> Self::Domain;
    fn iterate_to_fixed_point(&mut self, body: &Body) -> Results<Self::Domain> {
        let mut queue = VecDeque::new();
        let mut visited = FxHashSet::default();
        let basic_blocks = BasicBlockInfo::new(body);
        let mut results: IndexVec<BlockId, _> =
            IndexVec::from(self.bottom_value(), body.blocks.len());
        for block in traversal::reversed_postorder(&basic_blocks) {
            queue.push_back(block);
            visited.insert(block);
        }
        self.initialize_entry_block(&mut results[BlockId::START_BLOCK], body);
        let mut state = self.bottom_value();
        while let Some(block) = queue.pop_front() {
            visited.remove(&block);
            state.clone_from(&results[block]);
            for stmt in body.blocks[block].stmts.iter() {
                self.perform_statement_effect(stmt, &mut state);
            }
            for succ in
                self.perform_terminator_effect(body.blocks[block].expect_terminator(), &mut state)
            {
                if results[succ].join(&state) && visited.insert(succ) {
                    queue.push_back(succ);
                }
            }
        }
        results
    }
}

pub trait ResultVisitor<A: Analysis> {
    fn before_statement_effect(&mut self, _location: Location, _stmt: &Stmt, _state: &A::Domain) {}
    fn after_statement_effect(&mut self, _location: Location, _stmt: &Stmt, _state: &A::Domain) {}
    fn before_terminator_effect(
        &mut self,
        _location: Location,
        _terminator: &Terminator,
        _state: &A::Domain,
    ) {
    }
    fn after_terminator_effect(
        &mut self,
        _location: Location,
        _terminator: &Terminator,
        _state: &A::Domain,
    ) {
    }
}

pub fn visit_reachable_results<A: Analysis>(
    visitor: &mut impl ResultVisitor<A>,
    body: &Body,
    analysis: &mut A,
    results: Results<A::Domain>,
) {
    visit_results(
        visitor,
        body,
        traversal::reachable(&BasicBlockInfo::new(body)),
        analysis,
        results,
    );
}
pub fn visit_results<A: Analysis>(
    visitor: &mut impl ResultVisitor<A>,
    body: &Body,
    blocks: impl Iterator<Item = BlockId>,
    analysis: &mut A,
    mut results: Results<A::Domain>,
) {
    for block in blocks {
        for (i, stmt) in body.blocks[block].stmts.iter().enumerate() {
            let location = Location {
                statement_index: i,
                basic_block: block,
            };
            visitor.before_statement_effect(location, stmt, &results[block]);
            analysis.perform_statement_effect(stmt, &mut results[block]);
            visitor.after_statement_effect(location, stmt, &results[block]);
        }
        let location = Location {
            basic_block: block,
            statement_index: body.blocks[block].stmts.len(),
        };
        let terminator = body.blocks[block].expect_terminator();
        visitor.before_terminator_effect(location, terminator, &results[block]);
        analysis.perform_terminator_effect(terminator, &mut results[block]);
        visitor.after_terminator_effect(location, terminator, &results[block]);
    }
}

pub type Results<State> = IndexVec<BlockId, State>;

pub trait JoinLattice {
    fn join(&mut self, other: &Self) -> bool;
}

#[derive(Clone)]
pub struct StateInfo<V> {
    bottom: V,
    map: FxHashMap<PlaceIndex, V>,
}
impl<V: HasBottom> StateInfo<V> {
    pub fn new() -> Self {
        Self {
            map: FxHashMap::default(),
            bottom: V::BOTTOM,
        }
    }
    fn insert(&mut self, place_index: PlaceIndex, v: V) {
        self.map.insert(place_index, v);
    }
    fn get(&self, place_index: PlaceIndex) -> &V {
        self.map.get(&place_index).unwrap_or(&self.bottom)
    }
}
impl<V: HasBottom> Default for StateInfo<V> {
    fn default() -> Self {
        Self::new()
    }
}
#[derive(Clone)]
pub enum State<V> {
    Unreachable,
    Reachable(StateInfo<V>),
}
impl<V: HasBottom> State<V> {
    pub fn new() -> Self {
        Self::Reachable(StateInfo::new())
    }
}
impl<V: HasBottom> Default for State<V> {
    fn default() -> Self {
        Self::new()
    }
}

pub trait HasBottom {
    const BOTTOM: Self;
    fn is_bottom(&self) -> bool;
}
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum CompleteSet<T> {
    Top,
    Elem(T),
    Bottom,
}

impl<T> HasBottom for CompleteSet<T> {
    const BOTTOM: Self = Self::Bottom;
    fn is_bottom(&self) -> bool {
        match self {
            Self::Bottom => true,
            Self::Elem(_) | Self::Top => false,
        }
    }
}

impl<T: Clone + Eq> JoinLattice for CompleteSet<T> {
    fn join(&mut self, other: &Self) -> bool {
        let result = match (&mut *self, other) {
            (Self::Top, _) | (_, Self::Bottom) => return false,
            (Self::Elem(this), Self::Elem(other)) if this == other => return false,
            (Self::Bottom, Self::Elem(value)) => Self::Elem(value.clone()),
            _ => Self::Top,
        };
        *self = result;
        true
    }
}

impl<V: Clone + HasBottom> State<V> {
    pub fn insert(&mut self, place: PlaceIndex, val: V) {
        let State::Reachable(state) = self else {
            return;
        };
        state.insert(place, val);
    }
    pub fn get(&self, place: PlaceIndex) -> V {
        match self {
            Self::Unreachable => V::BOTTOM,
            Self::Reachable(state) => state.get(place).clone(),
        }
    }
}

impl<V: Clone + JoinLattice> JoinLattice for State<V> {
    fn join(&mut self, other: &Self) -> bool {
        match (&mut *self, other) {
            (_, Self::Unreachable) => false,
            (Self::Unreachable, _) => {
                *self = other.clone();
                true
            }
            (Self::Reachable(this), Self::Reachable(other)) => this.join(other),
        }
    }
}

impl<V: JoinLattice + Clone> JoinLattice for StateInfo<V> {
    fn join(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for (place, val) in other.map.iter() {
            match self.map.entry(*place) {
                Entry::Occupied(mut occupied) => {
                    changed |= occupied.get_mut().join(val);
                }
                Entry::Vacant(occupied) => {
                    occupied.insert(val.clone());
                    changed |= true;
                }
            }
        }
        changed
    }
}

define_id!(pub PlaceIndex);

#[derive(Debug)]
pub struct PlaceInfo {
    pub projection: Option<Projection>,
    children: Vec<PlaceIndex>,
}
#[derive(Debug)]
pub struct Map {
    locals: IndexVec<Local, Option<PlaceIndex>>,
    projections: FxHashMap<(PlaceIndex, Projection), PlaceIndex>,
    tracked_places: IndexVec<PlaceIndex, PlaceInfo>,
}
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum Projection {
    Field(FieldIndex),
    Variant(VariantIndex),
    Tag,
}

impl TryFrom<PlaceProjection> for Projection {
    type Error = ();
    fn try_from(value: PlaceProjection) -> Result<Self, Self::Error> {
        match value {
            PlaceProjection::Field(field_index) => Ok(Projection::Field(field_index)),
            PlaceProjection::Variant(_, index) => Ok(Projection::Variant(index)),
            PlaceProjection::ConstantIndex(_) | PlaceProjection::Index(_) => Err(()),
        }
    }
}
impl Map {
    pub fn for_each_place_in<T: Clone>(
        &self,
        place: PlaceIndex,
        value: T,
        map: &mut impl FnMut(PlaceIndex, Projection, &T) -> T,
        f: &mut impl FnMut(PlaceIndex, T),
    ) {
        let place_info = &self.tracked_places[place];
        for &child in &place_info.children {
            let val = if let Some(projection) = self.tracked_places[child].projection {
                map(child, projection, &value)
            } else {
                value.clone()
            };
            self.for_each_place_in(child, val, map, f);
        }
        f(place, value);
    }
    pub fn get_projection_for(
        &self,
        place: PlaceIndex,
        projection: Projection,
    ) -> Option<PlaceIndex> {
        self.projections.get(&(place, projection)).copied()
    }
    pub fn get(&self, place: &Place) -> Option<PlaceIndex> {
        let mut curr_place = self.locals[place.local]?;
        for &projection in &place.projections {
            let projection = match projection {
                PlaceProjection::Field(field_index) => Projection::Field(field_index),
                PlaceProjection::Variant(_, variant) => Projection::Variant(variant),
                _ => return None,
            };
            curr_place = *self.projections.get(&(curr_place, projection))?;
        }
        Some(curr_place)
    }
    pub fn new(body: &Body, context: &TypeContext) -> Self {
        let mut map = Self {
            locals: IndexVec::from(None, body.locals.len()),
            projections: FxHashMap::default(),
            tracked_places: IndexVec::new(),
        };
        for local in body.args() {
            map.locals[local] = Some(map.next_place(PlaceInfo {
                projection: None,
                children: vec![],
            }));
        }
        PlaceCollector {
            map: &mut map,
            body,
            context,
        }
        .visit_body(body);
        map
    }
    fn next_place(&mut self, place_info: PlaceInfo) -> PlaceIndex {
        self.tracked_places.push(place_info)
    }
}

struct PlaceCollector<'a> {
    map: &'a mut Map,
    body: &'a Body,
    context: &'a TypeContext,
}
impl Visitor for PlaceCollector<'_> {
    fn visit_place(&mut self, place: &Place, _: PlaceContext, _: Location) {
        let local = place.local;
        let mut current_place = match self.map.locals[local] {
            Some(place) => place,
            None => {
                let place = self.map.next_place(PlaceInfo {
                    projection: None,
                    children: vec![],
                });
                self.map.locals[local] = Some(place);
                place
            }
        };
        for &projection in &place.projections {
            let Ok(projection) = projection.try_into() else {
                break;
            };
            let next_place = match self.map.projections.get(&(current_place, projection)) {
                Some(&place) => place,
                None => {
                    let place = self.map.next_place(PlaceInfo {
                        projection: Some(projection),
                        children: vec![],
                    });
                    self.map
                        .projections
                        .insert((current_place, projection), place);
                    place
                }
            };
            self.map.tracked_places[current_place]
                .children
                .push(next_place);
            current_place = next_place;
        }
        if place.type_of(self.context, self.body).is_enum() {
            let tag_place = self.map.next_place(PlaceInfo {
                projection: Some(Projection::Tag),
                children: vec![],
            });
            self.map
                .projections
                .insert((current_place, Projection::Tag), tag_place);
            self.map.tracked_places[current_place]
                .children
                .push(tag_place);
        }
    }
}
