use crate::{
    SymbolInterner,
    data_structures::IntoIndex,
    identifiers::{SymbolIndex, VariantIndex},
};
pub mod lowering;
use super::typechecking::{
    context::TypeContext,
    types::{
        AdtKind, Type,
        format::TypeFormatter,
        subst::{Subst, TypeSubst},
    },
};
#[derive(Clone, Debug)]
pub struct Pattern {
    ty: Type,
    constructor: Constructor,
    fields: Vec<Pattern>,
}
impl Pattern {
    pub fn specialize(&self, constructor: Constructor, fields: &[Type]) -> Option<Vec<Self>> {
        if !constructor.is_covered_by(&self.constructor) {
            return None;
        }
        let is_wildcard = self.constructor == Constructor::Wildcard;
        Some(if is_wildcard {
            fields
                .iter()
                .map(|field| Pattern {
                    ty: field.clone(),
                    constructor: Constructor::Wildcard,
                    fields: vec![],
                })
                .collect()
        } else {
            self.fields.clone()
        })
    }
    fn format_fields<'a>(
        &self,
        context: &TypeContext,
        interner: &SymbolInterner,
        mut field_names: impl Iterator<Item = &'a str>,
    ) -> String {
        let mut result = String::new();
        for (i, field) in self.fields.iter().enumerate() {
            if i > 0 {
                result.push(',');
            }
            if let Some(field_name) = field_names.next() {
                result.push_str(&format!(
                    "{}:{}",
                    field_name,
                    field.format(context, interner)
                ));
            } else {
                result.push_str(&field.format(context, interner));
            }
        }
        result
    }
    pub fn format(&self, context: &TypeContext, interner: &SymbolInterner) -> String {
        match (self.constructor, &self.ty) {
            (Constructor::Bool(value), _) => value.to_string(),
            (Constructor::String(value), _) => interner.get(value).to_string(),
            (Constructor::Int(value), _) => value.to_string(),
            (Constructor::Float(value), _) => value.to_string(),
            (Constructor::Variant(index), ty) => {
                let &Type::Adt(_, id, AdtKind::Enum) = ty else {
                    unreachable!("Variant constructors should always have type enum")
                };
                if !self.fields.is_empty() {
                    format!(
                        "{}({})",
                        interner
                            .get(
                                context
                                    .ident(context.get_variant_by_index(id, index).id)
                                    .index
                            )
                            .to_string(),
                        self.format_fields(context, interner, None.into_iter())
                    )
                } else {
                    interner
                        .get(context.get_variant_by_index(id, index).name.index)
                        .to_string()
                }
            }
            (Constructor::Struct, ty) => {
                if let &Type::Adt(_, id, _) = ty {
                    let field_names = context
                        .expect_struct(id)
                        .fields
                        .iter()
                        .map(|field| interner.get(field.name.index));
                    format!(
                        "{}{{{}}}",
                        TypeFormatter::new(interner, context).format_type(&ty),
                        self.format_fields(context, interner, field_names)
                    )
                } else {
                    format!(
                        "({})",
                        self.format_fields(context, interner, None.into_iter())
                    )
                }
            }
            (Constructor::Wildcard, _) => format!("_"),
            (Constructor::Missing | Constructor::NonExhaustive, _) => format!("_"),
        }
    }
}

#[derive(Debug)]
pub enum ConstructorSet {
    Infinite,
    Variants(Vec<VariantIndex>),
    Bool,
    Struct,
    Empty,
}
impl ConstructorSet {
    pub fn split_constructors(
        &self,
        checker: &PatternChecker,
        ty: &Type,
        seen_constructors: &Vec<Constructor>,
    ) -> (Vec<Constructor>, Vec<Constructor>) {
        let mut seen = Vec::new();
        let mut missing = Vec::new();
        match self {
            Self::Bool => {
                if seen_constructors.contains(&Constructor::Bool(true)) {
                    seen.push(Constructor::Bool(true));
                } else {
                    missing.push(Constructor::Bool(true));
                }
                if seen_constructors.contains(&Constructor::Bool(false)) {
                    seen.push(Constructor::Bool(false));
                } else {
                    missing.push(Constructor::Bool(false));
                }
            }
            &Self::Variants(ref variants) => {
                let mut seen_map = vec![false; variants.len()];
                for constructor in seen_constructors {
                    if let Constructor::Variant(variant) = *constructor {
                        seen_map[variant.as_index() as usize] = true;
                    }
                }
                for (&variant, was_seen) in variants.iter().zip(seen_map) {
                    if was_seen {
                        seen.push(Constructor::Variant(variant));
                    } else if checker
                        .fields(ty, Constructor::Variant(variant))
                        .iter()
                        .all(|ty| checker.context.is_type_inhabited(ty))
                    {
                        missing.push(Constructor::Variant(variant));
                    }
                }
            }
            Self::Struct => {
                if !seen_constructors.is_empty() {
                    seen.push(Constructor::Struct);
                } else if checker
                    .fields(ty, Constructor::Struct)
                    .iter()
                    .all(|ty| checker.context.is_type_inhabited(ty))
                {
                    missing.push(Constructor::Missing);
                }
            }
            Self::Empty => (),
            Self::Infinite => {
                seen.extend_from_slice(&seen_constructors);
                missing.push(Constructor::NonExhaustive);
            }
        }
        (seen, missing)
    }
}
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Constructor {
    Int(i64),
    Bool(bool),
    Float(f64),
    Struct,
    Wildcard,
    Variant(VariantIndex),
    String(SymbolIndex),
    NonExhaustive,
    Missing,
}
impl Constructor {
    pub fn is_covered_by(&self, other: &Self) -> bool {
        let covered = match (self, other) {
            (_, Constructor::Wildcard) => true,
            (Constructor::NonExhaustive | Constructor::Missing, _) => false,
            (Constructor::Struct, Constructor::Struct) => true,
            (Constructor::Bool(value), Constructor::Bool(other_value)) => value == other_value,
            (Constructor::Int(value), Constructor::Int(other_value)) => value == other_value,
            (Constructor::Float(value), Constructor::Float(other_value)) => value == other_value,
            (Constructor::String(value), Constructor::String(other_value)) => value == other_value,
            (Constructor::Variant(index), Constructor::Variant(other_index)) => {
                index == other_index
            }
            _ => false,
        };
        covered
    }
}
#[derive(Clone, Debug)]
pub struct PatternRow {
    patterns: Vec<Pattern>,
}
impl PatternRow {
    pub fn new(row: Vec<Pattern>) -> Self {
        Self { patterns: row }
    }
    pub fn first_pattern(&self) -> Option<&Pattern> {
        self.patterns.get(0)
    }
    pub fn len(&self) -> usize {
        self.patterns.len()
    }
    pub fn take_first(&mut self) -> Pattern {
        self.patterns.remove(0)
    }
    pub fn specialize(&self, constructor: Constructor, fields: &[Type]) -> Option<Self> {
        let first_pattern = self.first_pattern()?;
        let Some(new_fields) = first_pattern.specialize(constructor, fields) else {
            return None;
        };
        let new_row = Self {
            patterns: new_fields
                .into_iter()
                .chain(self.patterns[1..].iter().cloned())
                .collect(),
        };
        Some(new_row)
    }
    pub fn unspecialize(&self, ty: Type, constructor: Constructor, arity: usize) -> Self {
        let fields = &self.patterns[0..arity];
        Self {
            patterns: std::iter::once(Pattern {
                ty,
                constructor,
                fields: fields.to_vec(),
            })
            .chain(self.patterns[arity..].iter().cloned())
            .collect(),
        }
    }
}
#[derive(Clone, Debug)]
pub struct PatternMatrix {
    column_types: Vec<Type>,
    rows: Vec<PatternRow>,
}
impl PatternMatrix {
    fn new(rows: impl Iterator<Item = PatternRow>, column_types: Vec<Type>) -> Self {
        Self {
            rows: rows.collect(),
            column_types,
        }
    }
    fn new_empty(column_types: Vec<Type>) -> Self {
        Self {
            rows: Vec::new(),
            column_types,
        }
    }

    fn specialize(&self, constructor: Constructor, fields: &[Type]) -> Self {
        let new_rows = self
            .rows
            .iter()
            .filter_map(|row| row.specialize(constructor, fields))
            .collect();
        let mut columns = Vec::new();
        columns.extend_from_slice(fields);
        if self.column_types.len() > 1 {
            columns.extend_from_slice(&self.column_types[1..]);
        }
        Self {
            rows: new_rows,
            column_types: columns,
        }
    }
}
pub struct PatternChecker<'a> {
    context: &'a TypeContext,
}
impl<'a> PatternChecker<'a> {
    pub fn new(context: &'a TypeContext) -> Self {
        Self { context }
    }
    fn constructors(&self, ty: &Type) -> ConstructorSet {
        match ty {
            &Type::Adt(_, id, kind) => match kind {
                AdtKind::Enum => {
                    let variants = self.context.expect_variants_for(id);
                    if variants.is_empty() {
                        ConstructorSet::Empty
                    } else {
                        ConstructorSet::Variants(variants)
                    }
                }
                AdtKind::Struct => ConstructorSet::Struct,
            },
            Type::Bool => ConstructorSet::Bool,
            Type::Tuple(_) => ConstructorSet::Struct,
            Type::Int => ConstructorSet::Infinite,
            Type::Never => ConstructorSet::Empty,
            Type::Param(_, _)
            | Type::Error
            | Type::Float
            | Type::String
            | Type::Array(_)
            | Type::Function(_, _) => ConstructorSet::Infinite,
        }
    }
    fn fields(&self, ty: &Type, constructor: Constructor) -> Vec<Type> {
        match (constructor, ty) {
            (Constructor::Bool(_), _) => vec![],
            (Constructor::Float(_), _) => vec![],
            (Constructor::Int(_), _) => vec![],
            (Constructor::Missing, _) => vec![],
            (Constructor::String(_), _) => vec![],
            (Constructor::NonExhaustive | Constructor::Wildcard, _) => vec![],
            (Constructor::Struct, Type::Tuple(fields)) => fields.clone(),
            (Constructor::Struct, &Type::Adt(ref args, id, AdtKind::Struct)) => self
                .context
                .field_defs(id)
                .iter()
                .map(|field_def| TypeSubst::new(args).instantiate_type(&field_def.ty))
                .collect(),
            (Constructor::Variant(variant_index), &Type::Adt(ref args, id, AdtKind::Enum)) => self
                .context
                .get_variant_by_index(id, variant_index)
                .fields
                .iter()
                .map(|ty| TypeSubst::new(args).instantiate_type(ty))
                .collect(),

            (ctor, ty) => unreachable!("Cannot find fields for {:?} {:?}", ctor, ty),
        }
    }
    fn usefulness(&self, matrix: PatternMatrix, depth: usize) -> PatternMatrix {
        /*There are no columns */
        if matrix.column_types.is_empty() {
            if matrix.rows.is_empty() {
                return PatternMatrix::new(vec![PatternRow::new(vec![])].into_iter(), vec![]);
            } else {
                return PatternMatrix::new_empty(vec![]);
            }
        }
        let ty = &matrix.column_types[0];
        /*There are no rows there can be more useful patterns*/
        let all_constructors = self.constructors(&ty);

        let mut had_wildcard = false;
        let seen_constructors = matrix
            .rows
            .iter()
            .filter_map(|row| match row.first_pattern()?.constructor {
                Constructor::Wildcard => {
                    had_wildcard = true;
                    None
                }
                constructor => Some(constructor),
            })
            .collect();

        let (mut constructors, mut missing) =
            all_constructors.split_constructors(self, ty, &seen_constructors);
        let mut witness_matrix = PatternMatrix::new_empty(matrix.column_types.clone());
        if !missing.is_empty() && seen_constructors.is_empty() && depth > 0 {
            missing = vec![Constructor::Wildcard];
        }
        if !missing.is_empty() {
            constructors.push(Constructor::Missing);
        }
        for constructor in constructors {
            let column_types = self.fields(&ty, constructor);
            let arity = column_types.len();
            let specialized_matrix = matrix.specialize(constructor, &column_types);
            let mut new_witnesses = self.usefulness(specialized_matrix, depth + 1);
            let new_witnesses = if matches!(constructor, Constructor::Missing) {
                let old_witnesses = new_witnesses;
                let mut new_witness_matrix = PatternMatrix::new_empty(vec![]);
                for &missing_constructor in &missing {
                    let fields = self.fields(&ty, missing_constructor);
                    let mut old_witnesses = old_witnesses.clone();
                    let wild_card_filled_pattern = Pattern {
                        ty: ty.clone(),
                        constructor: missing_constructor,
                        fields: fields
                            .into_iter()
                            .map(|field| Pattern {
                                ty: field,
                                constructor: Constructor::Wildcard,
                                fields: vec![],
                            })
                            .collect(),
                    };
                    for row in &mut old_witnesses.rows {
                        row.patterns.insert(0, wild_card_filled_pattern.clone());
                    }
                    for row in old_witnesses.rows {
                        new_witness_matrix.rows.push(row);
                    }
                }
                new_witness_matrix
            } else {
                new_witnesses.rows.iter_mut().for_each(|row| {
                    *row = row.unspecialize(ty.clone(), constructor, arity);
                });
                new_witnesses
            };
            for row in new_witnesses.rows {
                witness_matrix.rows.push(row);
            }
        }
        witness_matrix
    }
    pub fn check_exhaustive(self, patterns: Vec<Pattern>, ty: &Type) -> ExhaustiveResults {
        let matrix = self.usefulness(
            PatternMatrix::new(
                patterns
                    .into_iter()
                    .map(|pattern| PatternRow::new(vec![pattern])),
                vec![ty.clone()],
            ),
            0,
        );
        ExhaustiveResults {
            missing_patterns: matrix
                .rows
                .into_iter()
                .map(|mut row| row.take_first())
                .collect(),
        }
    }
}

pub struct ExhaustiveResults {
    missing_patterns: Vec<Pattern>,
}
impl ExhaustiveResults {
    pub fn missing_patterns(self) -> Vec<Pattern> {
        self.missing_patterns
    }
}
