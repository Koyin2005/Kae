use std::hash::Hash;
use indexmap::IndexMap;

use crate::{data_structures::IntoIndex, frontend::{ast_lowering::hir::{DefId, LiteralKind}, thir, typechecking::{context::TypeContext, types::Type}}, identifiers::{FieldIndex, SymbolIndex, VariantIndex}, middle::mir::{self, BlockId, Place}, thir_lowering::BodyBuild};

#[derive(Debug,Clone, Copy,PartialEq)]
enum TestResult{
    Success,
    Int(i64),
    String(SymbolIndex),
    Float(f64),
    Variant(DefId,VariantIndex),
    Failure
}
impl Eq for TestResult{}
impl Hash for TestResult{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match *self {
            Self::Success => state.write_i8(0 as i8),
            Self::Failure => state.write_i8(1 as i8),
            Self::Int(value) => state.write_i64(value),
            Self::String(index) => state.write_u32(index.as_index()),
            Self::Variant(id,index) => {state.write_u32(id.as_index());state.write_u32(index.as_index());},
            Self::Float(value) => state.write_u64(value.to_bits()),

        }
    }
}
#[derive(Debug,Clone, Copy,PartialEq, Eq,Hash)]
enum Test {
    SwitchVariant(DefId),
    If,
    Eq,
    SwitchInt
}

#[derive(Debug,Clone, Copy,PartialEq)]
enum TestCase{
    Bool(bool),
    Int(i64),
    String(SymbolIndex),
    Float(f64),
    Variant(DefId,VariantIndex),

}
impl Eq for TestCase{}
impl Hash for TestCase{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match *self {
            Self::Bool(value) => state.write_i8(value as i8),
            Self::Int(value) => state.write_i64(value),
            Self::String(index) => state.write_u32(index.as_index()),
            Self::Variant(id,index) => {state.write_u32(id.as_index());state.write_u32(index.as_index());},
            Self::Float(value) => state.write_u64(value.to_bits()),
        }
    }
}
#[derive(Debug,Clone)]
struct PlaceTest{
    place : Place,
    test : TestCase
}


#[derive(Debug,Clone)]
struct TestTree{
    base_test : PlaceTest,
    subtests : Vec<TestTree>
}
#[derive(Debug)]
struct MatchBranch{
    tests : Vec<TestTree>,
    success : Option<BlockId>
}
fn test_trees_from(context:&TypeContext,pattern:&thir::Pattern, place: Place, tests: &mut Vec<TestTree>){
    let mut subtests = Vec::new();
    let base_test = match &pattern.kind {
        thir::PatternKind::Binding(_,_,sub_pattern) => {
            if let Some(pattern) = sub_pattern{
                test_trees_from(context,pattern,place, &mut subtests);
            }
            None
        },
        &thir::PatternKind::Constant(literal) => match literal{
            LiteralKind::Bool(value) => Some(PlaceTest{place,test:TestCase::Bool(value)}),
            LiteralKind::Float(value) => Some(PlaceTest { place, test: TestCase::Float(value) }),
            LiteralKind::Int(value) => Some(PlaceTest { place, test: TestCase::Int(value) }),
            LiteralKind::String(value) => Some(PlaceTest { place, test: TestCase::String(value) })
        },
        thir::PatternKind::Tuple(fields) => {
            for (i,field) in fields.iter().enumerate(){
                test_trees_from(context,field, place.clone().project(mir::PlaceProjection::Field(FieldIndex::new(i as u32))), &mut subtests);
            }
            None
        },
        thir::PatternKind::Struct(_,_,fields) => {
            for field_pattern in fields{
                test_trees_from(context,&field_pattern.pattern, place.clone().project(mir::PlaceProjection::Field(field_pattern.field)), &mut subtests);
            }
            None
        },
        &thir::PatternKind::Variant(id,_,variant,ref fields) => {
                let projected_place = place.clone().project(mir::PlaceProjection::Variant(context.get_variant_by_index(id, variant).name.index, variant));
            for (i,field) in fields.iter().enumerate(){
                test_trees_from(context,field, projected_place.clone().project(mir::PlaceProjection::Field(FieldIndex::new(i as u32))), &mut subtests);
            }
            Some(PlaceTest { place: place, test: TestCase::Variant(id, variant) })
        }
        thir::PatternKind::Wildcard => None
    };
    if let Some(test) = base_test{
        tests.push(TestTree { base_test: test, subtests});
    }
    else{
        tests.extend(subtests);
    }
}

impl <'a> BodyBuild<'a>{
    fn test_result(place:&Place,test:&Test,branch:&mut MatchBranch) -> Option<(TestResult,bool)>{
        let (index,match_test) = branch.tests.iter().enumerate().find(|(_,branch_test)|{
            &branch_test.base_test.place == place
        })?;
        let mut fully_matched = false;

        let result = match (match_test.base_test.test,test){
            (TestCase::Bool(value),Test::If) => {
                fully_matched = true;
                if value{
                    Some(TestResult::Success)
                }
                else{
                    Some(TestResult::Failure)
                }
            },
            (TestCase::Int(value),Test::SwitchInt) => {
                fully_matched = true;
                Some(TestResult::Int(value))
            },
            (TestCase::String(string),Test::Eq) => {
                fully_matched = true;
                Some(TestResult::String(string))
            },
            (TestCase::Float(float),Test::Eq) => {
                fully_matched = true;
                Some(TestResult::Float(float))
            },
            (TestCase::Variant(id,variant),Test::SwitchVariant(other_id)) if *other_id == id => {
                fully_matched = true;
                Some(TestResult::Variant(id, variant))
            },
            _ => None
        }?;
        if fully_matched{
            let match_test = branch.tests.remove(index);
            branch.tests.extend(match_test.subtests);
        }
        Some((result,true))
    }
    fn select_test(&mut self,test_case:&TestCase) -> Test{
        match test_case{
            TestCase::Bool(_) => Test::If,
            TestCase::Float(_)|TestCase::String(_) => Test::Eq,
            TestCase::Int(_) => Test::SwitchInt,
            &TestCase::Variant(id,_) => Test::SwitchVariant(id),
        }
    }
    fn group_branches<'b>(&mut self,place: &Place, test: &Test, branches : Vec<&'b mut MatchBranch>) -> (IndexMap<TestResult,Vec<&'b mut MatchBranch>>,Vec<&'b mut MatchBranch>,bool){

        let mut grouped_branches: IndexMap<TestResult, Vec<&'b mut _>> = IndexMap::new();
        let mut remaining = Vec::new();
        let mut explicit_fail = false;
        for branch in branches{
            let Some((result,explicit)) = Self::test_result(place, test, branch) else {
                remaining.push(branch);
                continue;
            };
            grouped_branches.entry(result).or_default().push(branch);
            if result == TestResult::Failure && explicit{
                explicit_fail = true;
            }
        }
        (grouped_branches,remaining,explicit_fail)
    }
    fn pick_test(&mut self,branches:&mut [&mut MatchBranch]) -> (Place,Test){
        let first_branch = &mut branches[0];

        let test = &first_branch.tests[0].base_test;
        (test.place.clone(),self.select_test(&test.test))
    } 
    fn perform_test(&mut self,place: Place, test: &Test, targets: IndexMap<TestResult,BlockId>,otherwise_block:BlockId){
        let get_target = |result:TestResult| targets.get(&result).copied().unwrap_or(otherwise_block);
        match test{
            Test::If => {
                self.terminate(mir::Terminator::Switch(mir::Operand::Load(place),Box::new([(0,get_target(TestResult::Failure))]), get_target(TestResult::Success)));
            },
            Test::SwitchInt => {
                
                todo!("Handle test for switch int")
            },
            Test::Eq => {
                todo!("Handle test for eq")
            },
            &Test::SwitchVariant(id) => {
                let discriminant = self.new_temporary(Type::Int);
                self.assign_stmt(discriminant.into(),mir::RValue::Tag(place));
                let targets = (0..self.context.expect_variants(id).len()).map(|i| VariantIndex::new(i as u32)).filter_map(|variant|{
                    if let Some(_) = targets.get(&TestResult::Variant(id, variant)){
                        Some((variant.as_index() as u128,get_target(TestResult::Variant(id, variant))))
                    }
                    else{
                        None
                    }
                }).collect();
                self.terminate(mir::Terminator::Switch(mir::Operand::Load(discriminant.into()), targets, get_target(TestResult::Failure)));
            }
        }
    }
    fn build_match(&mut self,depth:usize,mut branches : Vec<&mut MatchBranch>, start_block : BlockId) -> BlockId{
        if branches.is_empty(){
            return start_block;
        }
        if branches[0].tests.is_empty(){
            branches[0].success = Some(start_block);
            let otherwise_block = self.new_block();
            self.build_match(depth, branches.split_off(1),otherwise_block)
        }
        else{
            let (place,test) = self.pick_test(&mut branches);
            let (branches,remaining,_) = self.group_branches(&place,&test,branches);
            let otherwise_block = self.new_block();
            let targets : IndexMap<_,_> = branches.into_iter().map(|(test,branch)|{
                let branch_block = self.new_block();
                let branch_otherwise = self.build_match(depth+2, branch,branch_block);
                self.current_block = branch_otherwise;
                self.terminate(mir::Terminator::Goto(otherwise_block));
                (test,branch_block)
            }).collect();
            self.current_block = start_block;
            self.perform_test(place, &test, targets, otherwise_block);
            self.current_block = otherwise_block;
            self.build_match(depth, remaining,otherwise_block)
        }

    }
    pub fn lower_match<'b>(&mut self,place : Option<Place>,scrutinee: Place, _: &Type,arms: impl Iterator<Item = &'b thir::Arm>){

        let (tests,bodies):(Vec<_>,Vec<_>) = arms.into_iter().map(|arm|{
            let mut tests = Vec::new();
            test_trees_from(self.context, &arm.pat, scrutinee.clone(), &mut tests);
            (tests,(arm.body,&arm.pat))
        }).unzip();

        let mut branches = tests.into_iter().map(|tests|{
            MatchBranch{tests,success:None}
        }).collect::<Vec<_>>();
        let otherwise_block = self.build_match(0,branches.iter_mut().collect(),self.current_block);
        self.current_block = otherwise_block;
        self.terminate(mir::Terminator::Unreachable);
        let blocks =  branches.into_iter().zip(bodies).map(|(branch,(body,pat))|{
            let block = branch.success.unwrap();
            self.current_block = block;
            self.declare_bindings(pat);
            self.lower_let(pat, scrutinee.clone());
            self.lower_expr(body,place.clone());
            self.current_block
        }).collect::<Vec<_>>();
        let merge_block = self.new_block();
        for block in blocks{
            self.current_block = block;
            self.terminate(mir::Terminator::Goto(merge_block));
        }
        self.current_block = merge_block;
        

    }
}