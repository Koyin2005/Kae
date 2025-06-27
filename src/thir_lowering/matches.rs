use std::hash::Hash;
use indexmap::IndexMap;

use crate::{data_structures::IntoIndex, frontend::{ast_lowering::hir::{ self, DefId, LiteralKind}, thir, typechecking::{context::TypeContext, types::Type}}, identifiers::{FieldIndex, VariantIndex}, middle::mir::{self, BlockId, Constant, Operand, Place}, thir_lowering::BodyBuild};

#[derive(Debug,Clone,Hash,PartialEq)]
enum TestResult{
    Success,
    Constant(Constant),
    Variant(DefId,VariantIndex),
    Failure
}
impl Eq for TestResult{}
#[derive(Debug,Clone ,PartialEq,Hash)]
enum Test {
    SwitchVariant(DefId),
    If,
    Eq(Constant),
    SwitchInt
}

#[derive(Debug,Clone,PartialEq,Hash)]
enum TestCase{
    Constant(Constant),
    Variant(DefId,VariantIndex),

}
impl Eq for TestCase{}
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
        &thir::PatternKind::Constant(literal) => {
            let (ty,constant) = match literal{
                LiteralKind::Bool(value) => (Type::Bool,mir::ConstantKind::Bool(value)),
                LiteralKind::Float(value) => (Type::Float,mir::ConstantKind::Float(value)),
                LiteralKind::Int(value) => (Type::Int,mir::ConstantKind::Int(value)),
                LiteralKind::String(value) => (Type::String,mir::ConstantKind::String(value))
            };
            Some(PlaceTest { place, test: TestCase::Constant(Constant { ty,kind:constant }) })
        },
        thir::PatternKind::Tuple(fields) => {
            for (i,field) in fields.iter().enumerate(){
                test_trees_from(context,field, place.clone().project(mir::PlaceProjection::Field(FieldIndex::new(i))), &mut subtests);
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
                test_trees_from(context,field, projected_place.clone().project(mir::PlaceProjection::Field(FieldIndex::new(i))), &mut subtests);
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
    fn test_result(place:&Place,test:&Test,branch:&mut MatchBranch) -> Option<TestResult>{
        let (index,match_test) = branch.tests.iter().enumerate().find(|(_,branch_test)|{
            &branch_test.base_test.place == place
        })?;
        let mut fully_matched = false;

        let result = match (&match_test.base_test.test,test){
            (&TestCase::Constant(mir::Constant{ty:_,kind:mir::ConstantKind::Bool(value)}),Test::If) => {
                fully_matched = true;
                if value{
                    Some(TestResult::Success)
                }
                else{
                    Some(TestResult::Failure)
                }
            },
            (&TestCase::Constant(mir::Constant{ty:_,kind:mir::ConstantKind::Int(value)}),Test::SwitchInt) => {
                fully_matched = true;
                Some(TestResult::Constant(Constant { ty: Type::Int, kind: mir::ConstantKind::Int(value) }))
            },
            (TestCase::Constant(const_val),Test::Eq(test_val))  => {
                if const_val == test_val{
                    fully_matched = true;
                    Some(TestResult::Success)
                }
                else{
                    Some(TestResult::Failure)
                }
            },
            (&TestCase::Variant(id,variant),Test::SwitchVariant(other_id)) if *other_id == id => {
                fully_matched = true;
                Some(TestResult::Variant(id, variant))
            },
            _ => None
        }?;
        if fully_matched{
            let match_test = branch.tests.remove(index);
            branch.tests.extend(match_test.subtests);
        }
        Some(result)
    }
    fn select_test(&mut self,test_case:&TestCase) -> Test{
        match test_case{
            TestCase::Constant(Constant { ty:_, kind:mir::ConstantKind::Bool(_) }) => Test::If,
            TestCase::Constant(Constant { ty:_, kind:mir::ConstantKind::Int(_) }) => Test::SwitchInt,
            TestCase::Constant(constant) => Test::Eq(constant.clone()),
            &TestCase::Variant(id,_) => Test::SwitchVariant(id),
        }
    }
    fn group_branches<'b,'c>(&mut self,place: &Place, test: &Test, mut branches : &'b mut [&'c mut MatchBranch]) -> (IndexMap<TestResult,Vec<&'b mut MatchBranch>>,&'b mut [&'c mut MatchBranch]){
        let mut grouped_branches: IndexMap<TestResult, Vec<&mut _>> = IndexMap::new();
        while let Some(branch) = branches.first_mut() {
            let Some(result) = Self::test_result(place, test, branch) else {
                break;
            };
            let (branch,rest) = branches.split_first_mut().unwrap();
            grouped_branches.entry(result).or_default().push(&mut **branch);
            branches = rest;

        }
        (grouped_branches,branches)
    }
    fn pick_test(&mut self,branches:&mut [&mut MatchBranch]) -> (Place,Test){
        let first_branch = &mut branches[0];
        let test = &first_branch.tests[0].base_test;
        (test.place.clone(),self.select_test(&test.test))
    } 
    fn perform_test(&mut self,place: Place, test: Test, targets: IndexMap<TestResult,BlockId>,otherwise_block:BlockId){
        let get_target = |result:TestResult| targets.get(&result).copied().unwrap_or(otherwise_block);
        match test{
            Test::If => {
                self.terminate(mir::Terminator::Switch(mir::Operand::Load(place),Box::new([(0,get_target(TestResult::Failure))]), get_target(TestResult::Success)));
            },
            Test::SwitchInt => {
                let targets = targets.iter().filter_map(|(result,&target)|{
                    match result{
                        &TestResult::Constant(Constant { ty:_, kind:mir::ConstantKind::Int(value) }) => Some((value,target)),
                        _ => None
                    }
                }).map(|(value,block)|{
                    let value = if value < 0{
                        u64::from_ne_bytes(value.to_ne_bytes()) as u128
                    }
                    else{
                        value as u128
                    };
                    (value,block)
                }).collect();
                self.terminate(mir::Terminator::Switch(mir::Operand::Load(place),targets, otherwise_block));
            },
            Test::Eq(constant) => {
                let success_block = get_target(TestResult::Success);
                let fail_block = get_target(TestResult::Failure);
                let is_equal = self.new_temporary(Type::Bool);
                self.assign_stmt(is_equal.into(), mir::RValue::Binary(hir::BinaryOp::Equals,Box::new((Operand::Load(place),Operand::Constant(constant)))));
                self.terminate(mir::Terminator::Switch(mir::Operand::Load(is_equal.into()), Box::new([(0,fail_block)]), success_block));
                self.current_block = fail_block;
            },
            Test::SwitchVariant(id) => {
                let discriminant = self.new_temporary(Type::Int);
                self.assign_stmt(discriminant.into(),mir::RValue::Tag(place));
                let targets = (0..self.context.expect_variants(id).len()).map(|i| VariantIndex::new(i)).filter_map(|variant|{
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
    fn build_match(&mut self,depth:usize,branches : &mut [&mut MatchBranch], start_block : BlockId) -> BlockId{
        let (remaining,otherwise_block) = match branches{
            [] => return start_block,
            [first_branch,rest @ ..] if first_branch.tests.is_empty() => {
                first_branch.success = Some(start_block);
                let otherwise_block = self.new_block();
                (rest,otherwise_block)
                
            },
            branches => {
                let (place,test) = self.pick_test(branches);
                let (branches,remaining) = self.group_branches(&place,&test,branches);
                let otherwise_block = self.new_block();
                let targets : IndexMap<_,_> = branches.into_iter().map(|(test,mut branch)|{
                    let branch_block = self.new_block();
                    let branch_otherwise = self.build_match(depth+2, &mut branch,branch_block);
                    self.current_block = branch_otherwise;
                    self.terminate(mir::Terminator::Goto(otherwise_block));
                    (test,branch_block)
                }).collect();
                self.current_block = start_block;
                self.perform_test(place, test, targets, otherwise_block);
                self.current_block = otherwise_block;
                (remaining,otherwise_block)

            }
        };
        self.build_match(depth, remaining,otherwise_block)
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
        let otherwise_block = self.build_match(0,&mut branches.iter_mut().collect::<Box<[_]>>(),self.current_block);
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