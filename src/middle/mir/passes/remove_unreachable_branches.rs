use fxhash::FxHashSet;

use crate::{ frontend::typechecking::{context::TypeContext, types::{subst::{Subst, TypeSubst}}}, middle::mir::{passes::MirPass, Body, Operand, RValue, Stmt, Terminator}};

pub struct RemoveUnreachableBranches;

impl MirPass for  RemoveUnreachableBranches{
    fn name(&self) -> &str {
        "Remove-Unreachable-Branches"
    }
    fn run_pass(&self, ctxt: &TypeContext, body:&mut Body){
        for (block,block_data) in body.blocks.index_value_iter_mut(){
            let Terminator::Switch(Operand::Load(place),targets,branch) = block_data.expect_terminator() else {
                continue;
            };
            let enum_place = block_data.stmts.iter().rev().find_map(|stmt|{
                let Stmt::Assign(lvalue,RValue::Tag(enum_place))  = stmt else {
                    return None;
                };
                (lvalue == place).then_some(enum_place)
            });
            if let Some(enum_place) = enum_place{
                let ty = enum_place.type_of(ctxt, body);
                let (generic_args,id,_) = ty.as_adt().expect("Should be an enum");
                let inhabited_variants =  ctxt.expect_variants(id).enumerate().into_iter().filter_map(|(i,variant)|{
                    variant.fields.iter().all(|field| ctxt.is_type_inhabited(&TypeSubst::new(generic_args).instantiate_type(field))).then_some(i as u128)
                }).collect::<FxHashSet<_>>();
                let mut targets = targets.iter().filter_map(|&(value,target)|{
                    inhabited_variants.contains(&value).then_some(
                        (value,target)
                    )
                }).collect::<Vec<_>>();

                let terminator = if targets.len() == inhabited_variants.len(){
                    if let Some((_,otherwise)) = targets.pop(){
                        if !targets.is_empty(){
                            Terminator::Switch(Operand::Load(place.clone()), targets.into_boxed_slice(), otherwise)
                        }
                        else{
                            Terminator::Goto(otherwise)
                        }
                    }
                    else{
                        Terminator::Unreachable
                    }
                }
                else{
                    Terminator::Switch(Operand::Load(place.clone()),targets.into_boxed_slice(), *branch)
                };
                block_data.terminator = Some(terminator);
                
            }
        }
    }
}