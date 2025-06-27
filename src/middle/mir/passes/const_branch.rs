use crate::{frontend::typechecking::context::TypeContext, middle::mir::{passes::{MirPass, Patch}, Body, Operand, Terminator}};

pub struct ConstBranch;
impl MirPass for ConstBranch {
    fn name(&self) -> &str {
        "Constant-Branching"
    }
    fn run_pass(&self, _:&TypeContext, body:&mut Body){
        let mut patch = Patch::new();
        'a : for (block_id,block) in body.blocks.index_value_iter(){
            if let Terminator::Switch(Operand::Constant(constant),targets,else_branch) = block.expect_terminator(){
                if let Some(const_value) = constant.eval_to_scalar(){
                    for &(target,target_block) in targets{
                        if const_value == target{
                            patch.add_terminator(block_id, Terminator::Goto(target_block));
                            continue 'a;
                        }
                    }
                    patch.add_terminator(block_id, Terminator::Goto(*else_branch));
                }
            }
            
            if let Terminator::Assert(Operand::Constant(constant),_,target) = block.expect_terminator(){
                if let Some(const_value) = constant.eval_to_scalar(){
                    if const_value == 1{
                        patch.add_terminator(block_id, Terminator::Goto(*target));
                    }
                }
            }
        }
        patch.apply(body);
    }
}