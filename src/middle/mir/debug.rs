use crate::{data_structures::IntoIndex, frontend::typechecking::{context::TypeContext, types::{format::TypeFormatter, AdtKind, Type}}, SymbolInterner};

use super::{Block, Body, Constant, Mir, Operand, Place, PlaceProjection, RValue, Stmt, Terminator};


pub struct DebugMir<'a>{
    mir : &'a Mir,
    output : String,
    symbol_interner : &'a SymbolInterner,
    context : &'a TypeContext,
    indents : usize
}

impl<'a> DebugMir<'a>{
    pub fn new(mir: &'a Mir, context: &'a TypeContext, symbol_interner: &'a SymbolInterner) -> Self{
        Self{mir,context,output:String::new(),symbol_interner,indents:0}
    }

    fn push_next_line(&mut self, line: &str){
        for _ in 0..self.indents{
            self.output.push(' ');
        }
        self.output.push_str(line);
        self.output.push('\n');
    }
    fn increase_indent_level(&mut self) {
        self.indents += 1;
    }
    fn decrease_indent_level(&mut self) {
        self.indents -= 1;
    }

    fn debug_lvalue(&self, lvalue: &Place) -> String{
        let mut output = format!("l{}",lvalue.local.as_index());
        for projection in &lvalue.projections{
            match projection{
                PlaceProjection::Field(field_index) => {
                    output.push_str(&format!(".{}",field_index.as_index()));
                },
                PlaceProjection::Variant(name,_) => {
                    output = format!("({output} as {})",self.symbol_interner.get(*name));
                },
                PlaceProjection::Index(local) => {
                    output.push_str(&format!("[l{}]",local.as_index()));
                }
            }
        }
        output
    }
    fn debug_operand(&self, operand: &Operand) -> String{
        match operand{
            Operand::Constant(constant) => {
                match constant{
                    Constant::Bool(value) => value.to_string(),
                    Constant::Int(value) => value.to_string(),
                    Constant::String(index) => self.symbol_interner.get(*index).to_string(),
                }
            },
            Operand::Load(place) => {
                format!("load {}",self.debug_lvalue(place))
            }
        }
    }
    fn debug_rvalue(&self, rvalue: &RValue) -> String{
        match rvalue{
            RValue::Use(operand) => self.debug_operand(operand),
            RValue::Call(callee,args) => {
                let mut output = self.debug_operand(callee);
                output.push('(');
                let mut first = true;
                for arg in args{
                    if !first{
                        output.push(',');
                    }
                    output.push_str(&self.debug_operand(arg));
                    first = false;
                }
                output.push(')');
                output
            },
            RValue::Binary(op,left_and_right) => {
                let (left,right) = left_and_right.as_ref();
                let mut output = String::new();
                output.push_str(&self.debug_operand(left));
                output.push_str(&op.to_string());
                output.push_str(&self.debug_operand(right));
                output
            },
            RValue::Unary(op,operand) => {
                format!("{} {}",op.to_string(),self.debug_operand(operand))
            },
            RValue::Adt(adt,operands) => {
                let &(id,ref generic_args,variant) = adt.as_ref();
                match variant{
                    Some(_) => {
                        let mut output = TypeFormatter::new(self.symbol_interner, self.context).format_type(&Type::new_adt(generic_args.clone(), id,AdtKind::Enum));
                        output.push_str(&format!("{}",self.symbol_interner.get(self.context.expect_variant(id).name.index)));
                        let mut first = true;
                        output.push('(');
                        for operand in  operands.iter(){
                            if !first{
                                output.push(',');
                            }
                            output.push_str(&self.debug_operand(operand));
                            first = false;
                        }
                        output.push(')');
                        output
                    },
                    None => {
                        let mut output = TypeFormatter::new(self.symbol_interner, self.context).format_type(&Type::new_adt(generic_args.clone(), id,AdtKind::Struct));
                        output.push('{');
                        let mut first = true;
                        for (field_name,operand) in  operands.index_value_iter().map(|(index,operand)|{
                            (self.symbol_interner.get(self.context.expect_struct(id).fields[index.as_index() as usize].name.index),operand)
                        }){
                            if !first{
                                output.push(',');
                            }
                            output.push_str(&format!("{} : {}",field_name,self.debug_operand(operand)));
                            first = false;
                        }
                        output.push('}');
                        output
                    }
                }
            },
            RValue::Array(elements) => {
                if elements.is_empty(){
                    "[]".to_string()
                }
                else{
                    let mut output = String::from('[');
                    let mut first = true;
                    for element in elements{
                        if !first{
                            output.push(',');
                        }   
                        first = false;
                        output.push_str(&self.debug_operand(element));
                    };
                    output.push(']');
                    output
                }
            },
            RValue::Tuple(elements) => {
                if elements.is_empty(){
                    "()".to_string()
                }
                else{
                    let mut output = String::from('(');
                    let mut first = true;
                    for element in elements{
                        if !first{
                            output.push(',');
                        }   
                        first = false;
                        output.push_str(&self.debug_operand(element));
                    };
                    output.push(')');
                    output
                }
            }
        }
    }
    fn format_block(&mut self,block:&Block){
        for stmt in block.stmts.iter(){
            match stmt{
                Stmt::Assign(lvalue,rvalue) => {
                    self.push_next_line(&format!("{} = {};",self.debug_lvalue(lvalue),self.debug_rvalue(rvalue)));
                },
                Stmt::Nop => ()
            }
        }
        match &block.terminator{
            Terminator::Switch(operand,branches,otherwise) => {
                let mut output = format!("switch {} -> {{",self.debug_operand(operand));
                let mut first = true;
                for (value,branch) in branches{
                    if !first{
                        output.push(',');
                    }
                    output.push_str(&format!("{} : {}",value,branch));
                    first = false;
                }
                output.push(',');
                output.push_str(&format!("otherwise : {}",otherwise));
                output.push('}');
                self.push_next_line(&output);
            },
            Terminator::Return => {
                self.push_next_line("return");
            },
            Terminator::Unreachable => {
                self.push_next_line("unreachable");
            },
            Terminator::Goto(block) => {
                self.push_next_line(&format!("goto -> {}",block));
            }
        }
    }
    fn format_body(&mut self,body:&Body){
        for (i,block) in body.blocks.iter().enumerate(){
            if i>0{
                self.output.push('\n');
            }
            self.increase_indent_level();
            self.format_block(block);
            self.decrease_indent_level();
        }
    }
    pub fn debug(mut self) -> String{
        for body in self.mir.bodies.iter(){
            self.format_body(body);
        }
        self.output
    }
}