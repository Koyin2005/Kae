use crate::{data_structures::IntoIndex, frontend::{ast_lowering::hir, typechecking::{context::TypeContext, types::{format::TypeFormatter, AdtKind, Type}}}, middle::mir::AssertKind, SymbolInterner};

use super::{Block, BlockId, Body, ConstantKind, FunctionKind, Mir, Operand, Place, PlaceProjection, RValue, Stmt, Terminator};


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
        let mut output = format!("_{}",lvalue.local.as_index());
        for projection in &lvalue.projections{
            match projection{
                PlaceProjection::Field(field_index) => {
                    output.push_str(&format!(".{}",field_index.as_index()));
                },
                PlaceProjection::Variant(name,_) => {
                    output = format!("({output} as {})",self.symbol_interner.get(*name));
                },
                PlaceProjection::Index(local) => {
                    output.push_str(&format!("[_{}]",local.as_index()));
                }
            }
        }
        output
    }
    fn debug_operand(&self, operand: &Operand) -> String{
        match operand{
            Operand::Constant(constant) => {
                match &constant.kind{
                    ConstantKind::Bool(value) => value.to_string(),
                    ConstantKind::Int(value) => value.to_string(),
                    ConstantKind::String(index) => format!("\"{}\"",self.symbol_interner.get(*index)),
                    ConstantKind::ZeroSized => TypeFormatter::new(self.symbol_interner, self.context).format_type(&constant.ty),
                    ConstantKind::Function(kind,generic_args) => {
                        let name = match kind {
                            FunctionKind::Anon(_) => "anonymous".to_string(),
                            FunctionKind::Normal(id) => self.symbol_interner.get(self.context.ident(*id).index).to_string(),
                            FunctionKind::Variant(id) => {
                                let base = self.symbol_interner.get(self.context.ident(self.context.expect_owner_of(*id)).index);
                                format!("{}::{}",base, self.symbol_interner.get(self.context.ident(*id).index))
                            },
                            FunctionKind::Builtin(builtin) => match builtin{
                                hir::BuiltinKind::Panic => "panic"
                            }.to_string()
                        };
                        format!("{}{}",name,TypeFormatter::new(self.symbol_interner, self.context).format_generic_args(generic_args))
                        
                    }
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
            RValue::Len(operand) => format!("len {}",self.debug_lvalue(operand)),
            RValue::Tag(operand) => format!("tag {}",self.debug_lvalue(operand)),
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
                output.push_str(&format!(" {} ",op));
                output.push_str(&self.debug_operand(right));
                output
            },
            RValue::Unary(op,operand) => {
                format!("{}{}",op.to_string(),self.debug_operand(operand))
            },
            RValue::Adt(adt,operands) => {
                let &(id,ref generic_args,variant) = adt.as_ref();
                match variant{
                    Some(variant) => {
                        let mut output = TypeFormatter::new(self.symbol_interner, self.context).format_type(&Type::new_adt(generic_args.clone(), id,AdtKind::Enum));
                        let id = self.context.get_variant_by_index(id, variant).id;
                        output.push_str(&format!("::{}",self.symbol_interner.get(self.context.expect_variant(id).name.index)));
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
    fn format_block(&mut self, block_id: BlockId,block:&Block){
        self.push_next_line(&format!("bb{}",block_id.as_index()));
        self.increase_indent_level();
        for stmt in block.stmts.iter(){
            match stmt{
                Stmt::Assign(lvalue,rvalue) => {
                    self.push_next_line(&format!("{} = {};",self.debug_lvalue(lvalue),self.debug_rvalue(rvalue)));
                },
                Stmt::Print(operands) => {
                    let mut output = "print".to_string();
                    output.push('(');
                    let mut first = true;
                    for arg in operands{
                        if !first{
                            output.push(',');
                        }
                        output.push_str(&self.debug_operand(arg));
                        first = false;
                    }
                    output.push(')');
                    output.push(';');
                    self.push_next_line(&output);

                }
                Stmt::Nop => self.push_next_line("nop"),
            }
        }
        if let Some(terminator) = block.terminator.as_ref(){
            match terminator{
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
                },
                Terminator::Assert(operand,kind,next) => {
                    self.push_next_line(&format!("assert({}, {}) -> {}",self.debug_operand(operand),match kind{
                        AssertKind::ArrayBoundsCheck(index,len) => {
                           format!("\"Index out of range, index was {{}} but len was {{}}\". {}, {}",self.debug_operand(index),self.debug_operand(len))
                        }
                    },next));
                }
            }
        }
        self.decrease_indent_level();
    }
    fn format_body(&mut self,body:&Body){
        let name = self.context.format_full_path(body.source.id, self.symbol_interner);
        let mut first_line = format!("fun {}(",name);
        let mut first = true;
        for (i,ty) in body.source.params.iter().enumerate(){
            if !first{
                first_line.push(',');
            }
            first_line.push_str(&format!("_{}:{}",i+1,TypeFormatter::new(self.symbol_interner, self.context).format_type(ty)));
            first = false;
        }
        first_line.push_str(&format!(") -> {}",TypeFormatter::new(self.symbol_interner,self.context).format_type(&body.source.return_type)));
        self.push_next_line(&first_line);
        for (id,block) in body.blocks.index_value_iter(){
            self.increase_indent_level();
            self.format_block(id,block);
            self.decrease_indent_level();
        }
        self.output.push('\n');
    }
    pub fn debug(mut self) -> String{
        for body in self.mir.bodies.iter(){
            self.format_body(body);
        }
        self.output
    }
}