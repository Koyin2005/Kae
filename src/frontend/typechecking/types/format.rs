use crate::{frontend::typechecking::{context::TypeContext, types::ConstantSize}, identifiers::SymbolInterner};

use super::{Type, generics::GenericArgs};

pub struct TypeFormatter<'a> {
    interner: &'a SymbolInterner,
    context: &'a TypeContext<'a>,
}
impl<'b> TypeFormatter<'b> {
    pub fn new(interner: &'b SymbolInterner, context: &'b TypeContext) -> Self {
        Self { interner, context }
    }

    fn format_types<'a>(&self, types: impl Iterator<Item = &'a Type>, buffer: &mut String) {
        for (i, ty) in types.enumerate() {
            if i > 0 {
                buffer.push(',');
            }
            self.format(ty, buffer);
        }
    }
    fn format(&self, ty: &Type, buffer: &mut String) {
        match ty {
            Type::Bool => buffer.push_str("bool"),
            Type::Float => buffer.push_str("float"),
            Type::Int => buffer.push_str("int"),
            Type::Never => buffer.push_str("never"),
            Type::String => buffer.push_str("string"),
            Type::Error => buffer.push('_'),
            &Type::Param(_, symbol) => {
                buffer.push_str(self.interner.get(symbol));
            }
            Type::Array(element_type, size) => {
                buffer.push('[');
                self.format(element_type, buffer);
                buffer.push(',');
                match size{
                    ConstantSize::Constant(_,name) => {
                        buffer.push_str(self.interner.get(*name));
                    },
                    ConstantSize::Value(value) => {
                        buffer.push_str(&value.into_size().to_string());
                    },
                    ConstantSize::Error => {
                        buffer.push('_');
                    }
                }
                buffer.push(']');
            }
            Type::Function(args, return_type) => {
                buffer.push_str("fun(");
                self.format_types(args.iter(), buffer);
                buffer.push_str(")->");
                self.format(return_type, buffer);
            }
            Type::Tuple(element_types) => {
                buffer.push('(');
                self.format_types(element_types.iter(), buffer);
                buffer.push(')');
            }
            &Type::Adt(ref args, id, _) => {
                buffer.push_str(self.interner.get(self.context.ident(id).index));
                if !args.is_empty() {
                    buffer.push('[');
                    self.format_types(args.iter(), buffer);
                    buffer.push(']');
                }
            }
        }
    }

    pub fn format_type(&mut self, ty: &Type) -> String {
        let mut buffer = String::new();
        self.format(ty, &mut buffer);
        buffer
    }
    pub fn format_generic_args(&mut self, args: &GenericArgs) -> String {
        let mut buffer = String::new();
        if !args.is_empty() {
            buffer.push('[');
            self.format_types(args.iter(), &mut buffer);
            buffer.push(']');
        }
        buffer
    }
}
