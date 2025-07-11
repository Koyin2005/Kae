use crate::{
    frontend::{
        parsing::ast::{
            ConstantExpr, ConstantExprKind, FunctionSig, ParsedGenericParam, ParsedMethod,
            ParsedParam, Symbol,
        },
        tokenizing::{
            SourceLocation,
            tokens::{Token, TokenKind},
        },
    },
    identifiers::SymbolInterner,
};

use super::ast::{
    EnumDef, EnumVariant, ExprNode, ExprNodeKind, FuncDef, FunctionProto, Impl, InferPath,
    InferPathKind, Item, LiteralKind, NodeId, ParsedBinaryOp, ParsedFunction, ParsedGenericArgs,
    ParsedGenericParams, ParsedLogicalOp, ParsedPatternNode, ParsedPatternNodeKind, ParsedUnaryOp,
    Path, PathSegment, PatternMatchArmNode, StmtNode, StructDef, Type,
};

#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Precedence {
    None = 0,
    Assignment,
    Or,
    And,
    Equality,
    Comparison,
    Term,
    Factor,
    Unary,
    Call,
    Primary,
}
impl Precedence {
    pub fn next(self) -> Precedence {
        match self {
            Precedence::None => Precedence::None,
            Precedence::Primary => Precedence::Primary,
            _ => unsafe { std::mem::transmute::<u8, Precedence>(self as u8 + 1) },
        }
    }
}
pub struct ParsingFailed;
pub struct Parser<'a> {
    tokens: Vec<Token<'a>>,
    current_token: Token<'a>,
    prev_token: Token<'a>,
    current_index: usize,
    had_error: bool,
    interner: &'a mut SymbolInterner,
    current_node: NodeId,
}
impl<'a> Parser<'a> {
    pub fn new(tokens: Vec<Token<'a>>, interner: &'a mut SymbolInterner) -> Self {
        Self {
            current_token: tokens[0],
            prev_token: tokens[0],
            tokens,
            current_index: 0,
            had_error: false,
            current_node: NodeId::FIRST,
            interner,
        }
    }
    fn next_id(&mut self) -> NodeId {
        let id = self.current_node;
        self.current_node = self.current_node.next();
        id
    }
    fn is_at_end(&self) -> bool {
        self.current_token.kind == TokenKind::Eof
    }
    fn advance(&mut self) {
        self.prev_token = self.current_token;
        if !self.is_at_end() && self.current_index < self.tokens.len() - 1 {
            self.current_index += 1;
            self.current_token = self.tokens[self.current_index];
        }
    }
    fn check(&self, kind: TokenKind) -> bool {
        self.current_token.kind == kind
    }
    fn matches(&mut self, kind: TokenKind) -> bool {
        if self.current_token.kind == kind {
            self.advance();
            true
        } else {
            false
        }
    }
    fn error_at_current(&mut self, message: &str) {
        self.error_at(self.current_token, message);
    }
    fn error(&mut self, message: &str) {
        self.error_at(self.prev_token, message);
    }
    fn error_at(&mut self, token: Token, message: &str) {
        eprint!("Error on [line {}] ", token.line);
        match token.kind {
            TokenKind::Eof => eprint!("at end "),
            _ => eprint!("at '{}'", token.lexeme),
        }
        eprintln!(": {message}");
        self.had_error = true;
    }
    fn expect(&mut self, kind: TokenKind, message: &str) {
        if !self.matches(kind) {
            self.error_at_current(message);
        }
    }
    fn new_symbol(&mut self, text: String, span: SourceLocation) -> Symbol {
        Symbol {
            content: self.interner.intern(text),
            location: span,
        }
    }
    fn parse_identifer(&mut self, error_message: &str) -> Symbol {
        self.expect(TokenKind::Identifier, error_message);
        self.new_symbol(
            self.prev_token.lexeme.to_string(),
            SourceLocation::one_line(self.prev_token.line),
        )
    }
    fn unary(&mut self) -> Result<ExprNode, ParsingFailed> {
        let op = match self.prev_token.kind {
            TokenKind::Minus => ParsedUnaryOp::Negate,
            _ => unreachable!(),
        };
        let line = self.prev_token.line;

        let operand = self.parse_precedence(Precedence::Unary)?;
        Ok(ExprNode {
            id: self.next_id(),
            location: SourceLocation::one_line(line),
            kind: ExprNodeKind::Unary {
                op,
                operand: Box::new(operand),
            },
        })
    }
    fn grouping(&mut self) -> Result<ExprNode, ParsingFailed> {
        let start_line = self.prev_token.line;
        let kind = if self.check(TokenKind::RightParen) {
            ExprNodeKind::Tuple(Vec::new())
        } else {
            let expression = self.expression()?;
            if self.check(TokenKind::Coma) {
                let mut elements = vec![expression];
                while self.matches(TokenKind::Coma)
                    && !self.check(TokenKind::RightParen)
                    && !self.is_at_end()
                {
                    elements.push(self.expression()?);
                }
                ExprNodeKind::Tuple(elements)
            } else {
                ExprNodeKind::Grouping(Box::new(expression))
            }
        };
        self.expect(TokenKind::RightParen, "Expect ')'.");
        let end_line = self.prev_token.line;
        Ok(ExprNode {
            id: self.next_id(),
            location: SourceLocation::new(start_line, end_line),
            kind,
        })
    }
    fn parse_int(&mut self) -> Result<(SourceLocation, i64), ParsingFailed> {
        let value = self.prev_token.lexeme.parse().map_err(|_| {
            self.error("Int literal is too big.");
            ParsingFailed
        })?;
        Ok((SourceLocation::one_line(self.prev_token.line), value))
    }
    fn int(&mut self) -> Result<ExprNode, ParsingFailed> {
        let (location, value) = self.parse_int()?;
        Ok(ExprNode {
            id: self.next_id(),
            location,
            kind: ExprNodeKind::Literal(LiteralKind::Int(value)),
        })
    }
    fn float(&mut self) -> Result<ExprNode, ParsingFailed> {
        Ok(ExprNode {
            id: self.next_id(),
            location: SourceLocation::one_line(self.prev_token.line),
            kind: ExprNodeKind::Literal(LiteralKind::Float(
                self.prev_token
                    .lexeme
                    .parse()
                    .expect("Can only have valid floats"),
            )),
        })
    }
    fn logical(&mut self, left: ExprNode) -> Result<ExprNode, ParsingFailed> {
        let op_line = self.prev_token.line;
        let (op, precedence) = match self.prev_token.kind {
            TokenKind::And => (ParsedLogicalOp::And, Precedence::And),
            TokenKind::Or => (ParsedLogicalOp::Or, Precedence::Or),
            _ => unreachable!(),
        };
        let right = self.parse_precedence(precedence)?;
        Ok(ExprNode {
            id: self.next_id(),
            location: SourceLocation::one_line(op_line),
            kind: ExprNodeKind::Logical {
                op,
                left: Box::new(left),
                right: Box::new(right),
            },
        })
    }
    fn binary(&mut self, left: ExprNode) -> Result<ExprNode, ParsingFailed> {
        let op_line = self.prev_token.line;
        let kind = match self.prev_token.kind {
            TokenKind::Plus => ParsedBinaryOp::Add,
            TokenKind::Minus => ParsedBinaryOp::Subtract,
            TokenKind::Slash => ParsedBinaryOp::Divide,
            TokenKind::Star => ParsedBinaryOp::Multiply,
            TokenKind::Lesser => ParsedBinaryOp::Lesser,
            TokenKind::Greater => ParsedBinaryOp::Greater,
            TokenKind::LesserEquals => ParsedBinaryOp::LesserEquals,
            TokenKind::GreaterEquals => ParsedBinaryOp::GreaterEquals,
            TokenKind::EqualsEquals => ParsedBinaryOp::Equals,
            TokenKind::BangEquals => ParsedBinaryOp::NotEquals,
            _ => unreachable!(),
        };
        let right = self.parse_precedence(self.precedence_of(self.prev_token.kind).next())?;
        Ok(ExprNode {
            id: self.next_id(),
            location: SourceLocation::one_line(op_line),
            kind: ExprNodeKind::BinaryOp {
                op: kind,
                left: Box::new(left),
                right: Box::new(right),
            },
        })
    }
    fn bool(&mut self, is_true: bool) -> Result<ExprNode, ParsingFailed> {
        Ok(ExprNode {
            id: self.next_id(),
            location: SourceLocation::one_line(self.prev_token.line),
            kind: ExprNodeKind::Literal(LiteralKind::Bool(is_true)),
        })
    }
    fn string(&mut self) -> Result<ExprNode, ParsingFailed> {
        Ok(ExprNode {
            id: self.next_id(),
            location: SourceLocation::one_line(self.prev_token.line),
            kind: ExprNodeKind::Literal(LiteralKind::String(String::from(
                &self.prev_token.lexeme[1..self.prev_token.lexeme.len() - 1],
            ))),
        })
    }
    fn array(&mut self) -> Result<ExprNode, ParsingFailed> {
        let start_line = self.prev_token.line;
        let mut elements = Vec::new();
        while !self.check(TokenKind::RightBracket) && !self.is_at_end() {
            elements.push(self.expression()?);
            if !self.matches(TokenKind::Coma) {
                break;
            }
        }
        self.expect(TokenKind::RightBracket, "Expect ']'.");
        let end_line = self.prev_token.line;
        Ok(ExprNode {
            id: self.next_id(),
            location: SourceLocation::new(start_line, end_line),
            kind: ExprNodeKind::Array(elements),
        })
    }
    fn instantiate(&mut self, lhs: ExprNode) -> Result<ExprNode, ParsingFailed> {
        let start_line = self.prev_token.line;
        let args = self.parse_generic_args()?;
        let end_line = self.prev_token.line;
        Ok(ExprNode {
            id: self.next_id(),
            location: SourceLocation::new(start_line, end_line),
            kind: ExprNodeKind::Instantiate {
                lhs: Box::new(lhs),
                args,
            },
        })
    }
    fn call(&mut self, callee: ExprNode) -> Result<ExprNode, ParsingFailed> {
        let start_line = self.prev_token.line;
        let args = if self.check(TokenKind::RightParen) {
            Vec::new()
        } else {
            let mut args = Vec::new();
            loop {
                args.push(self.expression()?);
                if !self.matches(TokenKind::Coma) {
                    break args;
                }
            }
        };
        self.expect(TokenKind::RightParen, "Expect ')' after args.");
        let end_line = self.prev_token.line;
        let kind = match callee.kind {
            ExprNodeKind::Property(receiver, field) => ExprNodeKind::MethodCall {
                receiver,
                method: PathSegment {
                    name: field,
                    generic_args: None,
                    location: field.location,
                },
                args,
            },
            ExprNodeKind::Instantiate {
                lhs,
                args: generic_args,
            } => match lhs.kind {
                ExprNodeKind::Property(receiver, field) => ExprNodeKind::MethodCall {
                    receiver,
                    method: PathSegment {
                        name: field,
                        generic_args: Some(generic_args),
                        location: lhs.location,
                    },
                    args,
                },
                kind => ExprNodeKind::Call {
                    callee: Box::new(ExprNode {
                        id: self.next_id(),
                        location: callee.location,
                        kind: ExprNodeKind::Instantiate {
                            lhs: Box::new(ExprNode {
                                location: lhs.location,
                                id: lhs.id,
                                kind,
                            }),
                            args: generic_args,
                        },
                    }),
                    args,
                },
            },
            _ => ExprNodeKind::Call {
                callee: Box::new(ExprNode {
                    id: self.next_id(),
                    location: callee.location,
                    kind: callee.kind,
                }),
                args,
            },
        };
        Ok(ExprNode {
            id: self.next_id(),
            location: SourceLocation::new(start_line, end_line),
            kind,
        })
    }
    fn if_expression(&mut self) -> Result<ExprNode, ParsingFailed> {
        let if_start = self.prev_token.line;
        self.expect(TokenKind::LeftParen, "Expect '(' after 'if'.");
        let condition = self.expression()?;
        self.expect(TokenKind::RightParen, "Expect ')' after 'if' condition.");
        let then = self.expression()?;
        let else_ = if self.matches(TokenKind::Else) {
            Some(self.expression()?)
        } else {
            None
        };
        let end_line = self.prev_token.line;
        Ok(ExprNode {
            id: self.next_id(),
            location: SourceLocation::new(if_start, end_line),
            kind: ExprNodeKind::If {
                condition: Box::new(condition),
                then_branch: Box::new(then),
                else_branch: else_.map(Box::new),
            },
        })
    }
    fn block(&mut self) -> Result<ExprNode, ParsingFailed> {
        let start_line = self.prev_token.line;
        let mut had_error = false;
        let mut stmts = Vec::new();
        let mut result_expr = None;
        while !self.is_at_end() && !self.check(TokenKind::RightBrace) {
            if let Some(stmt) = self.try_non_expr_stmt() {
                let Ok(stmt) = stmt else {
                    had_error = true;
                    continue;
                };
                stmts.push(stmt);
            } else {
                let Ok(expr) = self.expression() else {
                    had_error = true;
                    continue;
                };
                if self.check(TokenKind::RightBrace) {
                    result_expr = Some(expr);
                } else if Self::needs_semi_for_stmt(&expr) {
                    let had_semi = self.check(TokenKind::Semicolon);
                    self.expect(TokenKind::Semicolon, "Expect ';' after expression.");
                    if !had_semi {
                        had_error = true;
                        continue;
                    }
                    stmts.push(StmtNode::Expr {
                        expr,
                        has_semi: true,
                    });
                } else {
                    stmts.push(StmtNode::Expr {
                        expr,
                        has_semi: false,
                    });
                }
            }
        }
        self.expect(TokenKind::RightBrace, "Expect '}'.");
        let end_line = self.prev_token.line;
        if !had_error {
            Ok(ExprNode {
                id: self.next_id(),
                location: SourceLocation::new(start_line, end_line),
                kind: ExprNodeKind::Block {
                    stmts,
                    expr: result_expr.map(Box::new),
                },
            })
        } else {
            Err(ParsingFailed)
        }
    }
    fn call_args(&mut self) -> Result<Vec<ExprNode>, ParsingFailed> {
        let mut args = Vec::new();
        while !self.check(TokenKind::RightParen) && !self.is_at_end() {
            args.push(self.expression()?);
            if !self.matches(TokenKind::Coma) {
                break;
            }
        }
        self.expect(TokenKind::RightParen, "Expect ')'.");
        Ok(args)
    }
    fn intern_symbol(&mut self, text: String, span: SourceLocation) -> Symbol {
        Symbol {
            content: self.interner.intern(text),
            location: span,
        }
    }
    fn symbol_to_path(&mut self, symbol: Symbol) -> Path {
        Path {
            segments: vec![PathSegment {
                name: symbol,
                generic_args: None,
                location: symbol.location,
            }],
            location: symbol.location,
        }
    }
    fn struct_expr_fields(&mut self) -> Result<Vec<(Symbol, ExprNode)>, ParsingFailed> {
        let mut fields = Vec::new();
        while !self.check(TokenKind::RightBrace) && !self.is_at_end() {
            self.expect(TokenKind::Identifier, "Expect a valid field name.");

            let field_name = self.prev_token;
            let field_expr = if self.matches(TokenKind::Colon) {
                self.expression()?
            } else {
                let span = SourceLocation::one_line(field_name.line);
                ExprNode {
                    id: self.next_id(),
                    location: span,
                    kind: ExprNodeKind::GetPath({
                        let symbol = self.intern_symbol(field_name.lexeme.to_string(), span);
                        self.symbol_to_path(symbol).into()
                    }),
                }
            };
            fields.push((
                self.intern_symbol(
                    field_name.lexeme.to_string(),
                    SourceLocation::one_line(field_name.line),
                ),
                field_expr,
            ));
            if !self.matches(TokenKind::Coma) {
                break;
            }
        }
        self.expect(TokenKind::RightBrace, "Expect '}' after struct fields.");
        Ok(fields)
    }
    fn name(&mut self) -> Result<ExprNode, ParsingFailed> {
        let (location, kind) = if self.prev_token.kind == TokenKind::Dot {
            let start = self.prev_token.line;
            let name = self.parse_identifer("Expected an indentifier.");
            let location = SourceLocation::new(start, name.location.end_line);
            (location, InferPathKind::Infer(Some(name)))
        } else if self.prev_token.kind == TokenKind::Wildcard {
            (
                SourceLocation::one_line(self.prev_token.line),
                InferPathKind::Infer(None),
            )
        } else {
            let path = self.parse_path()?;
            (path.location, InferPathKind::Path(path))
        };
        let path = InferPath {
            location,
            infer_path: kind,
        };
        if self.matches(TokenKind::LeftBrace) {
            let start = self.prev_token.line;
            let fields = self.struct_expr_fields()?;
            Ok(ExprNode {
                id: self.next_id(),
                location: SourceLocation::new(start, self.prev_token.line),
                kind: ExprNodeKind::StructInit { path, fields },
            })
        } else {
            Ok(ExprNode {
                id: self.next_id(),
                location,
                kind: ExprNodeKind::GetPath(path),
            })
        }
    }
    fn print(&mut self) -> Result<ExprNode, ParsingFailed> {
        let line = self.prev_token.line;
        self.expect(TokenKind::LeftParen, "Expect '('.");
        let args = self.call_args()?;
        Ok(ExprNode {
            id: self.next_id(),
            location: SourceLocation::new(line, self.prev_token.line),
            kind: ExprNodeKind::Print(args),
        })
    }
    fn parse_generic_args(&mut self) -> Result<ParsedGenericArgs, ParsingFailed> {
        let start = self.prev_token.line;
        let args = if self.check(TokenKind::RightBracket) {
            Vec::new()
        } else {
            let mut args = Vec::new();
            loop {
                args.push(self.parse_type()?);
                if !self.matches(TokenKind::Coma) {
                    break args;
                }
            }
        };
        self.expect(TokenKind::RightBracket, "Expect ']' after generic args.");

        Ok(ParsedGenericArgs {
            location: SourceLocation::new(start, self.prev_token.line),
            types: args,
        })
    }
    fn is_expr_start(&self) -> bool {
        matches!(
            self.current_token.kind,
            TokenKind::Float
                | TokenKind::Int
                | TokenKind::True
                | TokenKind::False
                | TokenKind::While
                | TokenKind::If
                | TokenKind::Print
                | TokenKind::Return
                | TokenKind::Identifier
                | TokenKind::LeftParen
                | TokenKind::LeftBracket
                | TokenKind::Dot
                | TokenKind::Wildcard
                | TokenKind::LowerSelf
                | TokenKind::Bang
                | TokenKind::Minus
                | TokenKind::Fun
        )
    }
    fn parse_function_param(&mut self) -> Result<ParsedParam, ParsingFailed> {
        let param_pattern = self.pattern()?;
        self.expect(TokenKind::Colon, "Expect ':' after param.");
        let param_ty = self.parse_type()?;
        Ok(ParsedParam {
            pattern: param_pattern,
            ty: param_ty,
            by_ref: false,
        })
    }
    fn parse_function_return_type(&mut self) -> Result<Option<Type>, ParsingFailed> {
        self.matches(TokenKind::ThinArrow)
            .then(|| self.parse_type())
            .transpose()
    }
    fn parse_function_prototype(&mut self) -> Result<FunctionProto, ParsingFailed> {
        let name = self.parse_identifer("Expect a valid function name.");
        let generic_params = self.optional_generic_params()?;
        self.expect(TokenKind::LeftParen, "Expected '(' after function name.");
        let sig = self.parse_function_signature()?;
        Ok(FunctionProto {
            name,
            generic_params,
            sig,
        })
    }
    fn parse_function_signature(&mut self) -> Result<FunctionSig, ParsingFailed> {
        let params = self.parse_function_params()?;
        let return_type = self.parse_function_return_type()?;
        Ok(FunctionSig {
            params,
            return_type,
        })
    }
    fn parse_function_body(&mut self) -> Result<ExprNode, ParsingFailed> {
        let body = if self.matches(TokenKind::LeftBrace) {
            self.block()?
        } else {
            self.expect(TokenKind::FatArrow, "Expected '=>'");
            self.expression()?
        };
        Ok(body)
    }
    fn parse_function_params(&mut self) -> Result<Vec<ParsedParam>, ParsingFailed> {
        let params = if self.check(TokenKind::RightParen) {
            Vec::new()
        } else {
            let mut params = Vec::new();
            loop {
                params.push(self.parse_function_param()?);
                if !self.matches(TokenKind::Coma) {
                    break params;
                }
            }
        };
        self.expect(TokenKind::RightParen, "Expect ')'.");
        Ok(params)
    }
    fn function(&mut self, start: u32) -> Result<ExprNode, ParsingFailed> {
        self.expect(TokenKind::LeftParen, "Expect '(' after 'fun'.");
        let sig = self.parse_function_signature()?;
        let body = self.parse_function_body()?;
        let end_line = self.prev_token.line;
        Ok(ExprNode {
            id: self.next_id(),
            location: SourceLocation::new(start, end_line),
            kind: ExprNodeKind::Function(sig, Box::new(body)),
        })
    }
    fn return_expression(&mut self) -> Result<ExprNode, ParsingFailed> {
        let line = self.prev_token.line;
        let expr = if self.is_expr_start() {
            Some(self.expression()?)
        } else {
            None
        };
        let end_line = self.prev_token.line;
        Ok(ExprNode {
            id: self.next_id(),
            location: SourceLocation::new(line, end_line),
            kind: ExprNodeKind::Return(expr.map(Box::new)),
        })
    }
    fn while_expression(&mut self) -> Result<ExprNode, ParsingFailed> {
        let line = self.prev_token.line;
        self.expect(TokenKind::LeftParen, "Expect '('.");
        let condition = self.expression()?;
        self.expect(TokenKind::RightParen, "Expect ')'.");
        let body = self.expression()?;
        Ok(ExprNode {
            id: self.next_id(),
            location: SourceLocation::new(line, body.location.end_line),
            kind: ExprNodeKind::While {
                condition: Box::new(condition),
                body: Box::new(body),
            },
        })
    }
    fn pattern_match(&mut self) -> Result<ExprNode, ParsingFailed> {
        let start = self.prev_token.line;
        self.expect(TokenKind::LeftParen, "Expect '('.");
        let matchee = self.expression()?;
        self.expect(TokenKind::RightParen, "Expect ')'.");
        let mut arms = Vec::new();
        self.expect(TokenKind::LeftBrace, "Expect '{'.");
        while !self.check(TokenKind::RightBrace) && !self.is_at_end() {
            let pattern = self.pattern()?;
            self.expect(TokenKind::FatArrow, "Expect '=>'.");
            let location = SourceLocation::one_line(self.prev_token.line);
            let arm = self.expression()?;
            let needs_coma = Self::needs_semi_for_stmt(&arm);
            arms.push(PatternMatchArmNode {
                id: self.next_id(),
                location,
                pattern,
                expr: arm,
            });
            if !self.matches(TokenKind::Coma) && needs_coma {
                break;
            }
        }
        self.expect(TokenKind::RightBrace, "Expect '}'.");
        Ok(ExprNode {
            id: self.next_id(),
            location: SourceLocation::new(start, self.prev_token.line),
            kind: ExprNodeKind::Match {
                matchee: Box::new(matchee),
                arms,
            },
        })
    }
    fn property(&mut self, left: ExprNode) -> Result<ExprNode, ParsingFailed> {
        let start = self.prev_token.line;
        let property_symbol = if self.matches(TokenKind::Int) {
            self.new_symbol(
                self.prev_token.lexeme.to_string(),
                SourceLocation::one_line(self.prev_token.line),
            )
        } else if self.matches(TokenKind::LeftBracket) {
            let rhs = self.expression()?;
            self.expect(TokenKind::RightBracket, "Expected ']'.");
            return Ok(ExprNode {
                location: SourceLocation::new(start, self.prev_token.line),
                id: self.next_id(),
                kind: ExprNodeKind::Index {
                    lhs: Box::new(left),
                    rhs: Box::new(rhs),
                },
            });
        } else {
            if self.matches(TokenKind::Float) {
                let fields = self.prev_token.lexeme.split(".");
                if fields.clone().all(|field| field.parse::<usize>().is_ok()) {
                    let mut expr = left;
                    for field in fields {
                        let span = SourceLocation::one_line(self.prev_token.line);
                        expr = ExprNode {
                            id: self.next_id(),
                            location: SourceLocation::new(start, self.prev_token.line),
                            kind: ExprNodeKind::Property(
                                Box::new(expr),
                                self.new_symbol(field.to_string(), span),
                            ),
                        };
                    }
                    return Ok(expr);
                }
            }
            self.parse_identifer("Expect valid property name.")
        };
        Ok(ExprNode {
            id: self.next_id(),
            location: SourceLocation::new(start, self.prev_token.line),
            kind: ExprNodeKind::Property(Box::new(left), property_symbol),
        })
    }
    fn assign(&mut self, left: ExprNode) -> Result<ExprNode, ParsingFailed> {
        match &left.kind {
            ExprNodeKind::Property(_, _)
            | ExprNodeKind::GetPath(InferPath {
                location: _,
                infer_path: InferPathKind::Path(_),
            })
            | ExprNodeKind::Index { lhs: _, rhs: _ } => (),
            _ => {
                self.error("Invalid assignment target.");
                return Err(ParsingFailed);
            }
        };
        let lhs = Box::new(left);
        let rhs = self.parse_precedence(Precedence::Assignment)?;
        Ok(ExprNode {
            id: self.next_id(),
            location: SourceLocation::new(lhs.location.start_line, rhs.location.end_line),
            kind: ExprNodeKind::Assign {
                lhs,
                rhs: Box::new(rhs),
            },
        })
    }
    fn needs_semi_for_stmt(expr: &ExprNode) -> bool {
        match &expr.kind {
            ExprNodeKind::If {
                then_branch,
                else_branch,
                ..
            } => {
                Self::needs_semi_for_stmt(then_branch)
                    || else_branch
                        .as_ref()
                        .is_some_and(|else_| Self::needs_semi_for_stmt(else_))
            }
            ExprNodeKind::While { body, .. } => Self::needs_semi_for_stmt(body),
            ExprNodeKind::Block { .. } | ExprNodeKind::Match { .. } => false,
            _ => true,
        }
    }
    fn prefix(&mut self) -> Option<Result<ExprNode, ParsingFailed>> {
        Some(match self.prev_token.kind {
            TokenKind::Minus => self.unary(),
            TokenKind::LeftParen => self.grouping(),
            TokenKind::Int => self.int(),
            TokenKind::Float => self.float(),
            TokenKind::True => self.bool(true),
            TokenKind::False => self.bool(false),
            TokenKind::String => self.string(),
            TokenKind::If => self.if_expression(),
            TokenKind::LeftBrace => self.block(),
            TokenKind::LeftBracket => self.array(),
            TokenKind::Identifier
            | TokenKind::LowerSelf
            | TokenKind::UpperSelf
            | TokenKind::Dot
            | TokenKind::Wildcard => self.name(),
            TokenKind::Print => self.print(),
            TokenKind::Match => self.pattern_match(),
            TokenKind::While => self.while_expression(),
            TokenKind::Fun => self.function(self.prev_token.line),
            TokenKind::Return => self.return_expression(),
            _ => return None,
        })
    }
    fn infix(&mut self, left: ExprNode) -> Result<ExprNode, ParsingFailed> {
        match self.prev_token.kind {
            TokenKind::Plus
            | TokenKind::Minus
            | TokenKind::Slash
            | TokenKind::Star
            | TokenKind::Lesser
            | TokenKind::Greater
            | TokenKind::LesserEquals
            | TokenKind::GreaterEquals
            | TokenKind::EqualsEquals
            | TokenKind::BangEquals => self.binary(left),
            TokenKind::LeftBracket => self.instantiate(left),
            TokenKind::LeftParen => self.call(left),
            TokenKind::Equals => self.assign(left),
            TokenKind::Dot => self.property(left),
            TokenKind::And | TokenKind::Or => self.logical(left),
            _ => unreachable!(),
        }
    }
    fn precedence_of(&self, kind: TokenKind) -> Precedence {
        match kind {
            TokenKind::Plus | TokenKind::Minus => Precedence::Term,
            TokenKind::Star | TokenKind::Slash => Precedence::Factor,
            TokenKind::Lesser
            | TokenKind::Greater
            | TokenKind::LesserEquals
            | TokenKind::GreaterEquals => Precedence::Comparison,
            TokenKind::EqualsEquals | TokenKind::BangEquals => Precedence::Equality,
            TokenKind::LeftBracket | TokenKind::LeftParen | TokenKind::Dot => Precedence::Call,
            TokenKind::Equals => Precedence::Assignment,
            TokenKind::And => Precedence::And,
            TokenKind::Or => Precedence::Or,
            _ => Precedence::None,
        }
    }
    fn parse_precedence(&mut self, precedence: Precedence) -> Result<ExprNode, ParsingFailed> {
        self.advance();
        let Some(mut expr) = self.prefix() else {
            self.error("Expected expression.");
            return Err(ParsingFailed);
        };
        while precedence <= self.precedence_of(self.current_token.kind) {
            self.advance();
            expr = self.infix(expr?);
        }
        expr
    }
    fn expression(&mut self) -> Result<ExprNode, ParsingFailed> {
        self.parse_precedence(Precedence::Assignment)
    }

    fn parse_constant(&mut self) -> Result<ConstantExpr, ParsingFailed> {
        Ok(if self.matches(TokenKind::Int) {
            let value = self.prev_token.lexeme.parse().map_err(|_| {
                self.error("Int literal is too big.");
                ParsingFailed
            })?;
            ConstantExpr {
                location: SourceLocation::one_line(self.prev_token.line),
                kind: ConstantExprKind::Int(value),
            }
        } else {
            let constant = self.parse_identifer("Expected a valid constant.");
            ConstantExpr {
                location: SourceLocation::one_line(self.prev_token.line),
                kind: ConstantExprKind::Constant(constant.content),
            }
        })
    }
    fn parse_type(&mut self) -> Result<Type, ParsingFailed> {
        Ok(
            if self.matches(TokenKind::Identifier) || self.matches(TokenKind::UpperSelf) {
                let path = self.parse_path()?;
                Type::Path(path)
            } else if self.matches(TokenKind::LeftBracket) {
                let start = self.prev_token.line;
                let ty = self.parse_type()?;
                self.expect(TokenKind::Coma, "Expected ',' after array element type");
                let constant = self.parse_constant()?;
                self.expect(TokenKind::RightBracket, "Expect ']'.");
                let end = self.prev_token.line;
                Type::Array(SourceLocation::new(start, end), Box::new(ty), constant)
            } else if self.matches(TokenKind::LeftParen) {
                let start = self.prev_token.line;
                let mut elements = Vec::new();
                while !self.check(TokenKind::RightParen) && !self.is_at_end() {
                    elements.push(self.parse_type()?);
                    if !self.matches(TokenKind::Coma) {
                        break;
                    }
                }
                self.expect(TokenKind::RightParen, "Expect ')'.");
                let end = self.prev_token.line;
                Type::Tuple(SourceLocation::new(start, end), elements)
            } else if self.matches(TokenKind::Fun) {
                let start = self.prev_token.line;
                self.expect(TokenKind::LeftParen, "Expect '(' after 'fun'.");
                let params = if self.check(TokenKind::RightParen) {
                    Vec::new()
                } else {
                    let mut params = Vec::new();
                    loop {
                        params.push(self.parse_type()?);
                        if !self.matches(TokenKind::Coma) {
                            break params;
                        }
                    }
                };
                self.expect(TokenKind::RightParen, "Expect ')' after parameter types.");
                let return_type = if self.matches(TokenKind::ThinArrow) {
                    Some(self.parse_type()?)
                } else {
                    None
                };
                let end = self.prev_token.line;
                Type::Fun(
                    SourceLocation::new(start, end),
                    params,
                    return_type.map(Box::new),
                )
            } else {
                self.error_at_current("Invalid type.");
                return Err(ParsingFailed);
            },
        )
    }
    fn parse_path_segment(&mut self) -> Result<PathSegment, ParsingFailed> {
        let name = self.prev_token;
        let generic_args = if self.matches(TokenKind::LeftBracket) {
            let generic_args = self.parse_generic_args()?;
            Some(generic_args)
        } else {
            None
        };
        let name = self.intern_symbol(name.lexeme.to_string(), SourceLocation::one_line(name.line));
        Ok(PathSegment {
            location: SourceLocation::new(name.location.start_line, self.prev_token.line),
            name,
            generic_args,
        })
    }
    fn parse_path(&mut self) -> Result<Path, ParsingFailed> {
        let head = self.parse_path_segment()?;
        let start = head.location;
        let mut segments = vec![head];
        while self.matches(TokenKind::DoubleColon) {
            self.expect(
                TokenKind::Identifier,
                "Expected valid name for path segment.",
            );
            segments.push(self.parse_path_segment()?);
        }
        Ok(Path {
            location: SourceLocation::new(start.start_line, self.prev_token.line),
            segments,
        })
    }
    fn pattern(&mut self) -> Result<ParsedPatternNode, ParsingFailed> {
        let starts_with_dot = self.matches(TokenKind::Dot);
        let (location, kind) = if starts_with_dot
            || self.matches(TokenKind::Identifier)
            || self.check(TokenKind::Wildcard)
        {
            let path = if starts_with_dot {
                let start = self.prev_token.line;
                let name = self.parse_identifer("Expected identifier after '.'");
                InferPath {
                    location: SourceLocation::new(start, name.location.end_line),
                    infer_path: InferPathKind::Infer(Some(name)),
                }
            } else if self.matches(TokenKind::Wildcard) {
                InferPath {
                    location: SourceLocation::one_line(self.prev_token.line),
                    infer_path: InferPathKind::Infer(None),
                }
            } else {
                let path = self.parse_path()?;
                InferPath {
                    location: path.location,
                    infer_path: InferPathKind::Path(path),
                }
            };
            if self.matches(TokenKind::LeftBrace) {
                let mut fields = Vec::new();
                while !self.check(TokenKind::RightBrace) && !self.is_at_end() {
                    let field_name = self.parse_identifer("Expect valid field name.");
                    let field_pattern = if self.matches(TokenKind::Colon) {
                        self.pattern()?
                    } else {
                        ParsedPatternNode {
                            id: self.next_id(),
                            location: field_name.location,
                            kind: ParsedPatternNodeKind::Name(field_name.content),
                        }
                    };
                    fields.push((field_name, field_pattern));
                    if !self.matches(TokenKind::Coma) {
                        break;
                    }
                }
                self.expect(TokenKind::RightBrace, "Expect '}'.");
                (
                    SourceLocation::new(path.location.start_line, self.prev_token.line),
                    ParsedPatternNodeKind::Struct { path, fields },
                )
            } else if self.matches(TokenKind::LeftParen) {
                let mut fields = Vec::new();
                while !self.check(TokenKind::RightParen) && !self.is_at_end() {
                    let field_pattern = self.pattern()?;
                    fields.push(field_pattern);
                    if !self.matches(TokenKind::Coma) {
                        break;
                    }
                }
                self.expect(TokenKind::RightParen, "Expect ')'.");
                (
                    SourceLocation::new(path.location.start_line, self.prev_token.line),
                    ParsedPatternNodeKind::TupleStruct(path, fields),
                )
            } else {
                match path.infer_path {
                    InferPathKind::Infer(infer) => {
                        if let Some(symbol) = infer {
                            (path.location, ParsedPatternNodeKind::Infer(symbol))
                        } else {
                            (path.location, ParsedPatternNodeKind::Wildcard)
                        }
                    }
                    InferPathKind::Path(path) => match path.segments.as_slice() {
                        [head] => {
                            if head.generic_args.is_none() {
                                if self.matches(TokenKind::Is) {
                                    let pattern = self.pattern()?;
                                    (
                                        head.location,
                                        ParsedPatternNodeKind::Is(head.name, Box::new(pattern)),
                                    )
                                } else {
                                    (
                                        head.location,
                                        ParsedPatternNodeKind::Name(head.name.content),
                                    )
                                }
                            } else {
                                (path.location, ParsedPatternNodeKind::Path(path))
                            }
                        }
                        _ => (path.location, ParsedPatternNodeKind::Path(path)),
                    },
                }
            }
        } else if self.matches(TokenKind::LeftParen) {
            let start = self.prev_token.line;
            let kind = if self.check(TokenKind::RightParen) {
                ParsedPatternNodeKind::Tuple(Vec::new())
            } else {
                let pattern = self.pattern()?;
                if self.matches(TokenKind::Coma) {
                    let mut patterns = vec![pattern];
                    while !self.check(TokenKind::RightParen) && !self.is_at_end() {
                        patterns.push(self.pattern()?);
                        if !self.matches(TokenKind::Coma) {
                            break;
                        }
                    }
                    ParsedPatternNodeKind::Tuple(patterns)
                } else {
                    pattern.kind
                }
            };
            self.expect(TokenKind::RightParen, "Expect ')'.");
            (SourceLocation::new(start, self.prev_token.line), kind)
        } else if self.matches(TokenKind::Int) {
            (
                SourceLocation::one_line(self.prev_token.line),
                ParsedPatternNodeKind::Literal(LiteralKind::Int(
                    self.prev_token.lexeme.parse().expect("Int token"),
                )),
            )
        } else if self.matches(TokenKind::Float) {
            (
                SourceLocation::one_line(self.prev_token.line),
                ParsedPatternNodeKind::Literal(LiteralKind::Float(
                    self.prev_token.lexeme.parse().expect("Float token"),
                )),
            )
        } else if self.matches(TokenKind::String) {
            (
                SourceLocation::one_line(self.prev_token.line),
                ParsedPatternNodeKind::Literal(LiteralKind::String(
                    self.prev_token.lexeme[1..self.prev_token.lexeme.len() - 1].to_string(),
                )),
            )
        } else if self.matches(TokenKind::True) {
            (
                SourceLocation::one_line(self.prev_token.line),
                ParsedPatternNodeKind::Literal(LiteralKind::Bool(
                    self.prev_token
                        .lexeme
                        .parse()
                        .expect("Should be a true token"),
                )),
            )
        } else if self.matches(TokenKind::False) {
            (
                SourceLocation::one_line(self.prev_token.line),
                ParsedPatternNodeKind::Literal(LiteralKind::Bool(
                    self.prev_token
                        .lexeme
                        .parse()
                        .expect("Should be a false token"),
                )),
            )
        } else {
            self.error_at_current("Expected a valid pattern.");
            return Err(ParsingFailed);
        };
        Ok(ParsedPatternNode {
            id: self.next_id(),
            location,
            kind,
        })
    }
    fn let_stmt(&mut self) -> Result<StmtNode, ParsingFailed> {
        let pattern = self.pattern()?;
        let ty = if self.matches(TokenKind::Colon) {
            Some(self.parse_type()?)
        } else {
            None
        };
        self.expect(TokenKind::Equals, "Expect '='.");
        let expr = self.expression()?;
        self.expect(TokenKind::Semicolon, "Expect ';'.");
        Ok(StmtNode::Let {
            id: self.next_id(),
            pattern,
            expr,
            ty,
        })
    }
    fn optional_generic_params(&mut self) -> Result<Option<ParsedGenericParams>, ParsingFailed> {
        if self.matches(TokenKind::LeftBracket) {
            Ok(Some(self.parse_generic_params()?))
        } else {
            Ok(None)
        }
    }
    fn parse_generic_params(&mut self) -> Result<ParsedGenericParams, ParsingFailed> {
        fn parse_generic_param(this: &mut Parser) -> Result<ParsedGenericParam, ParsingFailed> {
            let (name, ty) = if this.matches(TokenKind::Const) {
                let name = this.parse_identifer("Expect valid generic parameter name.");
                this.expect(TokenKind::Colon, "Expected a ':' after const param.");
                (name, Some(this.parse_type()?))
            } else {
                (
                    this.parse_identifer("Expect valid generic parameter name."),
                    None,
                )
            };
            Ok(ParsedGenericParam(name, ty))
        }
        let id = self.next_id();
        let params = if self.check(TokenKind::RightBracket) {
            Vec::new()
        } else {
            let mut params = Vec::new();
            loop {
                let param = parse_generic_param(self)?;
                params.push(param);
                if !self.matches(TokenKind::Coma) {
                    break params;
                }
            }
        };
        self.expect(
            TokenKind::RightBracket,
            "Expect ']' after generic parameters.",
        );
        Ok(ParsedGenericParams(id, params))
    }
    fn parse_enum_variant(&mut self) -> Result<EnumVariant, ParsingFailed> {
        let variant_name = self.parse_identifer("Expect valid enum variant name.");
        let mut fields = Vec::new();
        if self.matches(TokenKind::LeftParen) {
            while !self.check(TokenKind::RightParen) && !self.is_at_end() {
                fields.push(self.parse_type()?);
                if !self.matches(TokenKind::Coma) {
                    break;
                }
            }
            self.expect(TokenKind::RightParen, "Expected ')'.");
        }
        Ok(EnumVariant {
            name: variant_name,
            fields,
        })
    }
    fn enum_stmt(&mut self) -> Result<EnumDef, ParsingFailed> {
        let name = self.parse_identifer("Expect valid enum name.");
        let generic_params = self.optional_generic_params()?;
        self.expect(TokenKind::LeftBrace, "Expect '{'.");
        let mut variants = Vec::new();
        while !self.check(TokenKind::RightBrace) && !self.is_at_end() {
            let enum_variant = self.parse_enum_variant()?;
            variants.push(enum_variant);
            if !self.matches(TokenKind::Coma) {
                break;
            }
        }
        self.expect(TokenKind::RightBrace, "Expect '}'.");
        Ok(EnumDef {
            id: self.next_id(),
            name,
            generic_params,
            variants,
        })
    }
    fn parse_struct_field(&mut self) -> Result<(Symbol, Type), ParsingFailed> {
        self.expect(TokenKind::Identifier, "Expect valid field name.");
        let field_name = self.prev_token;
        self.expect(TokenKind::Colon, "Expect ':' after field.");
        let field_type = self.parse_type()?;
        Ok((
            self.intern_symbol(
                field_name.lexeme.to_string(),
                SourceLocation::one_line(field_name.line),
            ),
            field_type,
        ))
    }
    fn struct_stmt(&mut self) -> Result<StructDef, ParsingFailed> {
        self.expect(TokenKind::Identifier, "Expect valid structure name.");
        let name = self.intern_symbol(
            self.prev_token.lexeme.to_string(),
            SourceLocation::one_line(self.prev_token.line),
        );

        let generic_params = self.optional_generic_params()?;
        self.expect(TokenKind::LeftBrace, "Expect '{'.");
        let mut fields = vec![];
        while !self.check(TokenKind::RightBrace) && !self.is_at_end() {
            fields.push(self.parse_struct_field()?);
            if !self.matches(TokenKind::Coma) {
                break;
            }
        }
        self.expect(TokenKind::RightBrace, "Expect '}'.");
        Ok(StructDef {
            id: self.next_id(),
            name,
            generic_params,
            fields,
        })
    }
    fn fun_stmt(&mut self) -> Result<FuncDef, ParsingFailed> {
        let proto = self.parse_function_prototype()?;
        let body = self.parse_function_body()?;
        Ok(FuncDef {
            id: self.next_id(),
            function: ParsedFunction { proto, body },
        })
    }
    fn parse_method_prototype(&mut self) -> Result<(FunctionProto, bool), ParsingFailed> {
        #[derive(Clone, Copy, PartialEq, Eq)]
        enum SelfParam {
            ByRef,
            ByValue,
        }
        let name = self.parse_identifer("Expected a method name.");
        let generic_params = self.optional_generic_params()?;
        self.expect(TokenKind::LeftParen, "Expect '(' after method name.");
        let mut params = Vec::new();
        let mut has_self = false;
        while !self.check(TokenKind::RightParen) && !self.is_at_end() {
            let self_param = if self.matches(TokenKind::Ref) {
                self.expect(
                    TokenKind::LowerSelf,
                    "Expected 'self' parameter after 'ref'.",
                );
                Some(SelfParam::ByRef)
            } else {
                self.matches(TokenKind::LowerSelf)
                    .then_some(SelfParam::ByValue)
            };
            let param = if let Some(self_param) = self_param {
                if params.len() > 1 {
                    self.error("Can only have 1 'self' parameter as first parameter.");
                    return Err(ParsingFailed);
                }
                has_self = true;
                let self_name = self.intern_symbol(
                    self.prev_token.lexeme.to_string(),
                    SourceLocation::one_line(self.prev_token.line),
                );
                ParsedParam {
                    pattern: ParsedPatternNode {
                        id: self.next_id(),
                        location: self_name.location,
                        kind: ParsedPatternNodeKind::Name(self_name.content),
                    },
                    ty: Type::Path(Path {
                        segments: vec![PathSegment {
                            name: self.intern_symbol("Self".to_string(), self_name.location),
                            location: self_name.location,
                            generic_args: None,
                        }],
                        location: name.location,
                    }),
                    by_ref: self_param == SelfParam::ByRef,
                }
            } else {
                self.parse_function_param()?
            };
            params.push(param);
            if !self.matches(TokenKind::Coma) {
                break;
            }
        }
        self.expect(TokenKind::RightParen, "Expect ')'.");
        let return_type = self.parse_function_return_type()?;
        Ok((
            FunctionProto {
                name,
                generic_params,
                sig: FunctionSig {
                    params,
                    return_type,
                },
            },
            has_self,
        ))
    }
    fn parse_method(&mut self) -> Result<(ParsedFunction, bool), ParsingFailed> {
        let (proto, has_receiver) = self.parse_method_prototype()?;
        let body = self.parse_function_body()?;
        Ok((ParsedFunction { proto, body }, has_receiver))
    }
    fn impl_stmt(&mut self) -> Result<Impl, ParsingFailed> {
        let start_line = self.current_token.line;

        let (ty, generic_params) = {
            let name = self.parse_identifer("Expected a valid type name.");
            let generic_params = self.optional_generic_params()?;
            if let Some(generic_params) = generic_params {
                (
                    Type::Path(Path {
                        segments: vec![PathSegment {
                            generic_args: Some(ParsedGenericArgs {
                                location: name.location,
                                types: generic_params
                                    .1
                                    .iter()
                                    .map(|&ParsedGenericParam(name, _)| {
                                        Type::Path(Path {
                                            segments: vec![name.into()],
                                            location: name.location,
                                        })
                                    })
                                    .collect(),
                            }),
                            ..name.into()
                        }],
                        location: name.location,
                    }),
                    Some(generic_params),
                )
            } else {
                (
                    Type::Path(Path {
                        segments: vec![name.into()],
                        location: name.location,
                    }),
                    None,
                )
            }
        };
        self.expect(TokenKind::LeftBrace, "Expect '{' after impl type.");

        let mut methods = Vec::new();
        while !self.check(TokenKind::RightBrace) && !self.is_at_end() {
            self.expect(TokenKind::Fun, "Expected 'fun'.");
            let id = self.next_id();
            let (method, has_receiver) = self.parse_method()?;
            methods.push(ParsedMethod {
                id,
                has_receiver,
                function: method,
            });
        }
        self.expect(TokenKind::RightBrace, "Expect '}'.");
        let end_line = self.current_token.line;
        Ok(Impl {
            id: self.next_id(),
            span: SourceLocation {
                start_line,
                end_line,
            },
            ty,
            generic_params,
            methods,
        })
    }
    fn try_item(&mut self) -> Option<Result<Item, ParsingFailed>> {
        Some(
            if self.matches(TokenKind::Fun) && self.check(TokenKind::Identifier) {
                self.fun_stmt().map(Item::Fun)
            } else if self.matches(TokenKind::Struct) {
                self.struct_stmt().map(Item::Struct)
            } else if self.matches(TokenKind::Enum) {
                self.enum_stmt().map(Item::Enum)
            } else if self.matches(TokenKind::Impl) {
                self.impl_stmt().map(Item::Impl)
            } else {
                return None;
            },
        )
    }
    fn try_non_expr_stmt(&mut self) -> Option<Result<StmtNode, ParsingFailed>> {
        Some(if self.matches(TokenKind::Let) {
            self.let_stmt()
        } else if let Some(item) = self.try_item() {
            item.map(StmtNode::Item)
        } else {
            return None;
        })
    }
    fn synchronize(&mut self) {
        loop {
            if self.matches(TokenKind::Semicolon)
                || self.matches(TokenKind::RightBrace)
                || self.is_at_end()
            {
                break;
            }
            self.advance();
        }
    }
    pub fn parse(mut self) -> Result<Vec<Item>, ParsingFailed> {
        let mut items = Vec::new();
        while !self.is_at_end() {
            let Some(item) = self.try_item() else {
                self.error("Expected an item.");
                self.synchronize();
                continue;
            };
            let Ok(item) = item else {
                self.had_error = true;
                self.synchronize();
                continue;
            };
            items.push(item);
        }
        if !self.had_error {
            Ok(items)
        } else {
            Err(ParsingFailed)
        }
    }
}
