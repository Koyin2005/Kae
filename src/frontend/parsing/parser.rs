use crate::frontend::{parsing::ast::{ParsedGenericParam, ParsedParam, Symbol}, tokenizing::{tokens::{Token, TokenKind}, SourceLocation}};

use super::ast::{ExprNode, ExprNodeKind, LiteralKind, ParsedAssignmentTarget, ParsedAssignmentTargetKind, ParsedBinaryOp, ParsedFunction, ParsedGenericArgs, ParsedGenericParams, ParsedLogicalOp, ParsedPatternNode, ParsedPatternNodeKind, ParsedType, ParsedUnaryOp, PatternMatchArmNode, StmtNode};

#[repr(u8)]
#[derive(Clone, Copy,PartialEq, Eq, PartialOrd, Ord)]
pub enum Precedence {
    None = 0, 
    Assignment,
    Or,
    And,
    Equality,
    Comparison,
    Term,
    Factor,
    Call,
    Unary,
    Primary
}
impl Precedence{
    pub fn next(self)->Precedence{
        match self{
            Precedence::None => Precedence::None,
            Precedence::Primary => Precedence::Primary,
             _ => unsafe{std::mem::transmute::<u8,Precedence>(self as u8 + 1)}
        }
    }
}
pub struct ParsingFailed;
pub struct Parser<'a>{
    tokens : Vec<Token<'a>>,
    current_token : Token<'a>,
    prev_token : Token<'a>,
    current_index : usize,
    had_error : bool
}
impl<'a> Parser<'a>{
    pub fn new(tokens:Vec<Token<'a>>)->Self{
        Self{
            current_token : tokens[0],
            prev_token : tokens[0] ,
            tokens,
            current_index:0,
            had_error:false
        }
    }
    fn is_at_end(&self)->bool{
        self.current_token.kind == TokenKind::Eof
    }
    fn advance(&mut self){
        self.prev_token = self.current_token;
        if !self.is_at_end() && self.current_index < self.tokens.len()-1{
            self.current_index += 1;
            self.current_token = self.tokens[self.current_index];
        }
    }
    fn check(&self,kind : TokenKind) -> bool{
        self.current_token.kind == kind
    }
    fn matches(&mut self,kind : TokenKind) -> bool{
        if self.current_token.kind == kind {
            self.advance();
            true
        }
        else{
            false
        }
    }
    fn error_at_current(&mut self,message:&str){
        self.error_at(self.current_token, message);
    }
    fn error(&mut self,message:&str){
        self.error_at(self.prev_token, message);
    }
    fn error_at(&mut self,token : Token,message:&str){
        eprint!("Error on [line {}] ",token.line);
        match token.kind{
            TokenKind::Eof => eprint!("at end "),
            _ => eprint!("at '{}'",token.lexeme)
        }
        eprintln!(": {}",message);
        self.had_error = true;
    }
    fn expect(&mut self,kind : TokenKind,message:&str){
        if !self.matches(kind){
            self.error_at_current(message);
        }
    }
    fn unary(&mut self)->Result<ExprNode,ParsingFailed>{
        let op = match self.prev_token.kind {
            TokenKind::Minus => ParsedUnaryOp::Negate,
            _ => unreachable!()
        };
        let line = self.prev_token.line;

        let operand = self.parse_precedence(Precedence::Unary)?;
        Ok(ExprNode{location:SourceLocation::one_line(line),kind: ExprNodeKind::Unary{op,operand:Box::new(operand)}})
    }
    fn grouping(&mut self)->Result<ExprNode,ParsingFailed>{
        
        let start_line = self.prev_token.line;
        let kind = if self.check(TokenKind::RightParen){
            ExprNodeKind::Tuple(Vec::new())
        }
        else{
            let expression = self.expression()?;
            if self.check(TokenKind::Coma){
                let mut elements = vec![expression];
                while self.matches(TokenKind::Coma) && !self.check(TokenKind::RightParen) && !self.is_at_end()   {
                    elements.push(self.expression()?);
                }
                ExprNodeKind::Tuple(elements)
            } else {
                ExprNodeKind::Grouping(Box::new(expression)) 
            }
        };
        self.expect(TokenKind::RightParen, "Expect ')'.");
        let end_line = self.prev_token.line;
        Ok(ExprNode { location:SourceLocation::new(start_line,end_line), kind})
    }
    fn int(&mut self)->Result<ExprNode,ParsingFailed>{
        Ok(ExprNode { location:SourceLocation::one_line(self.prev_token.line), kind: ExprNodeKind::Literal(LiteralKind::Int(self.prev_token.lexeme.parse().expect("Can only have valid ints"))) })
    }
    fn float(&mut self)->Result<ExprNode,ParsingFailed>{

        Ok(ExprNode { location:SourceLocation::one_line(self.prev_token.line), kind: ExprNodeKind::Literal(LiteralKind::Float(self.prev_token.lexeme.parse().expect("Can only have valid floats"))) })
    
    }
    fn logical(&mut self,left:ExprNode)->Result<ExprNode,ParsingFailed>{
        let op_line = self.prev_token.line;
        let (op,precedence) = match self.prev_token.kind{
            TokenKind::And => {
               (ParsedLogicalOp::And,Precedence::And)
            },
            TokenKind::Or => {
                (ParsedLogicalOp::Or,Precedence::Or)
            },
            _ => unreachable!()
        };
        let right = self.parse_precedence(precedence)?;
        Ok(ExprNode { location: SourceLocation::one_line(op_line), kind: ExprNodeKind::Logical { op, left: Box::new(left), right: Box::new(right) } })
    }
    fn binary(&mut self,left:ExprNode)->Result<ExprNode,ParsingFailed>{
        let op_line = self.prev_token.line;
        let kind = match self.prev_token.kind{
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
            _ => unreachable!()
        };
        let right = self.parse_precedence(self.precedence_of(self.prev_token.kind).next())?;
        Ok(ExprNode { location:SourceLocation::one_line(op_line), kind: ExprNodeKind::BinaryOp { op:kind, left: Box::new(left), right: Box::new(right) } })

    }
    fn bool(&mut self,is_true:bool)->Result<ExprNode,ParsingFailed>{
        Ok(ExprNode { location: SourceLocation::one_line(self.prev_token.line), kind: ExprNodeKind::Literal(LiteralKind::Bool(is_true)) })
    }
    fn string(&mut self)->Result<ExprNode,ParsingFailed>{
        Ok(ExprNode { location: SourceLocation::one_line(self.prev_token.line), kind: ExprNodeKind::Literal(LiteralKind::String(String::from(&self.prev_token.lexeme[1..self.prev_token.lexeme.len()-1]))) })
    }
    fn array(&mut self)->Result<ExprNode,ParsingFailed>{
        let start_line = self.prev_token.line;
        let mut elements = Vec::new();
        while !self.check(TokenKind::RightBracket) && !self.is_at_end(){
            elements.push(self.expression()?);
            if !self.matches(TokenKind::Coma){
                break;
            }
        } 
        self.expect(TokenKind::RightBracket, "Expect ']'.");
        let end_line = self.prev_token.line;
        Ok(ExprNode { location:SourceLocation::new(start_line, end_line), kind: ExprNodeKind::Array(elements) })
    }
    fn index(&mut self,lhs : ExprNode)->Result<ExprNode,ParsingFailed>{
        let start_line = self.prev_token.line;
        let rhs = self.expression()?;
        self.expect(TokenKind::RightBracket, "Expect ']'.");
        let end_line = self.prev_token.line;
        Ok(ExprNode { location:SourceLocation::new(start_line,end_line), kind: ExprNodeKind::Index { lhs:Box::new(lhs), rhs: Box::new(rhs) } })
    }
    fn call(&mut self,receiver:ExprNode)->Result<ExprNode,ParsingFailed>{
        let start_line = self.prev_token.line;
        let args = if self.check(TokenKind::RightParen){ Vec::new() } else {
            let mut args = Vec::new();
            loop{
                args.push(self.expression()?);
                if !self.matches(TokenKind::Coma){
                    break args;
                }
            }
        };
        self.expect(TokenKind::RightParen, "Expect ')' after args.");
        let end_line = self.prev_token.line;
        Ok(ExprNode { location: SourceLocation::new(start_line,end_line), kind: ExprNodeKind::Call { callee: Box::new(receiver), args } })
    }
    fn if_expression(&mut self)->Result<ExprNode,ParsingFailed>{
        let if_start = self.prev_token.line;
        self.expect(TokenKind::LeftParen, "Expect '(' after 'if'.");
        let condition = self.expression()?;
        self.expect(TokenKind::RightParen, "Expect ')' after 'if' condition.");
        let then = self.expression()?;
        let else_ = if self.matches(TokenKind::Else){
            Some(self.expression()?)
        } else {
            None
        };
        let end_line = self.prev_token.line;
        Ok(ExprNode { location: SourceLocation::new(if_start, end_line), kind: ExprNodeKind::If { condition: Box::new(condition), then_branch: Box::new(then), else_branch: else_.map(Box::new) } })
    }
    fn block(&mut self)->Result<ExprNode,ParsingFailed>{
        let start_line = self.prev_token.line;
        let mut had_error = false;
        let mut stmts = Vec::new();
        let mut result_expr = None;
        while !self.is_at_end() && !self.check(TokenKind::RightBrace){
            if let Some(stmt) = self.try_non_expr_stmt(){
                let Ok(stmt) = stmt else {
                    had_error = true;
                    continue;
                };
                stmts.push(stmt);
            }
            else{
                let Ok(expr) = self.expression() else {
                    had_error = true;
                    continue;
                };
                if self.check(TokenKind::RightBrace){
                    result_expr = Some(expr);
                }
                else if Self::needs_semi_for_stmt(&expr){
                    let had_semi = self.check(TokenKind::Semicolon);
                    self.expect(TokenKind::Semicolon, "Expect ';' after expression.");
                    if !had_semi{
                        had_error = true;
                        continue;
                    }
                    stmts.push(StmtNode::Expr { expr, has_semi:true });
                }
                else{
                    stmts.push(StmtNode::Expr { expr, has_semi: false });
                }
            }
        }
        self.expect(TokenKind::RightBrace, "Expect '}'.");
        let end_line = self.prev_token.line;
        if !had_error { Ok(ExprNode { location:SourceLocation::new(start_line, end_line) , kind: ExprNodeKind::Block { stmts, expr: result_expr.map(Box::new) } })} else {Err(ParsingFailed)}
    }
    fn call_args(&mut self)-> Result<Vec<ExprNode>,ParsingFailed>{
        let mut args = Vec::new();
        while !self.check(TokenKind::RightParen) && !self.is_at_end(){
            args.push(self.expression()?);
            if !self.matches(TokenKind::Coma){
                break;
            }
        }
        self.expect(TokenKind::RightParen, "Expect ')'.");
        Ok(args)
    }
    fn name(&mut self)->Result<ExprNode,ParsingFailed>{
        let line = self.prev_token.line;
        let name = self.prev_token.lexeme;
        let generic_args = if self.matches(TokenKind::Colon) {
            let generic_args = self.parse_generic_args()?;
            Some(generic_args)
        }
        else {
            None
        };
        if self.matches(TokenKind::LeftBrace) {
            let start = self.prev_token.line;
            let mut fields = Vec::new();
            while !self.check(TokenKind::RightBrace) && !self.is_at_end(){
                self.expect(TokenKind::Identifier, "Expect a valid field name.");
                
                let field_name = self.prev_token;
                let field_expr = if self.matches(TokenKind::Colon){
                    self.expression()?
                }
                else{
                    ExprNode{
                        location : SourceLocation::one_line(field_name.line),
                        kind : ExprNodeKind::Get(field_name.lexeme.to_string())
                    }
                };
                fields.push((Symbol{content:field_name.lexeme.to_string(),location:SourceLocation::one_line(field_name.line)},field_expr));
                if !self.matches(TokenKind::Coma) {
                    break;
                }
            }
            self.expect(TokenKind::RightBrace, "Expect '}' after struct fields.");
            Ok(ExprNode { 
                    location: SourceLocation::new(start, self.prev_token.line),
                    kind: ExprNodeKind::StructInit { name: Symbol { content: name.to_string(), location: SourceLocation::one_line(line) }, generic_args, fields } 
                })
        }
        else{
            if let Some(generic_args) = generic_args{
                Ok(ExprNode{
                    location:SourceLocation::new(line, generic_args.location.end_line),
                    kind:ExprNodeKind::GetGeneric(name.to_string(), generic_args)
                })
            }
            else{
                self.variable()
            }
        }
        
    }
    fn variable(&self)->Result<ExprNode,ParsingFailed>{
        Ok(ExprNode { location: SourceLocation::one_line(self.prev_token.line), kind: ExprNodeKind::Get(self.prev_token.lexeme.to_string()) })
    }
    fn typename(&mut self) -> Result<ExprNode,ParsingFailed>{
        let line = self.prev_token.line;
        self.expect(TokenKind::LeftParen, "Expect '('.");
        let ty = self.parse_type();
        self.expect(TokenKind::RightParen, "Expect ')'.");
        Ok(ExprNode { location: SourceLocation::new(line, self.prev_token.line), kind: ExprNodeKind::TypenameOf(ty?) })
    }
    fn print(&mut self) -> Result<ExprNode,ParsingFailed>{
        let line = self.prev_token.line;
        self.expect(TokenKind::LeftParen, "Expect '('.");
        let args = self.call_args()?;
        Ok(ExprNode { location: SourceLocation::new(line, self.prev_token.line), kind: ExprNodeKind::Print(args) })
    }
    fn parse_generic_args(&mut self) -> Result<ParsedGenericArgs,ParsingFailed>{
        let start = self.prev_token.line;
        self.expect(TokenKind::LeftBracket, "Expect '[' after ':'.");
        let args = if self.check(TokenKind::RightBracket) {
            Vec::new()
        }
        else{
            let mut args = Vec::new();
            loop{
                args.push(self.parse_type()?);
                if !self.matches(TokenKind::Coma){
                    break args;
                }
            }
        };
        self.expect(TokenKind::RightBracket, "Expect ']' after generic args.");
        
        Ok(ParsedGenericArgs { location: SourceLocation::new(start, self.prev_token.line), types: args })
    }
    fn is_expr_start(&self)->bool{
        matches!(self.current_token.kind,TokenKind::Float|TokenKind::Int|TokenKind::True|TokenKind::False
                |TokenKind::While|TokenKind::If| TokenKind::Print| TokenKind::Return|
                TokenKind::Identifier|TokenKind::LeftParen| TokenKind::LeftBracket |
                TokenKind::Bang| TokenKind::Minus | TokenKind::Fun)
    }
    fn parse_function(&mut self)->Result<ParsedFunction,ParsingFailed>{
        let params = if self.check(TokenKind::RightParen) { Vec::new() } else {
            let mut params = Vec::new();
            loop{
                let pattern = self.pattern()?;
                self.expect(TokenKind::Colon, "Expect ':'.");
                let ty = self.parse_type()?;

                params.push(ParsedParam{
                    pattern,
                    ty
                });
                if !self.matches(TokenKind::Coma){
                    break params;
                }
            }
        };
        self.expect(TokenKind::RightParen, "Expect ')'.");
        let return_type = if self.matches(TokenKind::ThinArrow){
            Some(self.parse_type()?)
        } else {
            None
        };
        let body = if self.matches(TokenKind::LeftBrace){self.block()? }else{
            let expr = self.expression()?;
            if Self::needs_semi_for_stmt(&expr){
                self.expect(TokenKind::Semicolon, "Expected ';'.");
            }
            expr
        };
        Ok(ParsedFunction{
                    params,
                    return_type,
                    body
        }) 
            
    }
    fn function(&mut self,start:u32)->Result<ExprNode,ParsingFailed>{
        self.expect(TokenKind::LeftParen, "Expect '(' after 'fun'.");
        let function = self.parse_function()?;
        let end_line = self.prev_token.line;
        Ok(ExprNode { 
            location: SourceLocation::new(start, end_line), 
            kind: ExprNodeKind::Function(Box::new(
                    function
                )) 
        })

    }
    fn return_expression(&mut self)->Result<ExprNode,ParsingFailed>{
        let line = self.prev_token.line;
        let expr = if self.is_expr_start(){
            Some(self.expression()?)
        } else {
            None
        };
        let end_line = self.prev_token.line;
        Ok(ExprNode { location: SourceLocation::new(line, end_line), kind: ExprNodeKind::Return(expr.map(Box::new)) })
    }
    fn while_expression(&mut self)->Result<ExprNode,ParsingFailed>{
        let line = self.prev_token.line;
        self.expect(TokenKind::LeftParen, "Expect '('.");
        let condition = self.expression()?;
        self.expect(TokenKind::RightParen, "Expect ')'.");
        let body = self.expression()?;
        Ok(ExprNode { location: SourceLocation::new(line,body.location.end_line), kind: ExprNodeKind::While { condition: Box::new(condition), body: Box::new(body) } })
    }
    fn pattern_match(&mut self)->Result<ExprNode,ParsingFailed>{
        let start = self.prev_token.line;
        self.expect(TokenKind::LeftParen, "Expect '('.");
        let matchee = self.expression()?;
        self.expect(TokenKind::RightParen, "Expect ')'.");
        let mut arms = Vec::new();
        self.expect(TokenKind::LeftBrace, "Expect '{'.");
        while !self.check(TokenKind::RightBrace) && !self.is_at_end(){
            let pattern = self.pattern()?;
            self.expect(TokenKind::FatArrow, "Expect '=>'.");
            let location = SourceLocation::one_line(self.prev_token.line);
            let arm = self.expression()?;
            arms.push(PatternMatchArmNode{
                location,
                pattern,
                expr:arm
            });
            if !self.matches(TokenKind::Coma){
                break;
            }
        }
        self.expect(TokenKind::RightBrace, "Expect '}'.");
        Ok(ExprNode { location: SourceLocation::new(start, self.prev_token.line), kind: ExprNodeKind::Match { matchee:Box::new(matchee), arms} })
    }
    fn property(&mut self,left:ExprNode)->Result<ExprNode,ParsingFailed>{
        let start = self.prev_token.line;
        self.expect(TokenKind::Identifier, "Expect a valid identifier.");
        Ok(ExprNode { location: SourceLocation::new(start, self.prev_token.line), kind: ExprNodeKind::Property(Box::new(left), Symbol { content: self.prev_token.lexeme.to_string(), location: SourceLocation::one_line(self.prev_token.line) }) })
    }
    fn assign(&mut self,left:ExprNode)->Result<ExprNode,ParsingFailed>{
        let assignment_target_kind = match left.kind{
            ExprNodeKind::Index { lhs, rhs } => {
                ParsedAssignmentTargetKind::Index { lhs, rhs }
            },
            ExprNodeKind::Get(name) => {
                ParsedAssignmentTargetKind::Name(name)
            },
            _ => {
                self.error("Invalid assignment target.");
                return Err(ParsingFailed);
            },
        };
        let lhs = ParsedAssignmentTarget{
            location:left.location,
            kind : assignment_target_kind
        };
        let rhs = self.parse_precedence(Precedence::Assignment)?;
        Ok(ExprNode { location: SourceLocation::new(lhs.location.start_line, rhs.location.end_line), kind: ExprNodeKind::Assign { lhs, rhs:Box::new(rhs) } })
    }
    fn needs_semi_for_stmt(expr:&ExprNode)->bool{
        match &expr.kind{
            ExprNodeKind::If {  then_branch, else_branch,.. } => {
                Self::needs_semi_for_stmt(then_branch) ||  else_branch.as_ref().is_some_and(|else_| Self::needs_semi_for_stmt(else_))
            },
            ExprNodeKind::While {body ,..} => {
                Self::needs_semi_for_stmt(body)
            },
            ExprNodeKind::Block { .. } | ExprNodeKind::Match {.. } => false,
            _ => true
        }
    }
    fn prefix(&mut self)->Option<Result<ExprNode,ParsingFailed>>{
         Some(match self.prev_token.kind{
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
            TokenKind::Identifier => self.name(),
            TokenKind::Print => self.print(),
            TokenKind::Match => self.pattern_match(),
            TokenKind::While => self.while_expression(),
            TokenKind::Fun => self.function(self.prev_token.line),
            TokenKind::Return => self.return_expression(),
            TokenKind::Typename => self.typename(),
            _ => return  None
        })
    }
    fn infix(&mut self,left:ExprNode)->Result<ExprNode,ParsingFailed>{
        match self.prev_token.kind{
            TokenKind::Plus | TokenKind::Minus | TokenKind::Slash | TokenKind::Star |
            TokenKind::Lesser | TokenKind::Greater | TokenKind::LesserEquals | TokenKind::GreaterEquals |
            TokenKind::EqualsEquals | TokenKind::BangEquals => {
                self.binary(left)
            },
            TokenKind::LeftBracket => self.index(left),
            TokenKind::LeftParen => self.call(left),
            TokenKind::Equals => self.assign(left),
            TokenKind::Dot => self.property(left),
            TokenKind::And | TokenKind::Or => self.logical(left),
            _ => unreachable!()
        }
    }
    fn precedence_of(&self,kind:TokenKind)-> Precedence{
        match kind{
            TokenKind::Plus | TokenKind::Minus => Precedence::Term,
            TokenKind::Star | TokenKind::Slash => Precedence::Factor,
            TokenKind::Lesser | TokenKind::Greater | TokenKind::LesserEquals | TokenKind::GreaterEquals => Precedence::Comparison,
            TokenKind::EqualsEquals | TokenKind::BangEquals => Precedence::Equality,
            TokenKind::LeftBracket | TokenKind::LeftParen | TokenKind::Dot => Precedence::Call,
            TokenKind::Equals => Precedence::Assignment,
            TokenKind::And => Precedence::And,
            TokenKind::Or => Precedence::Or,
            _ => Precedence::None
        }
    }
    fn parse_precedence(&mut self,precedence:Precedence)->Result<ExprNode,ParsingFailed>{
        self.advance();
        let Some(mut expr) = self.prefix() else {
            self.error("Expected expression.");
            return Err(ParsingFailed);
        };
        while precedence <= self.precedence_of(self.current_token.kind){
            self.advance();
            expr = self.infix(expr?);
        }
        expr
    }
    fn expression(&mut self)->Result<ExprNode,ParsingFailed>{
        self.parse_precedence(Precedence::Assignment)
    }
    fn expression_statement(&mut self)->Result<StmtNode,ParsingFailed>{
        let expression = self.expression()?;
        let has_semi = if Self::needs_semi_for_stmt(&expression){
            self.expect(TokenKind::Semicolon, "Expect ';' after expression.");
            true
        }
        else {
            self.matches(TokenKind::Semicolon)
        };
        Ok(StmtNode::Expr { expr:expression, has_semi })
    }
    fn parse_type(&mut self)->Result<ParsedType,ParsingFailed>{
        Ok(if self.matches(TokenKind::Identifier){
            let name = self.prev_token;
            if self.check(TokenKind::LeftBracket){
                let generic_args = self.parse_generic_args()?;
                ParsedType::NameWithArgs(Symbol{location: SourceLocation::one_line(name.line),content:name.lexeme.to_string()},generic_args)
            }
            else{
                ParsedType::Name(Symbol{location: SourceLocation::one_line(name.line),content:name.lexeme.to_string()})
            }
        }
        else if self.matches(TokenKind::LeftBracket){
            let ty = self.parse_type()?;
            self.expect(TokenKind::RightBracket, "Expect ']'.");
            ParsedType::Array(Box::new(ty))
        }
        else if self.matches(TokenKind::LeftParen){
            let mut elements = Vec::new();
            while !self.check(TokenKind::RightParen) && !self.is_at_end() {
               elements.push(self.parse_type()?);
               if !self.matches(TokenKind::Coma){
                    break;
               }
            }
            self.expect(TokenKind::RightParen, "Expect ')'.");
            ParsedType::Tuple(elements)
        }
        else if self.matches(TokenKind::Fun){
            self.expect(TokenKind::LeftParen, "Expect '(' after 'fun'.");
            let params = if self.check(TokenKind::RightParen) { Vec::new() } else {
                let mut params = Vec::new();
                loop{
                    params.push(self.parse_type()?);
                    if !self.matches(TokenKind::Coma){
                        break params;
                    }
                }
            };
            self.expect(TokenKind::RightParen, "Expect ')' after parameter types.");
            let return_type = if self.matches(TokenKind::ThinArrow){Some(self.parse_type()?)} else {None};
            ParsedType::Fun(params, return_type.map(Box::new))
        }
        else{
            self.error_at_current("Invalid type.");
            return Err(ParsingFailed);
        })
    }
    fn pattern(&mut self)->Result<ParsedPatternNode,ParsingFailed>{
        let (location,kind) = if self.matches(TokenKind::Identifier){
            (SourceLocation::one_line(self.prev_token.line),ParsedPatternNodeKind::Name(self.prev_token.lexeme.to_string()))
        }
        else if self.matches(TokenKind::LeftParen){
            let start = self.prev_token.line;
            let kind = if self.check(TokenKind::RightParen){
                ParsedPatternNodeKind::Tuple(Vec::new())
            }
            else {
                let pattern = self.pattern()?;
                if self.matches(TokenKind::Coma){
                    let mut patterns = vec![pattern];
                    while !self.check(TokenKind::RightParen) && !self.is_at_end(){
                        patterns.push(self.pattern()?);
                        if !self.matches(TokenKind::Coma){
                            break;
                        }
                    }
                    ParsedPatternNodeKind::Tuple(patterns)
                }
                else{
                    pattern.kind
                }
            };
            self.expect(TokenKind::RightParen, "Expect ')'.");
            (SourceLocation::new(start, self.prev_token.line),kind)
        }
        else if self.matches(TokenKind::Int){
            (SourceLocation::one_line(self.prev_token.line),ParsedPatternNodeKind::Literal(LiteralKind::Int(self.prev_token.lexeme.parse().expect("Int token"))))
        }
        else if self.matches(TokenKind::Float){
            (SourceLocation::one_line(self.prev_token.line),ParsedPatternNodeKind::Literal(LiteralKind::Float(self.prev_token.lexeme.parse().expect("Float token"))))
        }
        else if self.matches(TokenKind::String){
            (SourceLocation::one_line(self.prev_token.line),ParsedPatternNodeKind::Literal(LiteralKind::String(self.prev_token.lexeme[1..self.prev_token.lexeme.len()-1].to_string())))
        }
        else if self.matches(TokenKind::True){
            (SourceLocation::one_line(self.prev_token.line),ParsedPatternNodeKind::Literal(LiteralKind::Bool(self.prev_token.lexeme.parse().expect("Should be a true token"))))
        }
        else if self.matches(TokenKind::False){
            (SourceLocation::one_line(self.prev_token.line),ParsedPatternNodeKind::Literal(LiteralKind::Bool(self.prev_token.lexeme.parse().expect("Should be a false token"))))
        }
        else{
            self.error_at_current("Expected a valid pattern.");
            return Err(ParsingFailed);
        };
        Ok(ParsedPatternNode{
            location,
            kind
        })
    }
    fn let_stmt(&mut self)->Result<StmtNode,ParsingFailed>{
        let pattern = self.pattern()?;
        let ty = if self.matches(TokenKind::Colon){
            Some(self.parse_type()?)
        } else { None};
        self.expect(TokenKind::Equals, "Expect '='.");
        let expr = self.expression()?;
        self.expect(TokenKind::Semicolon, "Expect ';'.");
        Ok(StmtNode::Let { pattern, expr ,ty})
    }
    fn parse_generic_params(&mut self)->Result<ParsedGenericParams,ParsingFailed>{
        fn parse_generic_param(this:&mut Parser)->Result<ParsedGenericParam,ParsingFailed>{
            this.expect(TokenKind::Identifier, "Expect valid generic parameter name.");
            Ok(ParsedGenericParam(Symbol { content: this.prev_token.lexeme.to_string(), location: SourceLocation::one_line(this.prev_token.line) }))
        }
        let params = if self.check(TokenKind::RightBracket) { Vec::new() } else {
            let mut params = Vec::new();
            loop{
                let param = parse_generic_param(self)?;
                params.push(param);
                if !self.matches(TokenKind::Coma){
                    break params;
                }
            }
        };
        self.expect(TokenKind::RightBracket, "Expect ']' after generic parameters.");
        Ok(ParsedGenericParams(params))
    }
    fn parse_struct_field(&mut self)->Result<(Symbol,ParsedType),ParsingFailed>{
        self.expect(TokenKind::Identifier, "Expect valid field name.");
        let field_name = self.prev_token;
        self.expect(TokenKind::Colon, "Expect ':' after field.");
        let field_type = self.parse_type()?;
        Ok((Symbol{content:field_name.lexeme.to_string(),location:SourceLocation::one_line(field_name.line)},field_type))
    }
    fn struct_stmt(&mut self)->Result<StmtNode,ParsingFailed>{
        self.expect(TokenKind::Identifier, "Expect valid structure name.");
        let name = Symbol{content:self.prev_token.lexeme.to_string(),location:SourceLocation::one_line(self.prev_token.line)};

        let generic_params = if self.matches(TokenKind::LeftBracket) { Some(self.parse_generic_params()?)} else { None };
        self.expect(TokenKind::LeftBrace, "Expect '{'.");
        let mut fields = vec![];
        while !self.check(TokenKind::RightBrace) && !self.is_at_end(){
            fields.push(self.parse_struct_field()?);
            if !self.matches(TokenKind::Coma){
                break;
            }
        }
        self.expect(TokenKind::RightBrace, "Expect '}'.");
        Ok(StmtNode::Struct { name, generic_params, fields })
    }
    fn fun_stmt(&mut self)->Result<StmtNode,ParsingFailed>{
        self.expect(TokenKind::Identifier, "Expect valid function name.");
        let name = Symbol{content:self.prev_token.lexeme.to_string(),location:SourceLocation::one_line(self.prev_token.line)};
        let generic_params = if self.matches(TokenKind::LeftBracket){Some(self.parse_generic_params()?)} else { None};
        
        self.expect(TokenKind::LeftParen, "Expect '(' after function name.");
        let function = self.parse_function()?;
        Ok(StmtNode::Fun { name,generic_params, function })
    }
    fn try_non_expr_stmt(&mut self)->Option<Result<StmtNode,ParsingFailed>>{
        Some(if self.matches(TokenKind::Let){
            self.let_stmt()
        }
        else if self.matches(TokenKind::Fun){
            self.fun_stmt()
        }
        else if self.matches(TokenKind::Struct){
            self.struct_stmt()
        }
        else{
            return None
        })
    }
    fn statement(&mut self)->Result<StmtNode,ParsingFailed>{
        if let Some(stmt) = self.try_non_expr_stmt(){
            stmt
        }
        else{
            self.expression_statement()
        }
    }
    fn synchronize(&mut self){
        loop {
            if self.check(TokenKind::Fun) || 
                self.check(TokenKind::If) || 
                self.check(TokenKind::While) || 
                self.check(TokenKind::Let)  || 
                self.check(TokenKind::LeftBrace)||
                self.is_at_end(){
                break;
            }
            self.advance();
        }
    }
    pub fn parse(mut self)->Result<Vec<StmtNode>,ParsingFailed>{
        let mut stmts = Vec::new();
        while !self.is_at_end() {
            if let Ok(stmt) = self.statement(){
                stmts.push(stmt);
            }
            else{
                self.had_error = true;
                self.synchronize();
            }
        }
        if !self.had_error { Ok(stmts) } else { Err(ParsingFailed) }
    }
}