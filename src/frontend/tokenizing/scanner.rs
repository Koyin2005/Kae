use super::tokens::{Token, TokenKind};

pub struct ScanError{
    message : String,
    line : u32
}
pub struct ScanningFailed;
pub struct Scanner<'src>{
    source : &'src str,
    current_char : char,
    start_index : usize,
    current_index : usize,
    line : u32
}

impl<'src> Scanner<'src>{
    pub fn new(source:&'src str)->Self{
        Scanner { source , current_char:'\0', start_index:0, current_index:0,line:1}
    }
    fn is_at_end(&self)->bool{
        self.current_index >= self.source.len()
    }
    fn advance(&mut self)->char{
        let next_char = self.peek();
        self.current_index+=1;
        while !self.source.is_char_boundary(self.current_index){
            self.current_index+=1;
        }
        self.current_char = next_char;
        next_char

    }
    fn peek(&self)->char{
        self.source[self.current_index..].chars().next().unwrap_or('\0')
    }
    fn peek_next(&self)->char{
        if self.is_at_end() { return '\0';}
        let mut next_index = self.current_index+1;
        while !self.source.is_char_boundary(next_index) {
            next_index+=1;
        }
        self.source[next_index..].chars().next().unwrap_or('\0')
    }
    fn match_char(&mut self,char:char)->bool{
        if self.peek() == char{
            self.advance();
            return true;
        }
        false
    }
    fn make_token(&self,kind:TokenKind)->Token<'src>{
        Token{
            lexeme: &self.source[self.start_index..self.current_index],
            line:self.line,
            kind
        }
    }
    fn error(&self,message:String)->ScanError{
        ScanError { message, line:self.line }
    }
    fn number(&mut self)->Token<'src>{
        while self.peek().is_ascii_digit() {
            self.advance();
        }
        let is_float = if self.peek() == '.' && self.peek_next().is_ascii_digit(){
            self.advance();
            while self.peek().is_ascii_digit() {
                self.advance();
            }
            true
        } else {false};
        if !is_float { self.make_token(TokenKind::Int)} else {self.make_token(TokenKind::Float)}
    }
    fn string(&mut self)->Result<Token<'src>,ScanError>{
        while self.peek() != '"' && !self.is_at_end(){
            if self.peek() == '\n'{
                self.line+=1;
            }
            self.advance();
        }
        if self.peek() == '"'{
            self.advance();
            Ok(self.make_token(TokenKind::String))
        }
        else{
            Err(self.error("Unterminated string.".to_string()))
        }
    }
    fn skip_whitespace(&mut self)->Result<(),ScanError>{
        loop {
            let c = self.peek();
            match c{
                '\r'|' '|'\t' => {
                    self.advance();
                },
                '\n' => {
                    self.line += 1;
                    self.advance();
                },
                '/'  if self.peek_next() == '/' =>{
                    while self.peek() != '\n' && !self.is_at_end() {
                        self.advance();
                    }
                },
                '/' if self.peek_next() ==  '*' => {
                    self.advance();
                    self.advance();
                    let mut depth = 1;
                    while depth > 0 && !self.is_at_end() {
                        if self.peek() == '*' && self.peek_next() == '/'{
                            depth -= 1;
                            self.advance();
                            self.advance();
                        }
                        else if self.peek() == '/' && self.peek() == '*'{
                            depth += 1;
                            self.advance();
                            self.advance();
                        }
                        else if self.peek() == '\n'{
                            self.line += 1;
                            self.advance();
                        }
                        else{
                            self.advance();
                        }
                    }
                    if depth > 0{
                        return Err(self.error("Unterminated comment.".to_string()));
                    }

                },
                _ => break
            }
        }
        Ok(())
    }
    fn identifier(&mut self)->Token<'src>{
        while self.peek().is_ascii_alphanumeric() || self.peek() == '_'  {
            self.advance();
        }
        self.make_token(match  &self.source[self.start_index..self.current_index]{
            "and" => TokenKind::And,
            "or" => TokenKind::Or,
            "if" => TokenKind::If,
            "else" => TokenKind::Else,
            "while" => TokenKind::While,
            "fun" => TokenKind::Fun,
            "true" => TokenKind::True,
            "false" => TokenKind::False,
            "let" => TokenKind::Let,
            "print" => TokenKind::Print,
            "match" => TokenKind::Match,
            "return" => TokenKind::Return,
            "typename" => TokenKind::Typename,
            "struct" => TokenKind::Struct,
            _ => TokenKind::Identifier
        })
    }
    fn scan_token(&mut self)->Result<Token<'src>,ScanError>{
        self.skip_whitespace()?;
        self.start_index = self.current_index;
        if self.is_at_end() { return Ok(self.make_token(TokenKind::Eof));}
        let char = self.advance();
        Ok(match char{
            '+' => self.make_token(TokenKind::Plus),
            '-' => if self.match_char('>') {self.make_token(TokenKind::ThinArrow)} else {self.make_token(TokenKind::Minus)},
            '*' => self.make_token(TokenKind::Star),
            '/' => self.make_token(TokenKind::Slash),
            '(' => self.make_token(TokenKind::LeftParen),
            ')' => self.make_token(TokenKind::RightParen),
            '[' => self.make_token(TokenKind::LeftBracket),
            ']' => self.make_token(TokenKind::RightBracket),
            '{' => self.make_token(TokenKind::LeftBrace),
            '}' => self.make_token(TokenKind::RightBrace),
            ';' => self.make_token(TokenKind::Semicolon),
            '.' => self.make_token(TokenKind::Dot),
            ',' => self.make_token(TokenKind::Coma),
            '?' => self.make_token(TokenKind::QuestionMark),
            ':' => self.make_token(TokenKind::Colon),
            '=' => if self.match_char('=') {self.make_token(TokenKind::EqualsEquals)} else if self.match_char('>'){self.make_token(TokenKind::FatArrow)} else {self.make_token(TokenKind::Equals)},
            '<' => if self.match_char('=') {self.make_token(TokenKind::LesserEquals)} else {self.make_token(TokenKind::Lesser)},
            '>' => if self.match_char('=') {self.make_token(TokenKind::GreaterEquals)} else { self.make_token(TokenKind::Greater)},
            '!' => if self.match_char('=') {self.make_token(TokenKind::BangEquals)} else { self.make_token(TokenKind::Bang)},
            '0'..='9' => self.number(),
            '"' => self.string()?,
            char if char.is_ascii_alphabetic() || char == '_' => self.identifier(),
            char => return Err(self.error(format!("Unsupported character '{}'.",char)))
        })
    }
    pub fn scan(mut self)->Result<Vec<Token<'src>>,ScanningFailed>{
        let mut tokens = Vec::new();
        let mut had_error = false;
        loop{
            let token = match self.scan_token(){
                Ok(token) => token,
                Err(error) => {
                    eprintln!("Error on line {} : {}",error.line,error.message);
                    had_error = true;
                    if self.is_at_end(){
                        break;
                    }
                    continue;
                }
            };
            tokens.push(token);
            if token.kind == TokenKind::Eof{
                break;
            }
        }
        if !had_error { Ok(tokens) } else { Err(ScanningFailed) }
    }
}