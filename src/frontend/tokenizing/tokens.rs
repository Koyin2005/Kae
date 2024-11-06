#[derive(Clone, Copy,Debug)]
pub struct Token<'a>{
    pub  lexeme : &'a str,
    pub  kind : TokenKind,
    pub line : u32,
}
#[derive(PartialEq, Eq,Clone, Copy,Debug)]
pub enum TokenKind{
    Semicolon,
    Star,
    Slash,
    Plus,
    Minus,
    Equals,
    Bang,
    Lesser,
    Greater,
    LeftBrace,
    RightBrace,
    LeftParen,
    RightParen,
    LeftBracket,
    RightBracket,
    Dot,
    Coma,
    Colon,
    QuestionMark,

    EqualsEquals,
    BangEquals,
    LesserEquals,
    GreaterEquals,
    FatArrow,
    ThinArrow,

    Int,
    Float,
    String,

    Match,
    If, 
    While,
    And,
    Or,
    Else,
    Fun,
    Struct,
    True,
    False,
    Let,
    Print,
    Return,
    Typename,
    
    Identifier,
    Eof
}
