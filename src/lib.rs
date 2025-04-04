use miette::{miette, LabeledSpan, Report};

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Token{
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    Comma,
    Dot,
    Minus,
    Plus,
    Semicolon,
    Slash,
    Star,
    Bang,
    BangEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,
    Question,
    Colon,
}


pub struct Lexer<'a>{
    source: &'a String,
    tokens: Vec<Result<Token, Report>>,
    position: usize,
    start: usize,
}

impl<'a> Lexer<'a> {
    pub fn new(source: &'a String) -> Self {
        Lexer{source, tokens: vec![], position: 0, start: 0}
    }
    pub fn lex(&mut self) -> &Vec<Result<Token, Report>> {
        let mut chars = self.source.chars();

        for char in chars {
            let token = match char {
                '(' => Ok(Token::LeftParen),
                ')' => Ok(Token::RightParen),
                '{' => Ok(Token::LeftBrace),
                '}' => Ok(Token::RightBrace),
                ',' => Ok(Token::Comma),
                '.' => Ok(Token::Dot),
                '-' => Ok(Token::Minus),
                '+' => Ok(Token::Plus),
                ';' => Ok(Token::Semicolon),
                '/' => Ok(Token::Slash),
                '*' => Ok(Token::Star),
                '!' => Ok(Token::Bang),
                _ => {
                    Err(miette!(
                        help = "unexpected character",
                        labels = vec![LabeledSpan::at(self.position, "here")],
                        "expected closing ')'"
                        )
                        .with_source_code(self.source.to_string()))

                }
            };
            self.tokens.push(token);
            self.position += 1;
        }
        &self.tokens
    }
}