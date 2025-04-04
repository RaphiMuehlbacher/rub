use miette::{miette, LabeledSpan, Report};

#[derive(Debug, Copy, Clone)]
pub enum TokenKind {
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
    EOF,
}

#[derive(Debug, Copy, Clone)]
pub struct Token<'a> {
    token_kind: TokenKind,
    position: usize,
    lexeme: &'a str,
    literal: &'a str
}

pub struct Lexer<'a>{
    source: &'a String,
    tokens: Vec<Result<Token<'a>, Report>>,
    position: usize,
    start: usize,
}

impl<'a> Lexer<'a> {
    pub fn new(source: &'a String) -> Self {
        Lexer{source, tokens: vec![], position: 0, start: 0}
    }
    pub fn lex(&mut self) -> &Vec<Result<Token<'a>, Report>> {
        while self.position < self.source.len() {
            self.start = self.position;

            if let Some(c) = self.source[self.position..].chars().next(){
                self.position += c.len_utf8();

                let token = match c {
                    '(' => Ok(self.just(TokenKind::LeftParen)),
                    ')' => Ok(self.just(TokenKind::RightParen)),
                    '{' => Ok(self.just(TokenKind::LeftBrace)),
                    '}' => Ok(self.just(TokenKind::RightBrace)),
                    ',' => Ok(self.just(TokenKind::Comma)),
                    '.' => Ok(self.just(TokenKind::Dot)),
                    '-' => Ok(self.just(TokenKind::Minus)),
                    '+' => Ok(self.just(TokenKind::Plus)),
                    ';' => Ok(self.just(TokenKind::Semicolon)),
                    '/' => Ok(self.just(TokenKind::Slash)),
                    '*' => Ok(self.just(TokenKind::Star)),
                    '!' => Ok(self.just(TokenKind::Bang)),
                    _ => {
                        Err(miette!(
                        help = "unexpected character",
                        labels = vec![LabeledSpan::at(self.start, format!("unexpected '{}'", c))],
                        "expected closing ')'"
                        )
                            .with_source_code(self.source.to_string()))

                    }
                };
                self.tokens.push(token);
            } else {
                eprintln!("I don't know");
            }
        }
        let eof_token = Token{token_kind: TokenKind::EOF, position: self.source.len(), literal: "", lexeme: "", };
        self.tokens.push(Ok(eof_token));

        &self.tokens
    }

    pub fn just(&self, token_kind: TokenKind) -> Token<'a> {
        let lexeme = &self.source[self.start..self.position];
        Token {token_kind, position: self.start, lexeme, literal: lexeme}
    }
}