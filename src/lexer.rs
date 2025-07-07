use crate::error::LexError;
use miette::{Report, SourceSpan};
use std::fmt::{Display, Formatter, Result};

#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    Delim(Delimiter),
    Operator(Operator),
    Keyword(Keyword),
    Punct(Punctuation),
    Ident(String),
    Literal(Literal),
    EOF,
}
impl Display for TokenKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            TokenKind::Delim(d) => write!(
                f,
                "{}",
                match d {
                    Delimiter::LeftParen => "(",
                    Delimiter::RightParen => ")",
                    Delimiter::LeftBrace => "{",
                    Delimiter::RightBrace => "}",
                    Delimiter::LeftBracket => "[",
                    Delimiter::RightBracket => "]",
                }
            ),
            TokenKind::Operator(op) => write!(
                f,
                "{}",
                match op {
                    Operator::Plus => "+",
                    Operator::Minus => "-",
                    Operator::Star => "*",
                    Operator::Slash => "/",
                    Operator::Equal => "=",
                    Operator::EqualEqual => "==",
                    Operator::Bang => "!",
                    Operator::BangEqual => "!=",
                    Operator::Less => "<",
                    Operator::LessEqual => "<=",
                    Operator::Greater => ">",
                    Operator::GreaterEqual => ">=",
                }
            ),
            TokenKind::Keyword(k) => write!(
                f,
                "{}",
                match k {
                    Keyword::Let => "let",
                    Keyword::Fn => "fn",
                    Keyword::If => "if",
                    Keyword::Else => "else",
                    Keyword::Return => "return",
                    Keyword::While => "while",
                    Keyword::For => "for",
                    Keyword::Struct => "struct",
                    Keyword::True => "true",
                    Keyword::False => "false",
                    Keyword::Nil => "nil",
                    Keyword::And => "and",
                    Keyword::Or => "or",
                }
            ),
            TokenKind::Punct(p) => write!(
                f,
                "{}",
                match p {
                    Punctuation::Comma => ",",
                    Punctuation::Dot => ".",
                    Punctuation::Semicolon => ";",
                    Punctuation::Colon => ":",
                    Punctuation::Arrow => "->",
                }
            ),
            TokenKind::Ident(name) => write!(f, "{}", name),
            TokenKind::Literal(lit) => match lit {
                Literal::Int(i) => write!(f, "{}", i),
                Literal::Float(fl) => write!(f, "{}", fl),
                Literal::String(s) => write!(f, "\"{}\"", s),
            },
            TokenKind::EOF => write!(f, "EOF"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Punctuation {
    Comma,
    Dot,
    Semicolon,
    Colon,
    Arrow,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    Int(i64),
    Float(f64),
    String(String),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Delimiter {
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    LeftBracket,
    RightBracket,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Operator {
    Plus,
    Minus,
    Star,
    Slash,
    Equal,
    EqualEqual,
    Bang,
    BangEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Keyword {
    Let,
    Fn,
    If,
    Else,
    Return,
    While,
    For,
    Struct,
    True,
    False,
    Nil,
    And,
    Or,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub token_kind: TokenKind,
    pub span: SourceSpan,
}

pub struct LexerResult<'a> {
    pub errors: &'a Vec<Report>,
    pub tokens: Vec<Token>,
}

pub struct Lexer<'a> {
    source: &'a str,
    tokens: Vec<Token>,
    errors: Vec<Report>,
    position: usize,
    start: usize,
}

impl<'a> Lexer<'a> {
    pub fn new(source: &'a str) -> Self {
        Lexer {
            source,
            tokens: vec![],
            errors: vec![],
            position: 0,
            start: 0,
        }
    }

    pub fn lex(&mut self) -> LexerResult {
        while self.position < self.source.len() {
            self.start = self.position;
            let c = self.source[self.position..].chars().next().unwrap();

            self.position += c.len_utf8();

            let token = match c {
                '(' => self.create_token(TokenKind::Delim(Delimiter::LeftParen)),
                ')' => self.create_token(TokenKind::Delim(Delimiter::RightParen)),
                '{' => self.create_token(TokenKind::Delim(Delimiter::LeftBrace)),
                '}' => self.create_token(TokenKind::Delim(Delimiter::RightBrace)),
                '[' => self.create_token(TokenKind::Delim(Delimiter::LeftBracket)),
                ']' => self.create_token(TokenKind::Delim(Delimiter::RightBracket)),
                ',' => self.create_token(TokenKind::Punct(Punctuation::Comma)),
                '.' => self.create_token(TokenKind::Punct(Punctuation::Dot)),
                ';' => self.create_token(TokenKind::Punct(Punctuation::Semicolon)),
                ':' => self.create_token(TokenKind::Punct(Punctuation::Colon)),
                '-' => {
                    if self.match_char('>') {
                        self.create_token(TokenKind::Punct(Punctuation::Arrow))
                    } else {
                        self.create_token(TokenKind::Operator(Operator::Minus))
                    }
                }
                '+' => self.create_token(TokenKind::Operator(Operator::Plus)),
                '/' => {
                    if self.match_char('/') {
                        while self.position < self.source.len() && !self.match_char('\n') {
                            if let Some(c) = self.peek() {
                                self.position += c.len_utf8();
                            }
                        }
                        continue;
                    } else if self.match_char('*') {
                        let mut nesting = 1;
                        while nesting > 0 && self.position < self.source.len() {
                            if let Some(c) = self.peek() {
                                self.position += c.len_utf8();
                                match c {
                                    '/' if self.match_char('*') => nesting += 1,
                                    '*' if self.match_char('/') => nesting -= 1,
                                    _ => {}
                                }
                            }
                        }
                        if nesting > 0 {
                            self.errors.push(
                                LexError::UnterminatedComment {
                                    span: (self.start..self.position).into(),
                                    src: self.source.to_string(),
                                }
                                .into(),
                            )
                        }
                        continue;
                    } else {
                        self.create_token(TokenKind::Operator(Operator::Slash))
                    }
                }
                '*' => self.create_token(TokenKind::Operator(Operator::Star)),
                '!' => {
                    if self.match_char('=') {
                        self.create_token(TokenKind::Operator(Operator::BangEqual))
                    } else {
                        self.create_token(TokenKind::Operator(Operator::Bang))
                    }
                }
                '=' => {
                    if self.match_char('=') {
                        self.create_token(TokenKind::Operator(Operator::EqualEqual))
                    } else {
                        self.create_token(TokenKind::Operator(Operator::Equal))
                    }
                }
                '<' => {
                    if self.match_char('=') {
                        self.create_token(TokenKind::Operator(Operator::LessEqual))
                    } else {
                        self.create_token(TokenKind::Operator(Operator::Less))
                    }
                }
                '>' => {
                    if self.match_char('=') {
                        self.create_token(TokenKind::Operator(Operator::GreaterEqual))
                    } else {
                        self.create_token(TokenKind::Operator(Operator::Greater))
                    }
                }
                '"' => {
                    let rest = &self.source[self.start..];
                    let token = match rest[1..].find('"') {
                        Some(pos) => {
                            let end_offset = pos + 1;
                            self.position = self.start + end_offset + 1;
                            self.create_token(TokenKind::Literal(Literal::String(rest[1..end_offset].to_string())))
                        }
                        None => {
                            self.errors.push(
                                LexError::UnterminatedString {
                                    span: (self.start..self.source.len()).into(),
                                    src: self.source.to_string(),
                                }
                                .into(),
                            );
                            continue;
                        }
                    };
                    token
                }
                'a'..='z' | 'A'..='Z' | '_' => {
                    let rest = &self.source[self.start..];
                    let end_offset = rest.find(|c: char| !c.is_alphanumeric() && c != '_').unwrap_or(rest.len());

                    self.position = self.start + end_offset;

                    let literal = &self.source[self.start..self.position];

                    let kind = match literal {
                        "and" => TokenKind::Keyword(Keyword::And),
                        "else" => TokenKind::Keyword(Keyword::Else),
                        "false" => TokenKind::Keyword(Keyword::False),
                        "for" => TokenKind::Keyword(Keyword::For),
                        "fn" => TokenKind::Keyword(Keyword::Fn),
                        "if" => TokenKind::Keyword(Keyword::If),
                        "nil" => TokenKind::Keyword(Keyword::Nil),
                        "or" => TokenKind::Keyword(Keyword::Or),
                        "return" => TokenKind::Keyword(Keyword::Return),
                        "true" => TokenKind::Keyword(Keyword::True),
                        "let" => TokenKind::Keyword(Keyword::Let),
                        "while" => TokenKind::Keyword(Keyword::While),
                        "struct" => TokenKind::Keyword(Keyword::Struct),
                        _ => TokenKind::Ident(literal.to_string()),
                    };

                    self.create_token(kind)
                }
                '0'..='9' => {
                    let rest = &self.source[self.start..];
                    let first_part_offset = rest.find(|c| !matches!(c, '0'..='9')).unwrap_or(rest.len());

                    self.position = self.start + first_part_offset;

                    if self.match_char('.') {
                        let rest_after_dot = &self.source[self.position..];
                        let second_part_offset = rest_after_dot.find(|c| !matches!(c, '0'..='9')).unwrap_or(rest_after_dot.len());

                        self.position += second_part_offset;
                        Token {
                            token_kind: TokenKind::Literal(Literal::Float(self.source[self.start..self.position].parse().unwrap())),
                            span: SourceSpan::new(self.start.into(), self.position - self.start),
                        }
                    } else {
                        let literal = &rest[..first_part_offset];
                        Token {
                            token_kind: TokenKind::Literal(Literal::Int(literal.parse().unwrap())),
                            span: SourceSpan::new(self.start.into(), self.position - self.start),
                        }
                    }
                }

                ' ' | '\r' | '\t' | '\n' => continue,
                _ => {
                    self.errors.push(
                        LexError::UnexpectedCharacter {
                            span: self.start.into(),
                            src: self.source.to_string(),
                            character: c,
                        }
                        .into(),
                    );
                    continue;
                }
            };
            self.tokens.push(token);
        }
        let eof_token = Token {
            token_kind: TokenKind::EOF,
            span: SourceSpan::from(self.source.len() - 1),
        };
        self.tokens.push(eof_token);
        LexerResult {
            errors: &self.errors,
            tokens: self.tokens.clone(),
        }
    }

    fn create_token(&self, token_kind: TokenKind) -> Token {
        Token {
            token_kind,
            span: SourceSpan::new(self.start.into(), self.position - self.start),
        }
    }

    fn peek(&self) -> Option<char> {
        self.source[self.position..].chars().next()
    }

    fn match_char(&mut self, expected: char) -> bool {
        let next = match self.peek() {
            None => return false,
            Some(c) => c,
        };

        if next == expected {
            self.position += next.len_utf8();
            true
        } else {
            false
        }
    }
}
