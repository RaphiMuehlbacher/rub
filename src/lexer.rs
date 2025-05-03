use crate::error::LexError;
use miette::{Report, SourceSpan};

#[derive(Debug, Clone, PartialEq)]
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
    Colon,
    Arrow,

    String(String),
    Ident(String),
    Number(f64),

    And,
    Else,
    False,
    For,
    Fn,
    If,
    Nil,
    Or,
    Return,
    True,
    Let,
    While,

    TypeFloat,
    TypeString,
    TypeBool,
    TypeNil,

    EOF,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Token<'a> {
    pub token_kind: TokenKind,
    pub span: SourceSpan,
    pub literal: &'a str,
}

pub struct LexerResult<'a> {
    pub errors: &'a Vec<Report>,
    pub tokens: Vec<Token<'a>>,
}

pub struct Lexer<'a> {
    source: &'a str,
    tokens: Vec<Token<'a>>,
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
                '(' => self.create_token(TokenKind::LeftParen),
                ')' => self.create_token(TokenKind::RightParen),
                '{' => self.create_token(TokenKind::LeftBrace),
                '}' => self.create_token(TokenKind::RightBrace),
                ',' => self.create_token(TokenKind::Comma),
                '.' => self.create_token(TokenKind::Dot),
                '-' => {
                    if self.match_char('>') {
                        self.create_token(TokenKind::Arrow)
                    } else {
                        self.create_token(TokenKind::Minus)
                    }
                }
                '+' => self.create_token(TokenKind::Plus),
                ';' => self.create_token(TokenKind::Semicolon),
                ':' => self.create_token(TokenKind::Colon),
                '/' => {
                    if self.match_char('/') {
                        while self.position < self.source.len() && !self.match_char('\n') {
                            if let Some(c) = self.peek() {
                                self.position += c.len_utf8();
                            }
                        }
                        continue;
                    } else {
                        self.create_token(TokenKind::Slash)
                    }
                }
                '*' => self.create_token(TokenKind::Star),
                '!' => {
                    if self.match_char('=') {
                        self.create_token(TokenKind::BangEqual)
                    } else {
                        self.create_token(TokenKind::Bang)
                    }
                }
                '=' => {
                    if self.match_char('=') {
                        self.create_token(TokenKind::EqualEqual)
                    } else {
                        self.create_token(TokenKind::Equal)
                    }
                }
                '<' => {
                    if self.match_char('=') {
                        self.create_token(TokenKind::LessEqual)
                    } else {
                        self.create_token(TokenKind::Less)
                    }
                }
                '>' => {
                    if self.match_char('=') {
                        self.create_token(TokenKind::GreaterEqual)
                    } else {
                        self.create_token(TokenKind::Greater)
                    }
                }
                '"' => {
                    let rest = &self.source[self.start..];
                    let token = match rest[1..].find('"') {
                        Some(pos) => {
                            let end_offset = pos + 1;
                            self.position = self.start + end_offset + 1;
                            self.create_token(TokenKind::String(rest[1..end_offset].to_string()))
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
                        "and" => TokenKind::And,
                        "else" => TokenKind::Else,
                        "false" => TokenKind::False,
                        "for" => TokenKind::For,
                        "fn" => TokenKind::Fn,
                        "if" => TokenKind::If,
                        "nil" => TokenKind::Nil,
                        "or" => TokenKind::Or,
                        "return" => TokenKind::Return,
                        "true" => TokenKind::True,
                        "let" => TokenKind::Let,
                        "while" => TokenKind::While,
                        "Float" => TokenKind::TypeFloat,
                        "String" => TokenKind::TypeString,
                        "Bool" => TokenKind::TypeBool,
                        "Nil" => TokenKind::TypeNil,
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
                            token_kind: TokenKind::Number(self.source[self.start..self.position].parse().unwrap()),
                            span: SourceSpan::new(self.start.into(), self.position - self.start),
                            literal: &self.source[self.start..self.position],
                        }
                    } else {
                        Token {
                            token_kind: TokenKind::Number(rest[..first_part_offset].parse().unwrap()),
                            span: SourceSpan::new(self.start.into(), self.position - self.start),
                            literal: &rest[..first_part_offset],
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
            literal: "",
        };
        self.tokens.push(eof_token);
        LexerResult {
            errors: &self.errors,
            tokens: self.tokens.clone(),
        }
    }

    fn create_token(&self, token_kind: TokenKind) -> Token<'a> {
        let literal = &self.source[self.start..self.position];
        Token {
            token_kind,
            span: SourceSpan::new(self.start.into(), self.position - self.start),
            literal,
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
