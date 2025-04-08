use miette::Report;
use crate::{lexer, TokenKind};
use lexer::Token;
use crate::error::ParseError;

#[derive(Debug)]
pub enum Expr {
    Literal(Literal),
    Unary {
        op: UnaryOp,
        expr: Box<Expr>,
    },
    Binary {
        left: Box<Expr>,
        op: BinaryOp,
        right: Box<Expr>,
    },
    Grouping(Box<Expr>),
}

#[derive(Debug)]
enum Literal {
    Number(f64),
    String(String),
    Bool(bool),
    Nil,
}

#[derive(Debug)]
enum UnaryOp {
    Bang,
    Minus,
}

#[derive(Debug)]
enum BinaryOp {
    Plus,
    Minus,
    Star,
    Slash,

    Greater,
    GreaterEqual,
    Less,
    LessEqual,
    Equal,
    EqualEqual,
    BangEqual,
}

pub struct Parser<'a> {
    tokens: Vec<Token<'a>>,
    position: usize,
    errors: Vec<Report>,
    source: &'a str,
}

impl<'a> Parser<'a> {
    pub fn new(tokens: Vec<Token<'a>>, source: &'a str) -> Self {
        Parser {
            tokens,
            position: 0,
            errors: vec![],
            source,
        }
    }

    fn peek(&self) -> Option<&Token<'a>> {
        self.tokens.get(self.position)
    }

    fn previous(&self) -> Option<&Token<'a>> {
        self.tokens.get(self.position - 1)
    }

    fn is_at_end(&self) -> bool {
        if let Some(token) = self.peek() {
            token.token_kind == TokenKind::EOF
        } else {
            false
        }
    }

    fn advance(&mut self) {
        if !self.is_at_end() {
            self.position += 1;
        }
    }

    fn check(&self, token_kind: TokenKind) -> bool {
        if self.is_at_end() {
            return false;
        }

        if let Some(token) = self.peek() {
            token.token_kind == token_kind
        } else {
            false
        }
    }

    fn match_token(&mut self, types: &[TokenKind]) -> bool {
        for token_kind in types {
            if self.check(token_kind.clone()) {
                self.advance();
                return true;
            }
        }
        false
    }

    pub fn get_errors(&self) -> &Vec<Report> {
        &self.errors
    }

    pub fn parse(&mut self) -> Expr {
        self.expression()
    }


    fn expression(&mut self) -> Expr {
        self.equality()
    }

    fn equality(&mut self) -> Expr {
       let mut expr = self.comparison();
        while self.match_token(&[TokenKind::BangEqual, TokenKind::EqualEqual]) {
            let operator = self.previous().unwrap();

            let op = match operator.token_kind {
                TokenKind::BangEqual => BinaryOp::BangEqual,
                TokenKind::EqualEqual => BinaryOp::EqualEqual,
                _ => unreachable!(),
            };

            let right = self.comparison();
            expr = Expr::Binary {
                left: Box::new(expr),
                op,
                right: Box::new(right),
            }
        }
        expr
    }

    fn comparison(&mut self) -> Expr {
        let mut expr = self.term();
        while self.match_token(&[TokenKind::Less, TokenKind::LessEqual, TokenKind::EqualEqual, TokenKind::Greater, TokenKind::GreaterEqual]) {
            let operator = self.previous().unwrap();

            let op = match operator.token_kind {
                TokenKind::Less => BinaryOp::Less,
                TokenKind::LessEqual => BinaryOp::LessEqual,
                TokenKind::EqualEqual => BinaryOp::EqualEqual,
                TokenKind::Greater => BinaryOp::Greater,
                TokenKind::GreaterEqual => BinaryOp::GreaterEqual,
                _ => unreachable!(),
            };

            let right = self.term();

            expr = Expr::Binary {
                left: Box::new(expr),
                op,
                right: Box::new(right),
            };
        }
        expr
    }

    fn term(&mut self) -> Expr {
        let mut expr = self.factor();
        while self.match_token(&[TokenKind::Plus, TokenKind::Minus]) {
            let operator = self.previous().unwrap();

            let op = match operator.token_kind {
                TokenKind::Plus => BinaryOp::Plus,
                TokenKind::Minus => BinaryOp::Minus,
                _ => unreachable!(),
            };

            let right = self.factor();

            expr = Expr::Binary {
                left: Box::new(expr),
                op,
                right: Box::new(right),
            };
        }
        expr
    }

    fn factor(&mut self) -> Expr {
        let mut expr = self.unary();
        while self.match_token(&[TokenKind::Slash, TokenKind::Star]) {
            let operator = self.previous().unwrap();

            let op = match operator.token_kind {
                TokenKind::Slash => BinaryOp::Slash,
                TokenKind::Star => BinaryOp::Star,
                _ => unreachable!(),
            };

            let right = self.unary();

            expr = Expr::Binary {
                left: Box::new(expr),
                op,
                right: Box::new(right),
            };
        }
        expr
    }

    fn unary(&mut self) -> Expr {
        if self.match_token(&[TokenKind::Minus, TokenKind::Bang]) {
            let operator = self.previous().unwrap();

            let op = match operator.token_kind {
                TokenKind::Bang => UnaryOp::Bang,
                TokenKind::Minus => UnaryOp::Minus,
                _ => unreachable!(),
            };

            let right = self.unary();

            return Expr::Unary {
                op,
                expr: Box::new(right),
            };
        }
        self.primary()
    }

    fn primary(&mut self) -> Expr {
        if self.match_token(&[TokenKind::False]) {
            Expr::Literal(Literal::Bool(false))
        } else if self.match_token(&[TokenKind::True]) {
            Expr::Literal(Literal::Bool(true))
        } else if self.match_token(&[TokenKind::Nil]) {
            Expr::Literal(Literal::Nil)
        } else if let Some(token) = self.peek() {
            match &token.token_kind {
                TokenKind::Number(value) => {
                    let number = *value;
                    self.advance();
                    Expr::Literal(Literal::Number(number))
                }
                TokenKind::String(value) => {
                    let string = value.clone();
                    self.advance();
                    Expr::Literal(Literal::String(string))
                }
                TokenKind::LeftParen => {
                    let cloned_token = token.clone();
                    self.advance();
                    let expr = self.expression();
                    if !self.match_token(&[TokenKind::RightParen]) {
                        self.errors.push(ParseError::UnclosedParenthesis {
                            src: self.source.to_string(),
                            span: cloned_token.position.into()
                        }.into())
                    }
                    Expr::Grouping(Box::new(expr))
                }
            _ => {
                let token = self.peek().cloned();
                if let Some(token) = token {
                    let error = ParseError::UnexpectedToken {
                        src: self.source.to_string(),
                        span: token.position.into(),
                        found: token.token_kind,
                        expected: TokenKind::Class,
                    };
                    self.errors.push(error.into());
                    self.advance();
                } else {
                    let error = ParseError::UnexpectedToken {
                        src: self.source.to_string(),
                        span: self.source.len().into(),
                        found: TokenKind::EOF,
                        expected: TokenKind::Class,
                    };
                    self.errors.push(error.into())
                }
                Expr::Literal(Literal::Nil)
            },
            }

        } else {
            unreachable!();
        }
    }
}
