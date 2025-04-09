use crate::error::ParseError;
use crate::error::ParseError::{MissingOperand, UnclosedParenthesis, UnexpectedEOF};
use crate::{lexer, TokenKind};
use lexer::Token;
use miette::Report;

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

    pub fn parse(&mut self) -> Option<Expr> {
        if self.peek().unwrap().token_kind == TokenKind::EOF {
            None
        } else {
            self.expression()
        }
    }

    fn expression(&mut self) -> Option<Expr> {
        self.equality()
    }

    fn equality(&mut self) -> Option<Expr> {
        let mut expr = self.comparison()?;
        while self.match_token(&[TokenKind::BangEqual, TokenKind::EqualEqual]) {
            let operator = self.previous().unwrap();

            let op = match operator.token_kind {
                TokenKind::BangEqual => BinaryOp::BangEqual,
                TokenKind::EqualEqual => BinaryOp::EqualEqual,
                _ => unreachable!(),
            };
            let position = operator.position;

            if let Some(right) = self.comparison() {
                expr = Expr::Binary {
                    left: Box::new(expr),
                    op,
                    right: Box::new(right),
                };
            } else {
                let error = MissingOperand {
                    src: self.source.to_string(),
                    span: position.into(),
                    side: "right".to_string(),
                };
                self.errors.push(error.into());
                break;
            }
        }
        Some(expr)
    }

    fn comparison(&mut self) -> Option<Expr> {
        let mut expr = self.term()?;
        while self.match_token(&[
            TokenKind::Less,
            TokenKind::LessEqual,
            TokenKind::EqualEqual,
            TokenKind::Greater,
            TokenKind::GreaterEqual,
        ]) {
            let operator = self.previous().unwrap();

            let op = match operator.token_kind {
                TokenKind::Less => BinaryOp::Less,
                TokenKind::LessEqual => BinaryOp::LessEqual,
                TokenKind::EqualEqual => BinaryOp::EqualEqual,
                TokenKind::Greater => BinaryOp::Greater,
                TokenKind::GreaterEqual => BinaryOp::GreaterEqual,
                _ => unreachable!(),
            };

            let position = operator.position;
            if let Some(right) = self.term() {
                expr = Expr::Binary {
                    left: Box::new(expr),
                    op,
                    right: Box::new(right),
                };
            } else {
                let error = MissingOperand {
                    src: self.source.to_string(),
                    span: position.into(),
                    side: "right".to_string(),
                };
                self.errors.push(error.into());
                break;
            }
        }
        Some(expr)
    }

    fn term(&mut self) -> Option<Expr> {
        let mut expr = self.factor()?;
        while self.match_token(&[TokenKind::Plus, TokenKind::Minus]) {
            let operator = self.previous().unwrap();

            let op = match operator.token_kind {
                TokenKind::Plus => BinaryOp::Plus,
                TokenKind::Minus => BinaryOp::Minus,
                _ => unreachable!(),
            };

            let position = operator.position;
            if let Some(right) = self.factor() {
                expr = Expr::Binary {
                    left: Box::new(expr),
                    op,
                    right: Box::new(right),
                };
            } else {
                let error = MissingOperand {
                    src: self.source.to_string(),
                    span: position.into(),
                    side: "right".to_string(),
                };
                self.errors.push(error.into());
                break;
            }
        }
        Some(expr)
    }

    fn factor(&mut self) -> Option<Expr> {
        let mut expr = self.unary()?;
        while self.match_token(&[TokenKind::Slash, TokenKind::Star]) {
            let operator = self.previous().unwrap();

            let op = match operator.token_kind {
                TokenKind::Slash => BinaryOp::Slash,
                TokenKind::Star => BinaryOp::Star,
                _ => unreachable!(),
            };

            let position = operator.position;
            if let Some(right) = self.unary() {
                expr = Expr::Binary {
                    left: Box::new(expr),
                    op,
                    right: Box::new(right),
                };
            } else {
                let error = MissingOperand {
                    src: self.source.to_string(),
                    span: position.into(),
                    side: "right".to_string(),
                };
                self.errors.push(error.into());
                break;
            }
        }
        Some(expr)
    }

    fn unary(&mut self) -> Option<Expr> {
        if self.match_token(&[TokenKind::Minus, TokenKind::Bang]) {
            let operator = self.previous().unwrap();

            let op = match operator.token_kind {
                TokenKind::Bang => UnaryOp::Bang,
                TokenKind::Minus => UnaryOp::Minus,
                _ => unreachable!(),
            };

            let position = operator.position;
            return if let Some(right) = self.unary() {
                Some(Expr::Unary {
                    op,
                    expr: Box::new(right),
                })
            } else {
                let error = MissingOperand {
                    src: self.source.to_string(),
                    span: position.into(),
                    side: "right".to_string(),
                };
                self.errors.push(error.into());
                None
            };
        }
        self.primary()
    }

    fn primary(&mut self) -> Option<Expr> {
        println!("{:?}", self.peek());
        if self.match_token(&[TokenKind::False]) {
            Some(Expr::Literal(Literal::Bool(false)))
        } else if self.match_token(&[TokenKind::True]) {
            Some(Expr::Literal(Literal::Bool(true)))
        } else if self.match_token(&[TokenKind::Nil]) {
            Some(Expr::Literal(Literal::Nil))
        } else if self.match_token(&[
            TokenKind::Plus,
            TokenKind::Minus,
            TokenKind::Star,
            TokenKind::Slash,
            TokenKind::Less,
            TokenKind::LessEqual,
            TokenKind::Greater,
            TokenKind::GreaterEqual,
            TokenKind::BangEqual,
            TokenKind::EqualEqual,
        ]) {
            let token = self.previous().unwrap();
            let error = MissingOperand {
                src: self.source.to_string(),
                span: token.position.into(),
                side: "left".to_string(),
            };
            self.errors.push(error.into());
            None
        } else if self.match_token(&[TokenKind::EOF]) {
            None
        } else if let Some(token) = self.peek() {
            match &token.token_kind {
                TokenKind::Number(value) => {
                    let number = *value;
                    self.advance();
                    Some(Expr::Literal(Literal::Number(number)))
                }
                TokenKind::String(value) => {
                    let string = value.clone();
                    self.advance();
                    Some(Expr::Literal(Literal::String(string)))
                }
                TokenKind::LeftParen => {
                    let opening_paren = token.clone();
                    self.advance();

                    if self.check(TokenKind::RightParen) {
                        self.advance();
                        return Some(Expr::Grouping(Box::new(Expr::Literal(Literal::Nil))));
                    }

                    if self.check(TokenKind::EOF) {
                        let error = UnclosedParenthesis {
                            src: self.source.to_string(),
                            span: opening_paren.position.into(),
                        };
                        self.errors.push(error.into());
                        return Some(Expr::Grouping(Box::new(Expr::Literal(Literal::Nil))));
                    }
                    let expr = self.expression();
                    if !self.match_token(&[TokenKind::RightParen]) {
                        let error = UnclosedParenthesis {
                            src: self.source.to_string(),
                            span: opening_paren.position.into(),
                        };
                        self.errors.push(error.into());
                    }
                    Some(Expr::Grouping(Box::new(expr?)))
                }
                _ => {
                    let token = token.clone();
                    let error = ParseError::UnexpectedToken {
                        src: self.source.to_string(),
                        span: token.position.into(),
                        found: token.token_kind,
                        expected: "literal or '('".to_string(),
                    };
                    self.errors.push(error.into());
                    self.advance();
                    None
                }
            }
        } else {
            unreachable!();
        }
    }
}
