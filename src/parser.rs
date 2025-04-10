use crate::error::ParseError;
use crate::error::ParseError::{MissingOperand, UnclosedParenthesis, UnexpectedEOF};
use crate::{lexer, TokenKind};
use lexer::Token;
use miette::{Report, SourceSpan};

type ParseResult = Result<Expr, Report>;

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
    Err,
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
        match self.peek() {
            Some(token) => token.token_kind == TokenKind::EOF,
            None => false,
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

    fn error_expr(&mut self, err: ParseError) -> Expr {
        self.errors.push(err.into());
        Expr::Err
    }

    fn expect_expr(&self, result: ParseResult, side: &str, span: SourceSpan) -> ParseResult {
        result.map_err(|_| {
            MissingOperand {
                src: self.source.to_string(),
                span,
                side: side.to_string(),
            }
            .into()
        })
    }
    pub fn parse(&mut self) -> Expr {
        if self.peek().unwrap().token_kind == TokenKind::EOF {
            Expr::Err
        } else {
            match self.expression() {
                Ok(expr) => expr,
                Err(err) => {
                    self.errors.push(err.into());
                    Expr::Err
                }
            }
        }
    }

    fn expression(&mut self) -> ParseResult {
        self.equality()
    }

    fn equality(&mut self) -> ParseResult {
        let mut expr = self.comparison()?;
        while self.match_token(&[TokenKind::BangEqual, TokenKind::EqualEqual]) {
            let operator = self.previous().unwrap();

            let op = match operator.token_kind {
                TokenKind::BangEqual => BinaryOp::BangEqual,
                TokenKind::EqualEqual => BinaryOp::EqualEqual,
                _ => unreachable!(),
            };
            let span = operator.span;
            let result = self.comparison();
            let right = self.expect_expr(result, "right", span)?;
            expr = Expr::Binary {
                left: Box::new(expr),
                op,
                right: Box::new(right),
            };
        }
        Ok(expr)
    }

    fn comparison(&mut self) -> ParseResult {
        let mut expr = self.term()?;
        while self.match_token(&[
            TokenKind::Less,
            TokenKind::LessEqual,
            TokenKind::Greater,
            TokenKind::GreaterEqual,
        ]) {
            let operator = self.previous().unwrap();

            let op = match operator.token_kind {
                TokenKind::Less => BinaryOp::Less,
                TokenKind::LessEqual => BinaryOp::LessEqual,
                TokenKind::Greater => BinaryOp::Greater,
                TokenKind::GreaterEqual => BinaryOp::GreaterEqual,
                _ => unreachable!(),
            };

            let span = operator.span;
            let result = self.term();
            let right = self.expect_expr(result, "right", span)?;
            expr = Expr::Binary {
                left: Box::new(expr),
                op,
                right: Box::new(right),
            };
        }
        Ok(expr)
    }

    fn term(&mut self) -> ParseResult {
        let mut expr = self.factor()?;
        while self.match_token(&[TokenKind::Plus, TokenKind::Minus]) {
            let operator = self.previous().unwrap();

            let op = match operator.token_kind {
                TokenKind::Plus => BinaryOp::Plus,
                TokenKind::Minus => BinaryOp::Minus,
                _ => unreachable!(),
            };

            let span = operator.span;
            let result = self.factor();
            let right = self.expect_expr(result, "right", span)?;
            expr = Expr::Binary {
                left: Box::new(expr),
                op,
                right: Box::new(right),
            };
        }
        Ok(expr)
    }

    fn factor(&mut self) -> ParseResult {
        let mut expr = self.unary()?;
        while self.match_token(&[TokenKind::Slash, TokenKind::Star]) {
            let operator = self.previous().unwrap();

            let op = match operator.token_kind {
                TokenKind::Slash => BinaryOp::Slash,
                TokenKind::Star => BinaryOp::Star,
                _ => unreachable!(),
            };

            let span = operator.span;
            let result = self.unary();
            let right = self.expect_expr(result, "right", span)?;
            expr = Expr::Binary {
                left: Box::new(expr),
                op,
                right: Box::new(right),
            };
        }
        Ok(expr)
    }

    fn unary(&mut self) -> ParseResult {
        if self.match_token(&[TokenKind::Minus, TokenKind::Bang]) {
            let operator = self.previous().unwrap();

            let op = match operator.token_kind {
                TokenKind::Bang => UnaryOp::Bang,
                TokenKind::Minus => UnaryOp::Minus,
                _ => unreachable!(),
            };

            let span = operator.span;
            let result = self.unary();
            let expr = self.expect_expr(result, "right", span)?;

            Ok(Expr::Unary {
                op,
                expr: Box::new(expr),
            })
        } else {
            self.primary()
        }
    }

    fn primary(&mut self) -> ParseResult {
        if self.match_token(&[TokenKind::False]) {
            Ok(Expr::Literal(Literal::Bool(false)))
        } else if self.match_token(&[TokenKind::True]) {
            Ok(Expr::Literal(Literal::Bool(true)))
        } else if self.match_token(&[TokenKind::Nil]) {
            Ok(Expr::Literal(Literal::Nil))
        } else if self.match_token(&[TokenKind::LeftParen]) {
            let opening_paren = self.previous().unwrap().clone();

            if self.match_token(&[TokenKind::RightParen]) {
                return Ok(Expr::Grouping(Box::new(Expr::Literal(Literal::Nil))));
            }

            if self.check(TokenKind::EOF) {
                let error = UnclosedParenthesis {
                    src: self.source.to_string(),
                    span: opening_paren.span,
                };
                return Err(error.into());
            }

            let expr = self.expression()?;
            if !self.match_token(&[TokenKind::RightParen]) {
                let error = UnclosedParenthesis {
                    src: self.source.to_string(),
                    span: opening_paren.span,
                };
                self.errors.push(error.into());
            }
            Ok(Expr::Grouping(Box::new(expr)))
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
                span: token.span,
                side: "left".to_string(),
            };
            Err(error.into())
        } else if self.match_token(&[TokenKind::EOF]) {
            let error = UnexpectedEOF {
                src: self.source.to_string(),
                expected: "unexpected EOF".to_string(),
            };
            Err(error.into())
        } else if let Some(token) = self.peek() {
            match &token.token_kind {
                TokenKind::Number(value) => {
                    let number = *value;
                    self.advance();
                    Ok(Expr::Literal(Literal::Number(number)))
                }
                TokenKind::String(value) => {
                    let string = value.clone();
                    self.advance();
                    Ok(Expr::Literal(Literal::String(string)))
                }
                _ => {
                    let token = token.clone();
                    let error = ParseError::UnexpectedToken {
                        src: self.source.to_string(),
                        span: token.span,
                        found: token.token_kind,
                        expected: "literal or '('".to_string(),
                    };
                    Err(error.into())
                }
            }
        } else {
            unreachable!();
        }
    }
}
