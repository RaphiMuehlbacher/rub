use crate::error::ParseError;
use crate::error::ParseError::{
    MissingOperand, MissingSemicolon, RedundantSemicolon, UnclosedParenthesis, UnexpectedEOF,
};
use crate::{lexer, TokenKind};
use lexer::Token;
use miette::{Report, SourceOffset, SourceSpan};

type ParseResult<T> = Result<T, Report>;

#[derive(Debug)]
pub enum Stmt {
    ExprStmt { expr: Expr },
    PrintStmt { expr: Expr },
}

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

    fn expect_expr(
        &self,
        result: ParseResult<Expr>,
        side: &str,
        span: SourceSpan,
    ) -> ParseResult<Expr> {
        result.map_err(|_| {
            MissingOperand {
                src: self.source.to_string(),
                span,
                side: side.to_string(),
            }
            .into()
        })
    }

    fn missing_semicolon(&self, span: SourceSpan) -> ParseError {
        let offset = SourceOffset::from(span.offset() + span.len());
        let semicolon_span = SourceSpan::new(offset, 0);
        MissingSemicolon {
            src: self.source.to_string(),
            span: semicolon_span,
        }
    }

    fn synchronize(&mut self) {
        println!("{:?}", self.peek());

        while !self.is_at_end() {
            if self.peek().unwrap().token_kind == TokenKind::Semicolon {
                return;
            }

            match self.peek().map(|t| &t.token_kind) {
                Some(TokenKind::Print) => return,
                Some(TokenKind::EOF) => return,
                _ => self.advance(),
            }
        }
    }

    pub fn parse(&mut self) -> Vec<Stmt> {
        let mut statements = vec![];
        if self.peek().unwrap().token_kind == TokenKind::EOF {
            return statements;
        } else {
            while !self.is_at_end() {
                let statement = self.statement();
                match statement {
                    Ok(stmt) => statements.push(stmt),
                    Err(err) => {
                        self.errors.push(err);
                        self.synchronize();
                    }
                }
            }
        }
        statements
    }

    fn statement(&mut self) -> ParseResult<Stmt> {
        if self.match_token(&[TokenKind::Print]) {
            return self.print_stmt();
        }
        self.expression_stmt()
    }

    fn expression_stmt(&mut self) -> ParseResult<Stmt> {
        let value = self.expression()?;

        if !self.match_token(&[TokenKind::Semicolon]) {
            let span = self.previous().unwrap().span;
            let error = self.missing_semicolon(span);
            self.errors.push(error.into());
        }
        Ok(Stmt::ExprStmt { expr: value })
    }

    fn print_stmt(&mut self) -> ParseResult<Stmt> {
        let value = self.expression()?;

        if !self.match_token(&[TokenKind::Semicolon]) {
            let span = self.previous().unwrap().span;
            let error = self.missing_semicolon(span);

            self.errors.push(error.into());
        }
        Ok(Stmt::PrintStmt { expr: value })
    }

    fn expression(&mut self) -> ParseResult<Expr> {
        self.equality()
    }

    fn equality(&mut self) -> ParseResult<Expr> {
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

    fn comparison(&mut self) -> ParseResult<Expr> {
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

    fn term(&mut self) -> ParseResult<Expr> {
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

    fn factor(&mut self) -> ParseResult<Expr> {
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

    fn unary(&mut self) -> ParseResult<Expr> {
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

    fn primary(&mut self) -> ParseResult<Expr> {
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
        } else if self.match_token(&[TokenKind::Semicolon]) {
            let error = RedundantSemicolon {
                src: self.source.to_string(),
                span: self.previous().unwrap().span,
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
