use crate::error::ParseError;
use crate::error::ParseError::{
    ExpectedExpression, InvalidAssignmentTarget, MissingOperand, MissingSemicolon,
    MissingVariableAssignmentName, MissingVariableDeclarationName, RedundantSemicolon,
    UnclosedParenthesis, UnexpectedEOF, UnexpectedToken,
};
use crate::{lexer, TokenKind};
use lexer::Token;
use miette::{Error, Report, SourceOffset, SourceSpan};

type ParseResult<T> = Result<T, Report>;

#[derive(Debug)]
pub enum Stmt {
    ExprStmt {
        expr: Expr,
        span: SourceSpan,
    },
    PrintStmt {
        expr: Expr,
        span: SourceSpan,
    },
    VarDecl {
        name: String,
        initializer: Option<Expr>,
        span: SourceSpan,
    },
}

#[derive(Debug)]
pub enum Expr {
    Literal(Literal),
    Unary {
        op: UnaryOp,
        expr: Box<Expr>,
        span: SourceSpan,
    },
    Binary {
        left: Box<Expr>,
        op: BinaryOp,
        right: Box<Expr>,
        span: SourceSpan,
    },
    Grouping {
        expr: Box<Expr>,
        span: SourceSpan,
    },
    Variable {
        name: String,
        span: SourceSpan,
    },
    Assign {
        name: String,
        value: Box<Expr>,
        span: SourceSpan,
    },
}

#[derive(Debug)]
enum Literal {
    Number { value: f64, span: SourceSpan },
    String { value: String, span: SourceSpan },
    Bool { value: bool, span: SourceSpan },
    Nil { span: SourceSpan },
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
        Self {
            tokens,
            position: 0,
            errors: vec![],
            source,
        }
    }

    fn peek(&self) -> Option<&Token<'a>> {
        self.tokens.get(self.position)
    }

    fn previous(&self) -> &Token<'a> {
        &self.tokens[self.position - 1]
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
        self.peek().map_or(false, |t| t.token_kind == token_kind)
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

    fn create_span(&self, start: SourceSpan, end: SourceSpan) -> SourceSpan {
        let left = SourceOffset::from(start.offset());
        let right = end.offset() + end.len();

        SourceSpan::new(left, right)
    }

    pub fn get_errors(&self) -> &Vec<Report> {
        &self.errors
    }

    fn report(&mut self, error: Report) {
        self.errors.push(error.into());
    }

    fn expect_semicolon(&mut self) {
        if !self.match_token(&[TokenKind::Semicolon]) {
            let span = self.previous().span;
            let error = self.missing_semicolon(span);
            self.report(error.into());
        }
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
        self.advance();
        while !self.is_at_end() {
            if self.previous().token_kind == TokenKind::Semicolon {
                return;
            }

            match self.peek().map(|t| &t.token_kind) {
                Some(TokenKind::Print | TokenKind::EOF | TokenKind::Var) => return,
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
                let statement = self.declaration();
                match statement {
                    Ok(stmt) => statements.push(stmt),
                    Err(err) => {
                        self.report(err);
                        self.synchronize();
                    }
                }
            }
        }
        statements
    }

    fn declaration(&mut self) -> ParseResult<Stmt> {
        if self.match_token(&[TokenKind::Var]) {
            return self.var_declaration();
        }
        self.statement()
    }

    fn var_declaration(&mut self) -> ParseResult<Stmt> {
        let next_token = self.peek().unwrap();
        let left_span = next_token.span;

        let variable_name = match &next_token.token_kind {
            TokenKind::Ident(name) => {
                let name_clone = name.clone();
                self.advance();
                name_clone
            }
            TokenKind::Number(_) => {
                self.advance();
                if let Some(next_token) = self.peek() {
                    if matches!(next_token.token_kind, TokenKind::Ident(_)) {
                        return Err(InvalidAssignmentTarget {
                            src: self.source.to_string(),
                            span: left_span,
                            message: "A variable cannot start with a number".to_string(),
                        }
                        .into());
                    }
                }
                return Err(InvalidAssignmentTarget {
                    src: self.source.to_string(),
                    span: left_span,
                    message: "A variable name cannot be a number".to_string(),
                }
                .into());
            }
            TokenKind::Semicolon | TokenKind::Equal => {
                let prev_token = self.previous();
                return Err(MissingVariableDeclarationName {
                    src: self.source.to_string(),
                    span: prev_token.span,
                }
                .into());
            }
            other => {
                return Err(UnexpectedToken {
                    src: self.source.to_string(),
                    span: next_token.span,
                    found: other.clone(),
                    expected: "an identifier".to_string(),
                }
                .into());
            }
        };

        let initializer = if self.match_token(&[TokenKind::Equal]) {
            if self.match_token(&[TokenKind::Semicolon]) {
                return Err(ExpectedExpression {
                    src: self.source.to_string(),
                    span: self.previous().span,
                }
                .into());
            }
            Some(self.expression()?)
        } else {
            None
        };

        self.expect_semicolon();

        Ok(Stmt::VarDecl {
            name: variable_name.to_string(),
            initializer,
            span: self.create_span(left_span, self.previous().span),
        })
    }

    fn statement(&mut self) -> ParseResult<Stmt> {
        if self.match_token(&[TokenKind::Print]) {
            return self.print_stmt();
        }
        self.expression_stmt()
    }

    fn expression_stmt(&mut self) -> ParseResult<Stmt> {
        let left = self.peek().unwrap().span;
        let value = self.expression()?;

        self.expect_semicolon();

        Ok(Stmt::ExprStmt {
            expr: value,
            span: self.create_span(left, self.previous().span),
        })
    }

    fn print_stmt(&mut self) -> ParseResult<Stmt> {
        let left = self.peek().unwrap().span;
        let value = self.expression()?;

        self.expect_semicolon();

        Ok(Stmt::PrintStmt {
            expr: value,
            span: self.create_span(left, self.previous().span),
        })
    }

    fn expression(&mut self) -> ParseResult<Expr> {
        self.assignment()
    }

    fn assignment(&mut self) -> ParseResult<Expr> {
        let expr = self.equality()?;

        if self.match_token(&[TokenKind::Equal]) {
            let equal_span = self.previous().span;

            let result = self.expression();
            let value = match result {
                Ok(val) => val,
                Err(_) => {
                    return Err(ExpectedExpression {
                        src: self.source.to_string(),
                        span: equal_span,
                    }
                    .into())
                }
            };

            return match expr {
                Expr::Variable { name, span } => Ok(Expr::Assign {
                    name,
                    span,
                    value: Box::new(value),
                }),
                Expr::Literal(Literal::Number { value, span }) => {
                    if let Some(next_token) = self.peek() {
                        if matches!(next_token.token_kind, TokenKind::Ident(_)) {
                            return Err(InvalidAssignmentTarget {
                                src: self.source.to_string(),
                                span,
                                message: "A variable cannot start with a number".to_string(),
                            }
                            .into());
                        }
                    }

                    Err(InvalidAssignmentTarget {
                        src: self.source.to_string(),
                        span,
                        message: "Cannot assign to a number literal".to_string(),
                    }
                    .into())
                }
                _ => Err(MissingVariableAssignmentName {
                    src: self.source.to_string(),
                    span: equal_span,
                }
                .into()),
            };
        }
        Ok(expr)
    }

    fn equality(&mut self) -> ParseResult<Expr> {
        let mut expr = self.comparison()?;
        while self.match_token(&[TokenKind::BangEqual, TokenKind::EqualEqual]) {
            let operator = self.previous();

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
                span: self.create_span(span, self.previous().span),
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
            let operator = self.previous();

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
                span: self.create_span(span, self.previous().span),
            };
        }
        Ok(expr)
    }

    fn term(&mut self) -> ParseResult<Expr> {
        let mut expr = self.factor()?;
        while self.match_token(&[TokenKind::Plus, TokenKind::Minus]) {
            let operator = self.previous();

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
                span: self.create_span(span, self.previous().span),
            };
        }
        Ok(expr)
    }

    fn factor(&mut self) -> ParseResult<Expr> {
        let mut expr = self.unary()?;
        while self.match_token(&[TokenKind::Slash, TokenKind::Star]) {
            let operator = self.previous();

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
                span: self.create_span(span, self.previous().span),
            };
        }
        Ok(expr)
    }

    fn unary(&mut self) -> ParseResult<Expr> {
        if self.match_token(&[TokenKind::Minus, TokenKind::Bang]) {
            let operator = self.previous();

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
                span: self.create_span(span, self.previous().span),
            })
        } else {
            self.primary()
        }
    }

    fn primary(&mut self) -> ParseResult<Expr> {
        if self.match_token(&[TokenKind::False]) {
            Ok(Expr::Literal(Literal::Bool {
                value: false,
                span: self.previous().span,
            }))
        } else if self.match_token(&[TokenKind::True]) {
            Ok(Expr::Literal(Literal::Bool {
                value: true,
                span: self.previous().span,
            }))
        } else if self.match_token(&[TokenKind::Nil]) {
            Ok(Expr::Literal(Literal::Nil {
                span: self.previous().span,
            }))
        } else if self.match_token(&[TokenKind::LeftParen]) {
            let opening_paren = self.previous().clone();

            if self.match_token(&[TokenKind::RightParen]) {
                return Ok(Expr::Grouping {
                    expr: Box::new(Expr::Literal(Literal::Nil {
                        span: self.previous().span,
                    })),
                    span: self.create_span(opening_paren.span, self.previous().span),
                });
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
                self.report(error.into())
            }
            Ok(Expr::Grouping {
                expr: Box::new(expr),
                span: self.create_span(opening_paren.span, self.previous().span),
            })
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
            let token = self.previous();
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
                span: self.previous().span,
            };

            Err(error.into())
        } else if let Some(token) = self.peek() {
            match &token.token_kind {
                TokenKind::Number(value) => {
                    let span = token.span.clone();
                    let number = *value;
                    self.advance();

                    if let Some(next_token) = self.peek() {
                        if matches!(next_token.token_kind, TokenKind::Ident(_)) {
                            return Err(InvalidAssignmentTarget {
                                src: self.source.to_string(),
                                span,
                                message: "A variable cannot start with a number".to_string(),
                            }
                            .into());
                        }
                    }
                    Ok(Expr::Literal(Literal::Number {
                        value: number,
                        span,
                    }))
                }
                TokenKind::String(value) => {
                    let span = token.span.clone();
                    let string = value.clone();
                    self.advance();
                    Ok(Expr::Literal(Literal::String {
                        value: string,
                        span,
                    }))
                }
                TokenKind::Ident(name) => {
                    let string = name.clone();
                    let span = token.span;
                    self.advance();
                    Ok(Expr::Variable { name: string, span })
                }
                _ => {
                    let token = token.clone();
                    let error = UnexpectedToken {
                        src: self.source.to_string(),
                        span: token.span,
                        found: token.token_kind,
                        expected: "literal or '('".to_string(),
                    };
                    self.synchronize();
                    Err(error.into())
                }
            }
        } else {
            unreachable!();
        }
    }
}
