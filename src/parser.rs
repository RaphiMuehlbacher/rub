use crate::ast::Expr::{Call, Grouping, Literal, Unary, Variable};
use crate::ast::Stmt::{ExprStmt, PrintStmt, While};
use crate::ast::{
    AssignExpr, BinaryExpr, BinaryOp, CallExpr, Delimiter, Expr, FunDeclStmt, Ident, IfStmt,
    LiteralExpr, LogicalExpr, LogicalOp, Spanned, Stmt, UnaryExpr, UnaryOp, VarDeclStmt, WhileStmt,
};
use crate::error::ParseError::{
    ExpectedExpression, InvalidAssignmentTarget, MismatchedDelimiter, MissingLeftParenthesis,
    MissingOperand, MissingSemicolon, MissingVariableAssignmentName,
    MissingVariableDeclarationName, RedundantParenthesis, RedundantSemicolon, UnclosedBrace,
    UnclosedParenthesis, UnexpectedClosingDelimiter, UnexpectedEOF, UnexpectedToken,
    UnmatchedDelimiter,
};
use crate::{lexer, TokenKind};
use lexer::Token;
use miette::{Report, SourceOffset, SourceSpan};

type ParseResult<T> = Result<T, Report>;

pub struct Parser<'a> {
    tokens: Vec<Token<'a>>,
    position: usize,
    errors: Vec<Report>,
    source: &'a str,
    delimiter_stack: Vec<Delimiter>,
}

impl<'a> Parser<'a> {
    fn current(&self) -> &Token<'a> {
        &self.tokens[self.position]
    }

    fn peek(&self) -> &Token<'a> {
        &self.tokens[self.position + 1]
    }

    fn previous(&self) -> &Token<'a> {
        &self.tokens[self.position - 1]
    }

    fn next_is_eof(&self) -> bool {
        self.current().token_kind == TokenKind::EOF
    }

    fn advance_position(&mut self) {
        if !self.next_is_eof() {
            self.position += 1;
        }
    }

    fn current_is(&self, kind: TokenKind) -> bool {
        match (&self.current().token_kind, &kind) {
            (TokenKind::Number(_), TokenKind::Number(_)) => true,
            (TokenKind::String(_), TokenKind::String(_)) => true,
            (TokenKind::Ident(_), TokenKind::Ident(_)) => true,
            (a, b) => a == b,
        }
    }

    fn matches(&self, kinds: &[TokenKind]) -> bool {
        for kind in kinds {
            if self.current_is(kind.clone()) {
                return true;
            }
        }
        false
    }

    /// token to consume is `current`
    fn consume(&mut self, kinds: &[TokenKind]) -> bool {
        for kind in kinds {
            if self.current_is(kind.clone()) {
                self.advance_position();
                return true;
            }
        }
        false
    }
}

impl<'a> Parser<'a> {
    /// * `start` - Starting span (inclusive)
    /// * `end` - Ending span (inclusive)
    fn create_span(&self, start: SourceSpan, end: SourceSpan) -> SourceSpan {
        let left = SourceOffset::from(start.offset());
        let right = end.offset() + end.len();
        let length = right - left.offset();

        SourceSpan::new(left, length)
    }

    fn next_span(&self, current_span: SourceSpan) -> SourceSpan {
        let offset = SourceOffset::from(current_span.offset() + current_span.len());
        SourceSpan::new(offset, 0)
    }
}

impl<'a> Parser<'a> {
    pub fn get_errors(self) -> Vec<Report> {
        self.errors
    }

    fn report(&mut self, error: Report) {
        self.errors.push(error);
    }

    fn expect_semicolon(&mut self) {
        if !self.consume(&[TokenKind::Semicolon]) {
            let previous_span = self.previous().span;
            let next_span = self.next_span(previous_span);
            let error = MissingSemicolon {
                src: self.source.to_string(),
                span: next_span,
            };
            self.report(error.into());
            self.skip_to_next_stmt();
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
}

impl<'a> Parser<'a> {
    fn eat_to_tokens(&mut self, tokens: &[TokenKind]) {
        while !self.matches(tokens) && !self.next_is_eof() {
            self.advance_position();
        }
    }

    /// stops before block ending
    fn skip_to_next_stmt(&mut self) {
        while !self.matches(&[TokenKind::Semicolon, TokenKind::RightBrace]) && !self.next_is_eof() {
            self.advance_position();
        }
        if self.matches(&[TokenKind::Semicolon]) {
            self.advance_position();
        }
    }

    fn skip_to_next_block(&mut self) {
        self.eat_to_tokens(&[TokenKind::LeftBrace]);
        self.advance_position();
    }
}

impl<'a> Parser<'a> {
    /// current is the opening delimiter, end is the next token
    fn open_delimiter(&mut self, open_delim: TokenKind) -> ParseResult<()> {
        let current_token = self.current().clone();
        match open_delim {
            TokenKind::LeftParen | TokenKind::LeftBrace => {
                self.delimiter_stack.push(Delimiter {
                    delimiter: open_delim,
                    span: current_token.span,
                });
                self.advance_position();
                Ok(())
            }
            _ => {
                self.advance_position();
                Err(UnexpectedToken {
                    src: self.source.to_string(),
                    span: current_token.span,
                    found: current_token.token_kind,
                    expected: "an opening delimiter".to_string(),
                }
                .into())
            }
        }
    }

    /// current is closing delimiter, end is the next token
    fn close_delimiter(&mut self, close_delim: TokenKind) -> ParseResult<()> {
        if self.delimiter_stack.is_empty() {
            self.advance_position();
            return Err(UnexpectedClosingDelimiter {
                src: self.source.to_string(),
                delimiter: close_delim,
                span: self.previous().span,
            }
            .into());
        }

        let last_delimiter = self.delimiter_stack.pop().unwrap();
        let expected_closing = match last_delimiter.delimiter {
            TokenKind::LeftParen => TokenKind::RightParen,
            TokenKind::LeftBrace => TokenKind::RightBrace,
            _ => unreachable!("Invalid opening delimiter"),
        };

        match close_delim {
            TokenKind::RightParen if last_delimiter.delimiter == TokenKind::LeftParen => {
                self.advance_position();
                Ok(())
            }
            TokenKind::RightBrace if last_delimiter.delimiter == TokenKind::LeftBrace => {
                self.advance_position();
                Ok(())
            }
            _ => Err(UnmatchedDelimiter {
                src: self.source.to_string(),
                opening_span: last_delimiter.span,
                closing_span: self.current().span,
                expected: expected_closing,
            }
            .into()),
        }
    }
}

impl<'a> Parser<'a> {
    pub fn new(tokens: Vec<Token<'a>>, source: &'a str) -> Self {
        Self {
            tokens,
            position: 0,
            errors: vec![],
            source,
            delimiter_stack: vec![],
        }
    }

    pub fn parse(&mut self) -> Vec<Stmt> {
        let mut statements = vec![];
        if self.matches(&[TokenKind::EOF]) {
            return statements;
        }

        while !self.next_is_eof() {
            let statement = self.declaration();
            match statement {
                Ok(stmt) => statements.push(stmt),
                Err(err) => {
                    self.report(err);
                    self.skip_to_next_stmt();
                }
            }
        }
        statements
    }

    fn declaration(&mut self) -> ParseResult<Stmt> {
        if self.matches(&[TokenKind::Var]) {
            return self.var_declaration();
        } else if self.matches(&[TokenKind::Fun]) {
            return self.fun_declaration();
        }
        self.statement()
    }

    fn var_declaration(&mut self) -> ParseResult<Stmt> {
        let var_keyword_span = self.current().span;
        self.advance_position();

        let variable_name = self.parse_variable_name()?;

        let initializer = self.parse_var_initializer()?;
        self.expect_semicolon();

        Ok(Stmt::VarDecl(Spanned {
            node: VarDeclStmt {
                name: variable_name,
                initializer,
            },
            span: self.create_span(var_keyword_span, self.current().span),
        }))
    }

    fn parse_variable_name(&mut self) -> ParseResult<Ident> {
        let var_keyword_span = self.previous().span;
        let variable_token = self.current().clone();

        let variable_name = match &variable_token.token_kind {
            TokenKind::Ident(name) => {
                let variable_span = variable_token.span;
                self.advance_position();
                Ident::new(name, variable_span)
            }
            TokenKind::Number(_) => {
                if self.matches(&[TokenKind::Ident(String::new())]) {
                    return Err(InvalidAssignmentTarget {
                        src: self.source.to_string(),
                        span: variable_token.span,
                        message: "A variable cannot start with a number".to_string(),
                    }
                    .into());
                }
                return Err(InvalidAssignmentTarget {
                    src: self.source.to_string(),
                    span: variable_token.span,
                    message: "A variable name cannot be a number".to_string(),
                }
                .into());
            }
            TokenKind::Semicolon | TokenKind::Equal => {
                return Err(MissingVariableDeclarationName {
                    src: self.source.to_string(),
                    span: var_keyword_span,
                }
                .into());
            }
            _ => {
                return Err(UnexpectedToken {
                    src: self.source.to_string(),
                    span: variable_token.span,
                    found: variable_token.token_kind.clone(),
                    expected: "an identifier".to_string(),
                }
                .into());
            }
        };

        Ok(variable_name)
    }

    fn parse_var_initializer(&mut self) -> ParseResult<Option<Expr>> {
        let initializer = if self.consume(&[TokenKind::Equal]) {
            if self.consume(&[TokenKind::Semicolon]) {
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
        Ok(initializer)
    }

    fn fun_declaration(&mut self) -> ParseResult<Stmt> {
        let fun_keyword_span = self.current().span;
        self.advance_position();

        let function_name = self.parse_function_name()?;

        let parameters = self.parse_function_parameters()?;

        let body = self.block()?;

        Ok(Stmt::FunDecl(Spanned {
            node: FunDeclStmt {
                name: function_name,
                params: parameters,
                body: Box::new(body),
            },
            span: self.create_span(fun_keyword_span, self.previous().span),
        }))
    }

    /// current is function name, ends at '('
    fn parse_function_name(&mut self) -> ParseResult<Ident> {
        let function_token = self.current().clone();

        let function_name = match &function_token.token_kind {
            TokenKind::Ident(name) => {
                self.advance_position();
                Ident::new(name, function_token.span)
            }
            TokenKind::Number(_) => {
                if self.matches(&[TokenKind::Ident(String::new())]) {
                    return Err(InvalidAssignmentTarget {
                        src: self.source.to_string(),
                        span: function_token.span,
                        message: "A function name cannot start with a number".to_string(),
                    }
                    .into());
                }
                return Err(InvalidAssignmentTarget {
                    src: self.source.to_string(),
                    span: function_token.span,
                    message: "A function name name cannot be a number".to_string(),
                }
                .into());
            }
            _ => {
                panic!("Should skip after the function");
                return Err(UnexpectedToken {
                    src: self.source.to_string(),
                    span: function_token.span,
                    found: function_token.token_kind.clone(),
                    expected: "an identifier".to_string(),
                }
                .into());
            }
        };
        Ok(function_name)
    }

    /// current is '(' ends after ')'
    fn parse_function_parameters(&mut self) -> ParseResult<Vec<Ident>> {
        let mut parameters = vec![];
        self.open_delimiter(self.current().token_kind.clone())?;

        if self.consume(&[TokenKind::RightParen]) {
            self.close_delimiter(self.current().token_kind.clone())?;
            return Ok(parameters);
        }

        loop {
            let curr_token = self.current();
            match &curr_token.token_kind {
                TokenKind::Ident(name) => {
                    let span = self.current().span;
                    parameters.push(Ident::new(name, span));
                    self.advance_position();

                    match self.current().token_kind {
                        TokenKind::Comma => {
                            self.advance_position();
                            if self.current_is(TokenKind::RightParen) {
                                // ExpectedIdent
                                todo!();
                                return Err(ExpectedExpression {
                                    src: self.source.to_string(),
                                    span: self.previous().span,
                                }
                                .into());
                            }
                        }
                        TokenKind::RightParen => {
                            self.close_delimiter(self.current().token_kind.clone())?;
                            break;
                        }
                        TokenKind::EOF => {
                            return Err(UnexpectedEOF {
                                src: self.source.to_string(),
                                expected: "')' after function parameters".to_string(),
                            }
                            .into());
                        }
                        _ => {
                            return Err(UnexpectedToken {
                                src: self.source.to_string(),
                                span: self.current().span,
                                found: self.current().token_kind.clone(),
                                expected: "',', or ')'".to_string(),
                            }
                            .into());
                        }
                    }
                }
                TokenKind::EOF => {
                    return Err(UnexpectedEOF {
                        src: self.source.to_string(),
                        expected: "')' after function parameters".to_string(),
                    }
                    .into());
                }
                _ => {
                    // ExpectedIdent
                    return Err(ExpectedExpression {
                        src: self.source.to_string(),
                        span: curr_token.span,
                    }
                    .into());
                }
            }
        }
        Ok(parameters)
    }

    /// current is the start of the statement
    fn statement(&mut self) -> ParseResult<Stmt> {
        if self.matches(&[TokenKind::Print]) {
            return self.print_stmt();
        } else if self.matches(&[TokenKind::LeftBrace]) {
            return self.block();
        } else if self.matches(&[TokenKind::If]) {
            return self.if_stmt();
        } else if self.matches(&[TokenKind::While]) {
            return self.while_stmt();
        } else if self.matches(&[TokenKind::For]) {
            return self.for_stmt();
        }
        self.expression_stmt()
    }

    /// current is start of the statement, end is next statement
    fn expression_stmt(&mut self) -> ParseResult<Stmt> {
        let left_span = self.current().span;
        let value = self.expression()?;

        self.expect_semicolon();

        Ok(ExprStmt(Spanned {
            node: value,
            span: self.create_span(left_span, self.previous().span),
        }))
    }

    /// current is 'print', end is next statement
    fn print_stmt(&mut self) -> ParseResult<Stmt> {
        let left_span = self.current().span;
        self.advance_position();

        let value = self.expression()?;

        self.expect_semicolon();

        Ok(PrintStmt(Spanned {
            node: value,
            span: self.create_span(left_span, self.previous().span),
        }))
    }

    /// current is '{' and ends after '}'
    fn block(&mut self) -> ParseResult<Stmt> {
        let opening_brace_span = self.current().span;
        self.open_delimiter(self.current().token_kind.clone())?;

        let mut statements = vec![];
        while !self.matches(&[TokenKind::RightBrace]) && !self.next_is_eof() {
            let statement = self.declaration();
            match statement {
                Ok(stmt) => statements.push(stmt),
                Err(err) => {
                    self.report(err);
                    self.skip_to_next_stmt();
                }
            }
        }
        println!("{:?}", self.current());
        self.close_delimiter(self.current().token_kind.clone())?;

        Ok(Stmt::Block(Spanned {
            node: statements,
            span: self.create_span(opening_brace_span, self.previous().span),
        }))
    }

    /// start is `if`, end is next statement
    fn if_stmt(&mut self) -> ParseResult<Stmt> {
        let if_span = self.current().span;
        self.advance_position();
        let condition = self.parse_condition()?;

        let then_branch = self.block()?;

        let mut else_branch = None;
        if self.consume(&[TokenKind::Else]) {
            else_branch = Some(Box::new(self.block()?));
        }

        Ok(Stmt::If(Spanned {
            node: IfStmt {
                condition,
                then_branch: Box::new(then_branch),
                else_branch,
            },
            span: self.create_span(if_span, self.previous().span),
        }))
    }

    /// starts at first condition token, ends after the condition
    fn parse_condition(&mut self) -> ParseResult<Expr> {
        let left_condition_span = self.current().span;
        let condition = match self.expression() {
            Ok(con) => {
                if let Grouping(Spanned { node: _, span: _ }) = &con {
                    self.report(
                        RedundantParenthesis {
                            src: self.source.to_string(),
                            first: left_condition_span,
                            second: self.previous().span,
                        }
                        .into(),
                    );
                }
                con
            }
            Err(err) => {
                self.report(err.into());
                Literal(Spanned {
                    node: LiteralExpr::Bool(true),
                    span: self.create_span(left_condition_span, self.previous().span),
                })
            }
        };
        Ok(condition)
    }

    /// start is `while`, end is next statement
    fn while_stmt(&mut self) -> ParseResult<Stmt> {
        let while_span = self.current().span;
        self.advance_position();

        let condition = self.parse_condition()?;
        println!("{:?}", self.current());
        let block = self.block()?;
        println!("{:?}", self.current());

        Ok(While(Spanned {
            node: WhileStmt {
                condition,
                body: Box::new(block),
            },
            span: self.create_span(while_span, self.previous().span),
        }))
    }

    fn for_stmt(&mut self) -> ParseResult<Stmt> {
        todo!();
        // let if_left_span = self.current().span;
        // if !self.consume(&[TokenKind::LeftParen]) {
        //     let error = MissingLeftParenthesis {
        //         src: self.source.to_string(),
        //         span: self.peek().unwrap().span,
        //         paren_type: "for".to_string(),
        //     };
        //     self.report(error.into());
        // }
        //
        // let mut initializer = None;
        // if self.consume(&[TokenKind::Var]) {
        //     let expr = self.var_declaration()?;
        //     initializer = Some(expr);
        // } else if !self.consume(&[TokenKind::Semicolon]) {
        //     let expr = self.expression_stmt()?;
        //     initializer = Some(expr);
        // }
        //
        // let mut condition = Literal(Spanned {
        //     node: Literal(Spanned {
        //         node: Bool(true),
        //         span: self.previous().span,
        //     }),
        //     span: self.previous().span,
        // });
        //
        // if !self.current_is(TokenKind::Semicolon) {
        //     let expr = self.expression()?;
        //     condition = expr;
        // }
        //
        // if !self.consume(&[TokenKind::Semicolon]) {
        //     let error = MissingSemicolon {
        //         src: self.source.to_string(),
        //         span: self.previous().span,
        //     };
        //     self.report(error.into());
        // }
        //
        // let increment_left_span = self.peek().unwrap().span;
        // let mut increment = None;
        // if !self.current_is(TokenKind::RightParen) {
        //     let expr = self.expression()?;
        //     increment = Some(expr);
        // }
        //
        // if !self.consume(&[TokenKind::RightParen]) {
        //     let error = MissingRightParenthesis {
        //         src: self.source.to_string(),
        //         span: self.peek().unwrap().span,
        //         paren_type: "for".to_string(),
        //     };
        //     self.report(error.into());
        // }
        //
        // let mut body = self.statement()?;
        //
        // if let Some(increment) = increment {
        //     body = Stmt::Block {
        //         stmts: vec![
        //             body,
        //             ExprStmt {
        //                 expr: increment,
        //                 span: self.create_span(increment_left_span, self.previous().span),
        //             },
        //         ],
        //         span: self.create_span(if_left_span, self.previous().span),
        //     }
        // }
        //
        // body = While {
        //     condition,
        //     body: Box::new(body),
        //     span: self.create_span(if_left_span, self.previous().span),
        // };
        //
        // if let Some(initializer) = initializer {
        //     body = Stmt::Block {
        //         stmts: vec![initializer, body],
        //         span: self.create_span(if_left_span, self.previous().span),
        //     };
        // }
        //
        // Ok(body)
    }

    /// starts at first token, ends after the last token of the expression
    fn expression(&mut self) -> ParseResult<Expr> {
        self.assignment()
    }

    fn assignment(&mut self) -> ParseResult<Expr> {
        let left_assignment_span = self.current().span;
        let expr = self.logic_or()?;

        if self.consume(&[TokenKind::Equal]) {
            let equal_span = self.previous().span;

            let result = self.expression();
            let value = match result {
                Ok(val) => val,
                Err(_) => {
                    return Err(ExpectedExpression {
                        src: self.source.to_string(),
                        span: self.previous().span,
                    }
                    .into())
                }
            };

            return match expr {
                Variable(variable_ident) => Ok(Expr::Assign(Spanned {
                    node: AssignExpr {
                        target: variable_ident.clone(),
                        value: Box::new(value),
                    },
                    span: variable_ident.span,
                })),
                // Literal(Literal::Number { value: _, span }) => {
                //     if let Some(next_token) = self.peek() {
                //         if matches!(next_token.token_kind, TokenKind::Ident(_)) {
                //             return Err(InvalidAssignmentTarget {
                //                 src: self.source.to_string(),
                //                 span: self.create_span(left_span, self.previous().span),
                //                 message: "A variable cannot start with a number".to_string(),
                //             }
                //             .into());
                //         }
                //     }
                //
                //     Err(InvalidAssignmentTarget {
                //         src: self.source.to_string(),
                //         span,
                //         message: "Cannot assign to a number literal".to_string(),
                //     }
                //     .into())
                // }
                _ => Err(MissingVariableAssignmentName {
                    src: self.source.to_string(),
                    span: equal_span,
                }
                .into()),
            };
        }
        Ok(expr)
    }

    fn logic_or(&mut self) -> ParseResult<Expr> {
        let logic_or_left_span = self.current().span;
        let mut expr = self.logic_and()?;

        while self.consume(&[TokenKind::Or]) {
            let operator = self.previous();

            let op = match operator.token_kind {
                TokenKind::Or => LogicalOp::Or,
                _ => unreachable!(),
            };

            if self.current_is(TokenKind::Semicolon) {
                let error = ExpectedExpression {
                    src: self.source.to_string(),
                    span: self.current().span,
                };
                self.report(error.into());

                return Ok(Expr::Logical(Spanned {
                    node: LogicalExpr {
                        left: Box::new(expr),
                        op,
                        right: Box::new(Literal(Spanned {
                            node: LiteralExpr::Bool(false),
                            span: self.current().span,
                        })),
                    },
                    span: self.create_span(logic_or_left_span, self.current().span),
                }));
            }

            let right = self.logic_and()?;

            expr = Expr::Logical(Spanned {
                node: LogicalExpr {
                    left: Box::new(expr),
                    op,
                    right: Box::new(right),
                },
                span: self.create_span(logic_or_left_span, self.previous().span),
            })
        }
        Ok(expr)
    }

    fn logic_and(&mut self) -> ParseResult<Expr> {
        let logic_and_left_span = self.current().span;
        let mut expr = self.equality()?;

        while self.consume(&[TokenKind::And]) {
            let operator = self.previous();

            let op = match operator.token_kind {
                TokenKind::And => LogicalOp::And,
                _ => unreachable!(),
            };

            if self.current_is(TokenKind::Semicolon) {
                let error = ExpectedExpression {
                    src: self.source.to_string(),
                    span: self.current().span,
                };
                self.report(error.into());

                return Ok(Expr::Logical(Spanned {
                    node: LogicalExpr {
                        left: Box::new(expr),
                        op,
                        right: Box::new(Literal(Spanned {
                            node: LiteralExpr::Bool(false),
                            span: self.current().span,
                        })),
                    },
                    span: self.create_span(logic_and_left_span, self.current().span),
                }));
            }

            let right = self.equality()?;
            expr = Expr::Logical(Spanned {
                node: LogicalExpr {
                    left: Box::new(expr),
                    op,
                    right: Box::new(right),
                },
                span: self.create_span(logic_and_left_span, self.previous().span),
            });
        }

        Ok(expr)
    }

    fn equality(&mut self) -> ParseResult<Expr> {
        let equality_left_span = self.current().span;
        let mut expr = self.comparison()?;
        while self.consume(&[TokenKind::BangEqual, TokenKind::EqualEqual]) {
            let operator = self.previous();

            let op = match operator.token_kind {
                TokenKind::BangEqual => BinaryOp::BangEqual,
                TokenKind::EqualEqual => BinaryOp::EqualEqual,
                _ => unreachable!(),
            };
            let operator_span = operator.span;
            let result = self.comparison();
            let right = self.expect_expr(result, "right", operator_span)?;
            expr = Expr::Binary(Spanned {
                node: BinaryExpr {
                    left: Box::new(expr),
                    op,
                    right: Box::new(right),
                },
                span: self.create_span(equality_left_span, self.previous().span),
            })
        }
        Ok(expr)
    }

    fn comparison(&mut self) -> ParseResult<Expr> {
        let comparison_left_span = self.current().span;
        let mut expr = self.term()?;
        while self.consume(&[
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

            let operator_span = operator.span;
            let result = self.term();
            let right = self.expect_expr(result, "right", operator_span)?;
            expr = Expr::Binary(Spanned {
                node: BinaryExpr {
                    left: Box::new(expr),
                    op,
                    right: Box::new(right),
                },
                span: self.create_span(comparison_left_span, self.previous().span),
            });
        }
        Ok(expr)
    }

    fn term(&mut self) -> ParseResult<Expr> {
        let term_left_span = self.current().span;
        let mut expr = self.factor()?;
        while self.consume(&[TokenKind::Plus, TokenKind::Minus]) {
            let operator = self.previous();

            let op = match operator.token_kind {
                TokenKind::Plus => BinaryOp::Plus,
                TokenKind::Minus => BinaryOp::Minus,
                _ => unreachable!(),
            };

            let operator_span = operator.span;
            let result = self.factor();
            let right = self.expect_expr(result, "right", operator_span)?;
            expr = Expr::Binary(Spanned {
                node: BinaryExpr {
                    left: Box::new(expr),
                    op,
                    right: Box::new(right),
                },
                span: self.create_span(term_left_span, self.previous().span),
            });
        }
        Ok(expr)
    }

    fn factor(&mut self) -> ParseResult<Expr> {
        let facto_left_span = self.current().span;
        let mut expr = self.unary()?;
        while self.consume(&[TokenKind::Slash, TokenKind::Star]) {
            let operator = self.previous();

            let op = match operator.token_kind {
                TokenKind::Slash => BinaryOp::Slash,
                TokenKind::Star => BinaryOp::Star,
                _ => unreachable!(),
            };

            let operator_span = operator.span;
            let result = self.unary();
            let right = self.expect_expr(result, "right", operator_span)?;
            expr = Expr::Binary(Spanned {
                node: BinaryExpr {
                    left: Box::new(expr),
                    op,
                    right: Box::new(right),
                },
                span: self.create_span(facto_left_span, self.previous().span),
            });
        }
        Ok(expr)
    }

    fn unary(&mut self) -> ParseResult<Expr> {
        let unary_left_span = self.current().span;
        if self.consume(&[TokenKind::Minus, TokenKind::Bang]) {
            let operator = self.previous();

            let op = match operator.token_kind {
                TokenKind::Bang => UnaryOp::Bang,
                TokenKind::Minus => UnaryOp::Minus,
                _ => unreachable!(),
            };

            let operator_span = operator.span;
            let result = self.unary();
            let expr = self.expect_expr(result, "right", operator_span)?;

            Ok(Unary(Spanned {
                node: UnaryExpr {
                    op,
                    expr: Box::new(expr),
                },
                span: self.create_span(unary_left_span, self.previous().span),
            }))
        } else {
            self.call()
        }
    }

    fn call(&mut self) -> ParseResult<Expr> {
        let mut expr = self.primary()?;

        while self.matches(&[TokenKind::LeftParen]) {
            expr = self.finish_call(expr)?;
        }

        Ok(expr)
    }

    // current is '('
    fn finish_call(&mut self, callee: Expr) -> ParseResult<Expr> {
        let left_paren_span = self.current().span;
        self.open_delimiter(self.current().token_kind.clone())?;

        if self.matches(&[TokenKind::EOF, TokenKind::Semicolon]) {
            return Err(UnclosedParenthesis {
                src: self.source.to_string(),
                span: left_paren_span,
            }
            .into());
        }

        let mut arguments = vec![];

        if !self.matches(&[TokenKind::RightParen]) {
            arguments.push(self.expression()?);
            while self.consume(&[TokenKind::Comma]) {
                arguments.push(self.expression()?);
            }
        }

        self.close_delimiter(self.current().token_kind.clone())?;

        Ok(Call(Spanned {
            node: CallExpr {
                callee: Box::new(callee),
                arguments,
            },
            span: self.create_span(left_paren_span, self.previous().span),
        }))
    }

    /// current is token to parse, end is after the token
    fn primary(&mut self) -> ParseResult<Expr> {
        match self.current().token_kind {
            TokenKind::RightBrace | TokenKind::RightParen => {
                let token = self.current();
                self.close_delimiter(token.token_kind.clone())?;
                Err(UnexpectedClosingDelimiter {
                    src: self.source.to_string(),
                    span: self.current().span,
                    delimiter: self.current().token_kind.clone(),
                }
                .into())
            }
            TokenKind::Plus
            | TokenKind::Minus
            | TokenKind::Star
            | TokenKind::Slash
            | TokenKind::Less
            | TokenKind::LessEqual
            | TokenKind::Greater
            | TokenKind::GreaterEqual
            | TokenKind::BangEqual
            | TokenKind::EqualEqual => {
                let operator = self.current().clone();
                self.advance_position();
                let right = self.primary()?;
                Err(MissingOperand {
                    src: self.source.to_string(),
                    span: operator.span,
                    side: "left".to_string(),
                }
                .into())
            }
            TokenKind::False => {
                self.advance_position();
                Ok(Literal(Spanned {
                    node: LiteralExpr::Bool(false),
                    span: self.previous().span,
                }))
            }
            TokenKind::True => {
                self.advance_position();
                Ok(Literal(Spanned {
                    node: LiteralExpr::Bool(true),
                    span: self.previous().span,
                }))
            }
            TokenKind::Nil => {
                self.advance_position();
                Ok(Literal(Spanned {
                    node: LiteralExpr::Nil,
                    span: self.previous().span,
                }))
            }
            TokenKind::LeftParen => {
                let opening_paren_span = self.current().span;
                self.open_delimiter(self.current().token_kind.clone())?;

                let expr = if self.peek().token_kind == TokenKind::RightParen {
                    Err(ExpectedExpression {
                        src: self.source.to_string(),
                        span: self.create_span(opening_paren_span, self.peek().span),
                    }
                    .into())
                } else {
                    self.expression()
                }?;

                self.close_delimiter(self.current().token_kind.clone())?;

                Ok(Grouping(Spanned {
                    node: Box::new(expr),
                    span: self.create_span(opening_paren_span, self.previous().span),
                }))
            }
            TokenKind::Number(value) => {
                let span = self.current().span;
                self.advance_position();

                if matches!(self.current().token_kind, TokenKind::Ident(_)) {
                    return Err(InvalidAssignmentTarget {
                        src: self.source.to_string(),
                        span,
                        message: "A variable cannot start with a number".to_string(),
                    }
                    .into());
                }
                Ok(Literal(Spanned {
                    node: LiteralExpr::Number(value),
                    span,
                }))
            }
            TokenKind::String(ref value) => {
                let span = self.current().span;
                let string = value.clone();
                self.advance_position();
                Ok(Literal(Spanned {
                    node: LiteralExpr::String(string),
                    span,
                }))
            }
            TokenKind::Ident(ref name) => {
                let string = name.clone();
                let span = self.current().span;
                self.advance_position();
                Ok(Variable(Ident::new(&string, span)))
            }
            TokenKind::EOF => Err(UnexpectedEOF {
                src: self.source.to_string(),
                expected: "unexpected EOF".to_string(),
            }
            .into()),
            TokenKind::Semicolon => {
                let span = self.current().span;
                self.advance_position();
                Err(RedundantSemicolon {
                    src: self.source.to_string(),
                    span,
                }
                .into())
            }
            _ => {
                let token = self.current().clone();
                Err(UnexpectedToken {
                    src: self.source.to_string(),
                    span: token.span,
                    found: token.token_kind,
                    expected: "literal or '('".to_string(),
                }
                .into())
            }
        }
    }
}
