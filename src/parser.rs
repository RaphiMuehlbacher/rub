use crate::ast::Expr::{Call, Grouping, Lambda, Literal, Unary, Variable};
use crate::ast::Stmt::{Block, ExprStmt, PrintStmt, Return, While};
use crate::ast::{
    AssignExpr, BinaryExpr, BinaryOp, BlockStmt, CallExpr, Delimiter, Expr, FunDeclStmt, Ident, IfStmt, LambdaExpr, LiteralExpr,
    LogicalExpr, LogicalOp, Parameter, Program, ReturnStmt, Stmt, Typed, UnaryExpr, UnaryOp, VarDeclStmt, WhileStmt,
};
use crate::error::ParseError::{
    ExpectedExpression, ExpectedIdentifier, InvalidFunctionName, InvalidVariableName, MissingBlock, MissingOperand, MissingSemicolon,
    RedundantParenthesis, RedundantSemicolon, UnclosedDelimiter, UnexpectedClosingDelimiter, UnexpectedEOF, UnexpectedToken,
    UnmatchedDelimiter,
};
use crate::type_inferrer::Type;
use crate::{TokenKind, lexer};
use lexer::Token;
use miette::{Report, SourceOffset, SourceSpan};

type ParseResult<T> = Result<T, Report>;

pub struct ParserResult<'a> {
    pub errors: &'a Vec<Report>,
    pub ast: Program,
}

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

    fn at_eof(&self) -> bool {
        self.current().token_kind == TokenKind::EOF
    }

    fn advance_position(&mut self) {
        if !self.at_eof() {
            self.position += 1;
        }
    }

    fn next_is(&self, kind: TokenKind) -> bool {
        match (&self.peek().token_kind, &kind) {
            (TokenKind::Number(_), TokenKind::Number(_)) => true,
            (TokenKind::String(_), TokenKind::String(_)) => true,
            (TokenKind::Ident(_), TokenKind::Ident(_)) => true,
            (a, b) => a == b,
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

    /// token to match is `current`
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
    fn report(&mut self, error: Report) {
        self.errors.push(error);
    }

    /// if `current` is not a left brace it skips the whole block
    fn expect_block(&mut self) -> ParseResult<()> {
        if !self.matches(&[TokenKind::LeftBrace]) {
            let opening_span = self.current().span;
            self.skip_next_block();
            return Err(MissingBlock {
                src: self.source.to_string(),
                span: opening_span,
            }
            .into());
        }
        Ok(())
    }

    /// if `current` is not a semicolon, it skips to the next statement
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

    fn expect_expr(&self, result: ParseResult<Expr>, side: &str, span: SourceSpan) -> ParseResult<Expr> {
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
        while !self.at_eof() && !self.matches(tokens) {
            self.advance_position();
        }
    }

    /// skips past the next semicolon, stops before block ending
    fn skip_to_next_stmt(&mut self) {
        while !self.matches(&[TokenKind::Semicolon, TokenKind::RightBrace]) && !self.at_eof() {
            self.advance_position();
        }
        if self.matches(&[TokenKind::Semicolon]) {
            self.advance_position();
        }
    }

    /// skips until next left brace
    fn skip_to_next_block(&mut self) {
        self.eat_to_tokens(&[TokenKind::LeftBrace]);
    }

    /// skips until next left paren
    fn skip_to_next_paren(&mut self) {
        self.eat_to_tokens(&[TokenKind::LeftParen])
    }

    /// skips past the whole next block
    fn skip_next_block(&mut self) {
        self.eat_to_tokens(&[TokenKind::LeftBrace]);

        let mut brace_count = 1;
        self.advance_position();

        while brace_count > 0 && !self.at_eof() {
            match self.current().token_kind {
                TokenKind::LeftBrace => {
                    brace_count += 1;
                    self.advance_position();
                }
                TokenKind::RightBrace => {
                    brace_count -= 1;
                    self.advance_position();
                }
                _ => self.advance_position(),
            }
        }
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
                span: self.previous().span,
                delimiter: close_delim,
            }
            .into());
        }

        let last_delimiter = self.delimiter_stack.pop().unwrap();
        let expected_closing = match last_delimiter.delimiter {
            TokenKind::LeftParen => TokenKind::RightParen,
            TokenKind::LeftBrace => TokenKind::RightBrace,
            _ => unreachable!("Invalid opening delimiter"),
        };

        if close_delim != expected_closing {
            return Err(UnmatchedDelimiter {
                src: self.source.to_string(),
                opening_span: last_delimiter.span,
                closing_span: self.current().span,
                expected: expected_closing,
                found: self.current().token_kind.clone(),
            }
            .into());
        }
        self.advance_position();
        Ok(())
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

    pub fn parse(&mut self) -> ParserResult {
        let left_program_span = self.current().span;
        let mut statements = vec![];
        if self.matches(&[TokenKind::EOF]) {
            return ParserResult {
                ast: Program {
                    statements,
                    span: self.create_span(left_program_span, self.current().span),
                },
                errors: &self.errors,
            };
        }

        while !self.at_eof() {
            let statement = self.declaration();
            match statement {
                Ok(stmt) => statements.push(stmt),
                Err(err) => {
                    self.report(err);
                    self.skip_to_next_stmt();
                }
            }
        }

        ParserResult {
            ast: Program {
                statements,
                span: self.create_span(left_program_span, self.current().span),
            },
            errors: &self.errors,
        }
    }

    fn declaration(&mut self) -> ParseResult<Stmt> {
        if self.matches(&[TokenKind::Let]) {
            return self.var_declaration();
        } else if self.matches(&[TokenKind::Fn]) {
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

        Ok(Stmt::VarDecl(Typed::new(
            VarDeclStmt {
                ident: variable_name,
                initializer,
            },
            self.create_span(var_keyword_span, self.current().span),
        )))
    }

    fn parse_variable_name(&mut self) -> ParseResult<Ident> {
        let var_keyword_span = self.previous().span;
        let variable_token = self.current().clone();

        let variable_name = match &variable_token.token_kind {
            TokenKind::Ident(name) => {
                let variable_span = variable_token.span;
                self.advance_position();
                Typed::new(name.clone(), variable_span)
            }
            TokenKind::Number(_) => {
                if self.next_is(TokenKind::Ident(String::new())) {
                    self.advance_position();
                    return Err(InvalidVariableName {
                        src: self.source.to_string(),
                        span: self.create_span(variable_token.span, self.current().span),
                        message: "A variable cannot start with a number".to_string(),
                    }
                    .into());
                }
                return Err(InvalidVariableName {
                    src: self.source.to_string(),
                    span: variable_token.span,
                    message: "A variable name cannot be a number".to_string(),
                }
                .into());
            }
            TokenKind::Semicolon | TokenKind::Equal => {
                return Err(ExpectedIdentifier {
                    src: self.source.to_string(),
                    span: var_keyword_span,
                    context: "variable name".to_string(),
                }
                .into());
            }
            _ => {
                return Err(ExpectedIdentifier {
                    src: self.source.to_string(),
                    span: variable_token.span,
                    context: "variable".to_string(),
                }
                .into());
            }
        };

        Ok(variable_name)
    }

    fn parse_var_initializer(&mut self) -> ParseResult<Option<Typed<Expr>>> {
        let initializer = if self.consume(&[TokenKind::Equal]) {
            if self.consume(&[TokenKind::Semicolon]) {
                return Err(ExpectedExpression {
                    src: self.source.to_string(),
                    span: self.previous().span,
                }
                .into());
            }
            let expr_left_span = self.current().span;
            Some(Typed::new(
                self.expression()?,
                self.create_span(expr_left_span, self.current().span),
            ))
        } else if self.matches(&[TokenKind::Semicolon]) {
            None
        } else {
            return Err(UnexpectedToken {
                src: self.source.to_string(),
                span: self.current().span,
                expected: "'=' or ';'".to_string(),
                found: self.current().token_kind.clone(),
            }
            .into());
        };
        Ok(initializer)
    }

    fn fun_declaration(&mut self) -> ParseResult<Stmt> {
        let fun_keyword_span = self.current().span;
        self.advance_position();

        let function_name = self.parse_function_name()?;

        let parameters = self.parse_function_parameters()?;
        let return_type = self.parse_return_type()?;

        let body = self.block()?;

        Ok(Stmt::FunDecl(Typed::new(
            FunDeclStmt {
                ident: function_name,
                params: parameters,
                body,
                return_type,
            },
            self.create_span(fun_keyword_span, self.previous().span),
        )))
    }

    fn parse_return_type(&mut self) -> ParseResult<Type> {
        if !self.consume(&[TokenKind::Arrow]) {
            return Ok(Type::Nil);
        }

        match self.current().token_kind {
            TokenKind::TypeFloat => {
                self.advance_position();
                Ok(Type::Float)
            }
            TokenKind::TypeString => {
                self.advance_position();
                Ok(Type::String)
            }
            TokenKind::TypeBool => {
                self.advance_position();
                Ok(Type::Bool)
            }
            TokenKind::TypeNil => {
                self.advance_position();
                Ok(Type::Nil)
            }
            _ => Err(UnexpectedToken {
                src: self.source.to_string(),
                span: self.current().span,
                expected: "type".to_string(),
                found: self.current().token_kind.clone(),
            }
            .into()),
        }
    }

    /// current is function name, ends at '('
    fn parse_function_name(&mut self) -> ParseResult<Ident> {
        let function_token = self.current().clone();

        let function_name = match &function_token.token_kind {
            TokenKind::Ident(name) => {
                self.advance_position();
                Typed::new(name.clone(), function_token.span)
            }
            TokenKind::Number(_) => {
                if self.next_is(TokenKind::Ident(String::new())) {
                    self.skip_to_next_paren();
                    self.report(
                        InvalidFunctionName {
                            src: self.source.to_string(),
                            span: self.create_span(function_token.span, self.current().span),
                            message: "A function name cannot start with a number".to_string(),
                        }
                        .into(),
                    );
                    Typed::new("err_fun".to_string(), self.current().span)
                } else {
                    self.skip_to_next_paren();
                    self.report(
                        InvalidFunctionName {
                            src: self.source.to_string(),
                            span: function_token.span,
                            message: "A function name name cannot be a number".to_string(),
                        }
                        .into(),
                    );
                    Typed::new("err fun".to_string(), self.current().span)
                }
            }
            _ => {
                self.skip_to_next_paren();
                return Err(ExpectedIdentifier {
                    src: self.source.to_string(),
                    span: function_token.span,
                    context: "function".to_string(),
                }
                .into());
            }
        };
        Ok(function_name)
    }

    /// current is `:` end is after type
    fn parse_type_annotation(&mut self) -> ParseResult<Type> {
        if !self.consume(&[TokenKind::Colon]) {
            return Err(UnexpectedToken {
                src: self.source.to_string(),
                span: self.current().span,
                expected: "type".to_string(),
                found: self.current().token_kind.clone(),
            }
            .into());
        }

        self.parse_type()
    }

    /// current is the type annotation
    fn parse_type(&mut self) -> ParseResult<Type> {
        if self.matches(&[TokenKind::LeftParen]) {
            self.open_delimiter(self.current().token_kind.clone())?;
            let mut param_types = vec![];

            if !self.matches(&[TokenKind::RightParen]) {
                param_types.push(Box::new(self.parse_type()?));
                while self.consume(&[TokenKind::Comma]) {
                    param_types.push(Box::new(self.parse_type()?));
                }
            }

            self.close_delimiter(TokenKind::RightParen)?;

            if !self.consume(&[TokenKind::Arrow]) {
                return Err(UnexpectedToken {
                    src: self.source.to_string(),
                    span: self.current().span,
                    expected: "'->'".to_string(),
                    found: self.current().token_kind.clone(),
                }
                .into());
            }

            let return_type = Box::new(self.parse_type()?);
            Ok(Type::Function {
                params: param_types,
                return_ty: return_type,
            })
        } else {
            match self.current().token_kind {
                TokenKind::TypeFloat => {
                    self.advance_position();
                    Ok(Type::Float)
                }
                TokenKind::TypeString => {
                    self.advance_position();
                    Ok(Type::String)
                }
                TokenKind::TypeBool => {
                    self.advance_position();
                    Ok(Type::Bool)
                }
                TokenKind::TypeNil => {
                    self.advance_position();
                    Ok(Type::Nil)
                }
                _ => Err(UnexpectedToken {
                    src: self.source.to_string(),
                    span: self.current().span,
                    expected: "type".to_string(),
                    found: self.current().token_kind.clone(),
                }
                .into()),
            }
        }
    }

    fn parse_parameter(&mut self) -> ParseResult<Typed<Parameter>> {
        let curr_token = self.current().clone();

        match &curr_token.token_kind {
            TokenKind::Ident(name) => {
                let name_span = curr_token.span;
                self.advance_position();

                let type_annotation = self.parse_type_annotation()?;

                Ok(Typed::new(
                    Parameter {
                        name: Typed::new(name.clone(), name_span),
                        type_annotation,
                    },
                    self.create_span(curr_token.span, self.previous().span),
                ))
            }
            _ => {
                self.skip_next_block();
                Err(ExpectedIdentifier {
                    src: self.source.to_string(),
                    span: curr_token.span,
                    context: "parameter".to_string(),
                }
                .into())
            }
        }
    }

    /// current is '(' ends after ')'
    fn parse_function_parameters(&mut self) -> ParseResult<Vec<Typed<Parameter>>> {
        let mut parameters = vec![];
        let opening_paren_span = self.current().span;

        self.open_delimiter(self.current().token_kind.clone())?;

        if self.matches(&[TokenKind::RightParen]) {
            self.close_delimiter(self.current().token_kind.clone())?;
            return Ok(parameters);
        }

        loop {
            if self.matches(&[TokenKind::EOF]) {
                return Err(UnclosedDelimiter {
                    src: self.source.to_string(),
                    span: opening_paren_span,
                    delimiter: TokenKind::LeftParen,
                }
                .into());
            }

            let parameter = self.parse_parameter()?;
            parameters.push(parameter);

            match self.current().token_kind {
                TokenKind::Comma => {
                    self.advance_position();
                    if self.current_is(TokenKind::RightParen) {
                        return Err(ExpectedIdentifier {
                            src: self.source.to_string(),
                            span: self.previous().span,
                            context: "parameter".to_string(),
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
        Ok(parameters)
    }

    /// current is the start of the statement
    fn statement(&mut self) -> ParseResult<Stmt> {
        if self.matches(&[TokenKind::Print]) {
            return self.print_stmt();
        } else if self.matches(&[TokenKind::LeftBrace]) {
            return Ok(Block(self.block()?));
        } else if self.matches(&[TokenKind::If]) {
            return self.if_stmt();
        } else if self.matches(&[TokenKind::While]) {
            return self.while_stmt();
        } else if self.matches(&[TokenKind::For]) {
            return self.for_stmt();
        } else if self.matches(&[TokenKind::Return]) {
            return self.return_stmt();
        }
        self.expression_stmt()
    }

    /// current is start of the statement, end is next statement
    fn expression_stmt(&mut self) -> ParseResult<Stmt> {
        let left_span = self.current().span;
        let value = self.expression()?;

        self.expect_semicolon();

        Ok(ExprStmt(Typed::new(value, self.create_span(left_span, self.previous().span))))
    }

    /// current is 'print', end is next statement
    fn print_stmt(&mut self) -> ParseResult<Stmt> {
        let left_span = self.current().span;
        self.advance_position();

        let value = self.expression()?;

        self.expect_semicolon();

        Ok(PrintStmt(Typed::new(value, self.create_span(left_span, self.previous().span))))
    }

    /// current is '{' and ends after '}'
    fn block(&mut self) -> ParseResult<Typed<BlockStmt>> {
        let opening_brace_span = self.current().span;
        self.open_delimiter(self.current().token_kind.clone())?;

        let mut statements = vec![];
        while !self.matches(&[TokenKind::RightBrace]) && !self.at_eof() {
            let statement = self.declaration();
            match statement {
                Ok(stmt) => statements.push(stmt),
                Err(err) => {
                    self.report(err);
                    self.skip_to_next_stmt();
                }
            }
        }
        self.close_delimiter(self.current().token_kind.clone())?;

        Ok(Typed::new(
            BlockStmt { statements },
            self.create_span(opening_brace_span, self.previous().span),
        ))
    }

    /// start is `if`, end is next statement
    fn if_stmt(&mut self) -> ParseResult<Stmt> {
        let if_span = self.current().span;
        self.advance_position();
        let condition_span = self.current().span;
        let condition = self.parse_condition()?;

        let then_branch = self.block()?;

        let mut else_branch = None;
        if self.consume(&[TokenKind::Else]) {
            else_branch = Some(self.block()?);
        }

        Ok(Stmt::If(Typed::new(
            IfStmt {
                condition: Typed::new(condition, condition_span),
                then_branch,
                else_branch,
            },
            self.create_span(if_span, self.previous().span),
        )))
    }

    /// starts at first condition token, ends after the condition
    fn parse_condition(&mut self) -> ParseResult<Expr> {
        let expr_left_span = self.current().span;
        let expr = match self.expression() {
            Ok(expr) => {
                if let Grouping(_) = &expr {
                    self.report(
                        RedundantParenthesis {
                            src: self.source.to_string(),
                            first: expr_left_span,
                            second: self.previous().span,
                        }
                        .into(),
                    );
                }
                expr
            }
            Err(_) => Literal(LiteralExpr::Bool(true)),
        };
        Ok(expr)
    }

    /// start is `while`, end is next statement
    fn while_stmt(&mut self) -> ParseResult<Stmt> {
        let while_span = self.current().span;
        self.advance_position();

        let condition_span = self.current().span;
        let condition = Typed::new(self.parse_condition()?, condition_span);

        let block = self.block()?;

        Ok(While(Typed::new(
            WhileStmt { condition, body: block },
            self.create_span(while_span, self.previous().span),
        )))
    }

    /// current is for, end is after block
    fn for_stmt(&mut self) -> ParseResult<Stmt> {
        let for_span = self.current().span;
        self.advance_position();

        let initializer = if self.matches(&[TokenKind::Let]) {
            Some(self.var_declaration()?)
        } else if !self.consume(&[TokenKind::Semicolon]) {
            Some(self.expression_stmt()?)
        } else {
            None
        };

        let condition_span = self.current().span;
        let condition = if !self.matches(&[TokenKind::Semicolon]) {
            self.expression()?
        } else {
            Literal(LiteralExpr::Bool(true))
        };
        let condition = Typed::new(condition, condition_span);

        if !self.consume(&[TokenKind::Semicolon]) {
            let error = MissingSemicolon {
                src: self.source.to_string(),
                span: self.previous().span,
            };
            self.report(error.into());
        }

        let increment = if !self.matches(&[TokenKind::LeftBrace]) {
            Some(self.expression()?)
        } else {
            None
        };

        let body = self.block()?;
        let mut statements = vec![];

        if let Some(init) = initializer {
            statements.push(init);
        }

        let mut while_body_statements = Vec::new();
        while_body_statements.extend(body.node.statements);

        if let Some(inc) = increment {
            while_body_statements.push(ExprStmt(Typed::new(inc, self.create_span(for_span, self.previous().span))));
        }

        let while_stmt = While(Typed::new(
            WhileStmt {
                condition,
                body: Typed::new(
                    BlockStmt {
                        statements: while_body_statements,
                    },
                    body.span,
                ),
            },
            self.create_span(for_span, self.previous().span),
        ));
        statements.push(while_stmt);

        Ok(Block(Typed::new(
            BlockStmt { statements },
            self.create_span(for_span, self.previous().span),
        )))
    }

    /// current is `return` end is next statement
    fn return_stmt(&mut self) -> ParseResult<Stmt> {
        let left_return_span = self.current().span;
        self.advance_position();

        let value = if !self.matches(&[TokenKind::Semicolon]) {
            let left_expr_span = self.current().span;
            if self.matches(&[TokenKind::EOF]) {
                return Err(ExpectedExpression {
                    src: self.source.to_string(),
                    span: self.current().span,
                }
                .into());
            }
            Some(Typed::new(
                self.expression()?,
                self.create_span(left_expr_span, self.previous().span),
            ))
        } else {
            None
        };

        self.expect_semicolon();
        Ok(Return(Typed::new(
            ReturnStmt { expr: value },
            self.create_span(left_return_span, self.previous().span),
        )))
    }

    /// starts at first token, ends after the last token of the expression
    fn expression(&mut self) -> ParseResult<Expr> {
        if self.matches(&[TokenKind::Fn]) {
            return self.lambda_expr();
        }
        self.assignment()
    }

    fn lambda_expr(&mut self) -> ParseResult<Expr> {
        self.advance_position();

        let parameters = self.parse_function_parameters()?;
        let return_type = self.parse_return_type()?;
        let block = self.block()?;

        Ok(Lambda(LambdaExpr {
            parameters,
            body: block,
            return_type,
        }))
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
                    .into());
                }
            };

            return match expr {
                Variable(name) => Ok(Expr::Assign(AssignExpr {
                    target: name,
                    value: Box::new(Typed::new(value, self.create_span(left_assignment_span, self.current().span))),
                })),
                _ => Err(ExpectedIdentifier {
                    src: self.source.to_string(),
                    span: equal_span,
                    context: "variable name".to_string(),
                }
                .into()),
            };
        }
        Ok(expr)
    }

    fn logic_or(&mut self) -> ParseResult<Expr> {
        let expr_left_span = self.current().span;
        let mut expr = self.logic_and()?;
        let expr_right_span = self.previous().span;

        while self.consume(&[TokenKind::Or]) {
            let operator = self.previous();

            let op = match operator.token_kind {
                TokenKind::Or => LogicalOp::Or,
                _ => unreachable!(),
            };

            let operator_span = operator.span;
            let right_left_span = self.current().span;

            let result = self.logic_and();
            let right_right_span = self.current().span;

            let right = self.expect_expr(result, "right", operator_span)?;

            expr = Expr::Logical(LogicalExpr {
                left: Box::new(Typed::new(expr, self.create_span(expr_left_span, expr_right_span))),
                op: Typed::new(op, operator_span),
                right: Box::new(Typed::new(right, self.create_span(right_left_span, right_right_span))),
            })
        }
        Ok(expr)
    }

    fn logic_and(&mut self) -> ParseResult<Expr> {
        let expr_left_span = self.current().span;
        let mut expr = self.equality()?;
        let expr_right_span = self.previous().span;

        while self.consume(&[TokenKind::And]) {
            let operator = self.previous();

            let op = match operator.token_kind {
                TokenKind::And => LogicalOp::And,
                _ => unreachable!(),
            };

            let operator_span = operator.span;
            let right_left_span = self.current().span;

            let result = self.equality();
            let right_right_span = self.current().span;

            let right = self.expect_expr(result, "right", operator_span)?;

            expr = Expr::Logical(LogicalExpr {
                left: Box::new(Typed::new(expr, self.create_span(expr_left_span, expr_right_span))),
                op: Typed::new(op, operator_span),
                right: Box::new(Typed::new(right, self.create_span(right_left_span, right_right_span))),
            })
        }
        Ok(expr)
    }

    fn equality(&mut self) -> ParseResult<Expr> {
        let expr_left_span = self.current().span;
        let mut expr = self.comparison()?;
        let expr_right_span = self.previous().span;

        while self.consume(&[TokenKind::BangEqual, TokenKind::EqualEqual]) {
            let operator = self.previous();

            let op = match operator.token_kind {
                TokenKind::BangEqual => BinaryOp::BangEqual,
                TokenKind::EqualEqual => BinaryOp::EqualEqual,
                _ => unreachable!(),
            };
            let operator_span = operator.span;

            let right_left_span = self.current().span;
            let result = self.comparison();
            let right_right_span = self.previous().span;

            let right = self.expect_expr(result, "right", operator_span)?;

            expr = Expr::Binary(BinaryExpr {
                left: Box::new(Typed::new(expr, self.create_span(expr_left_span, expr_right_span))),
                op: Typed::new(op, operator_span),
                right: Box::new(Typed::new(right, self.create_span(right_left_span, right_right_span))),
            })
        }
        Ok(expr)
    }

    fn comparison(&mut self) -> ParseResult<Expr> {
        let expr_left_span = self.current().span;
        let mut expr = self.term()?;
        let expr_right_span = self.previous().span;

        while self.consume(&[TokenKind::Less, TokenKind::LessEqual, TokenKind::Greater, TokenKind::GreaterEqual]) {
            let operator = self.previous();

            let op = match operator.token_kind {
                TokenKind::Less => BinaryOp::Less,
                TokenKind::LessEqual => BinaryOp::LessEqual,
                TokenKind::Greater => BinaryOp::Greater,
                TokenKind::GreaterEqual => BinaryOp::GreaterEqual,
                _ => unreachable!(),
            };

            let operator_span = operator.span;

            let right_left_span = self.current().span;
            let result = self.term();
            let right_right_span = self.previous().span;

            let right = self.expect_expr(result, "right", operator_span)?;

            expr = Expr::Binary(BinaryExpr {
                left: Box::new(Typed::new(expr, self.create_span(expr_left_span, expr_right_span))),
                op: Typed::new(op, operator_span),
                right: Box::new(Typed::new(right, self.create_span(right_left_span, right_right_span))),
            })
        }
        Ok(expr)
    }

    fn term(&mut self) -> ParseResult<Expr> {
        let expr_left_span = self.current().span;
        let mut expr = self.factor()?;
        let expr_right_span = self.previous().span;

        while self.consume(&[TokenKind::Plus, TokenKind::Minus]) {
            let operator = self.previous();

            let op = match operator.token_kind {
                TokenKind::Plus => BinaryOp::Plus,
                TokenKind::Minus => BinaryOp::Minus,
                _ => unreachable!(),
            };

            let operator_span = operator.span;

            let right_left_span = self.current().span;
            let result = self.factor();
            let right_right_span = self.previous().span;
            let right = self.expect_expr(result, "right", operator_span)?;

            expr = Expr::Binary(BinaryExpr {
                left: Box::new(Typed::new(expr, self.create_span(expr_left_span, expr_right_span))),
                op: Typed::new(op, operator_span),
                right: Box::new(Typed::new(right, self.create_span(right_left_span, right_right_span))),
            })
        }
        Ok(expr)
    }

    fn factor(&mut self) -> ParseResult<Expr> {
        let expr_left_span = self.current().span;
        let mut expr = self.unary()?;
        let expr_right_span = self.previous().span;

        while self.consume(&[TokenKind::Slash, TokenKind::Star]) {
            let operator = self.previous();

            let op = match operator.token_kind {
                TokenKind::Slash => BinaryOp::Slash,
                TokenKind::Star => BinaryOp::Star,
                _ => unreachable!(),
            };

            let operator_span = operator.span;

            let right_left_span = self.current().span;
            let result = self.unary();
            let right_right_span = self.previous().span;

            let right = self.expect_expr(result, "right", operator_span)?;

            expr = Expr::Binary(BinaryExpr {
                left: Box::new(Typed::new(expr, self.create_span(expr_left_span, expr_right_span))),
                op: Typed::new(op, operator_span),
                right: Box::new(Typed::new(right, self.create_span(right_left_span, right_right_span))),
            })
        }
        Ok(expr)
    }

    fn unary(&mut self) -> ParseResult<Expr> {
        if self.consume(&[TokenKind::Minus, TokenKind::Bang]) {
            let operator = self.previous();

            let op = match operator.token_kind {
                TokenKind::Bang => UnaryOp::Bang,
                TokenKind::Minus => UnaryOp::Minus,
                _ => unreachable!(),
            };

            let operator_span = operator.span;

            let expr_left_span = self.current().span;
            let result = self.unary();
            let expr_right_span = self.previous().span;

            let expr = self.expect_expr(result, "right", operator_span)?;

            Ok(Unary(UnaryExpr {
                op: Typed::new(op, operator_span),
                expr: Box::new(Typed::new(expr, self.create_span(expr_left_span, expr_right_span))),
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
            return Err(UnclosedDelimiter {
                src: self.source.to_string(),
                span: left_paren_span,
                delimiter: TokenKind::LeftParen,
            }
            .into());
        }

        let mut arguments = vec![];

        if !self.matches(&[TokenKind::RightParen]) {
            let expr_left_span = self.current().span;
            arguments.push(Typed::new(
                self.expression()?,
                self.create_span(expr_left_span, self.previous().span),
            ));
            while self.consume(&[TokenKind::Comma]) {
                let expr_left_span = self.current().span;
                arguments.push(Typed::new(
                    self.expression()?,
                    self.create_span(expr_left_span, self.previous().span),
                ));
            }
        }

        self.close_delimiter(self.current().token_kind.clone())?;

        Ok(Call(CallExpr {
            callee: Box::new(Typed::new(callee, left_paren_span)),
            arguments,
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
            TokenKind::False => {
                self.advance_position();
                Ok(Literal(LiteralExpr::Bool(false)))
            }
            TokenKind::True => {
                self.advance_position();
                Ok(Literal(LiteralExpr::Bool(true)))
            }
            TokenKind::Nil => {
                self.advance_position();
                Ok(Literal(LiteralExpr::Nil))
            }
            TokenKind::LeftParen => {
                let opening_paren_span = self.current().span;
                self.open_delimiter(self.current().token_kind.clone())?;

                let expr = if self.next_is(TokenKind::RightParen) {
                    Err(ExpectedExpression {
                        src: self.source.to_string(),
                        span: self.create_span(opening_paren_span, self.peek().span),
                    }
                    .into())
                } else {
                    self.expression()
                }?;

                self.close_delimiter(self.current().token_kind.clone())?;

                Ok(Grouping(Box::new(Typed::new(
                    expr,
                    self.create_span(opening_paren_span, self.current().span),
                ))))
            }
            TokenKind::Number(value) => {
                let span = self.current().span;
                self.advance_position();

                if self.current_is(TokenKind::Ident(String::new())) {
                    return Err(InvalidVariableName {
                        src: self.source.to_string(),
                        span,
                        message: "A variable cannot start with a number".to_string(),
                    }
                    .into());
                }
                Ok(Literal(LiteralExpr::Number(value)))
            }
            TokenKind::String(ref value) => {
                let string = value.clone();
                self.advance_position();
                Ok(Literal(LiteralExpr::String(string)))
            }
            TokenKind::Ident(ref name) => {
                let string = name.clone();
                self.advance_position();
                Ok(Variable(Typed::new(string, self.previous().span)))
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
