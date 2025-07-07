use crate::ast::Stmt::{ExprStmtNode, Return, While};
use crate::ast::{
    AssignExpr, AstNode, AstProgram, BinaryExpr, BinaryOp, BlockExpr, CallExpr, Expr, ExprStmt, FieldAccessExpr, FieldAssignExpr, ForStmt,
    FunDeclStmt, Ident, IfExpr, LambdaExpr, LiteralExpr, LogicalExpr, LogicalOp, MethodCallExpr, ReturnStmt, Stmt, StructDeclStmt,
    StructInitExpr, TypedIdent, UnaryExpr, UnaryOp, UnresolvedType, VarDeclStmt, WhileStmt,
};
use crate::error::ParseError;
use crate::error::ParseError::{
    ExpectedExpression, ExpectedIdentifier, InvalidIdentifier, MissingBlock, MissingOperand, MissingSemicolon, RedundantParenthesis,
    RedundantSemicolon, UnclosedDelimiter, UnexpectedClosingDelimiter, UnexpectedEOF, UnexpectedToken, UnmatchedDelimiter,
};
use crate::lexer::Delimiter::{LeftParen, RightParen};
use crate::lexer::{Delimiter, Keyword, Literal, Operator, Punctuation};
use crate::{Token, TokenKind};
use miette::{Report, SourceOffset, SourceSpan};

type ParseResult<T> = Result<T, ParseError>;

pub struct ParserResult<'a> {
    pub errors: &'a Vec<Report>,
    pub ast: AstProgram,
}

pub struct Parser {
    tokens: Vec<Token>,
    position: usize,
    errors: Vec<Report>,
    source: String,
    delimiter_stack: Vec<Token>,
}

impl Parser {
    fn current(&self) -> &Token {
        &self.tokens[self.position]
    }

    fn peek(&self) -> &Token {
        &self.tokens[self.position + 1]
    }

    fn previous(&self) -> &Token {
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
            (TokenKind::Literal(Literal::Int(_)), TokenKind::Literal(Literal::Int(_))) => true,
            (TokenKind::Literal(Literal::Float(_)), TokenKind::Literal(Literal::Float(_))) => true,
            (TokenKind::Literal(Literal::String(_)), TokenKind::Literal(Literal::String(_))) => true,
            (TokenKind::Ident(_), TokenKind::Ident(_)) => true,
            (a, b) => a == b,
        }
    }

    fn current_is(&self, kind: TokenKind) -> bool {
        match (&self.current().token_kind, &kind) {
            (TokenKind::Literal(Literal::Int(_)), TokenKind::Literal(Literal::Int(_))) => true,
            (TokenKind::Literal(Literal::Float(_)), TokenKind::Literal(Literal::Float(_))) => true,
            (TokenKind::Literal(Literal::String(_)), TokenKind::Literal(Literal::String(_))) => true,
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

impl Parser {
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

impl Parser {
    fn report(&mut self, error: ParseError) {
        self.errors.push(error.into());
    }

    /// if `current` is not a semicolon, it skips to the next statement
    fn expect_semicolon(&mut self) {
        if !self.consume(&[TokenKind::Punct(Punctuation::Semicolon)]) {
            let previous_span = self.previous().span;
            let next_span = self.next_span(previous_span);
            let error = MissingSemicolon {
                src: self.source.to_string(),
                span: next_span,
            };
            self.report(error);
            self.skip_to_next_stmt();
        }
    }

    fn expect_expr(&self, result: ParseResult<Expr>, side: &str, span: SourceSpan) -> ParseResult<Expr> {
        result.map_err(|_| MissingOperand {
            src: self.source.to_string(),
            span,
            side: side.to_string(),
        })
    }
}

impl Parser {
    /// eats until `current` is one of the given tokens
    fn eat_to_tokens(&mut self, tokens: &[TokenKind]) {
        while !self.at_eof() && !self.matches(tokens) {
            self.advance_position();
        }
    }

    /// skips past the next semicolon, stops before block ending
    fn skip_to_next_stmt(&mut self) {
        while !self.matches(&[TokenKind::Punct(Punctuation::Semicolon), TokenKind::Delim(Delimiter::RightBrace)]) && !self.at_eof() {
            self.advance_position();
        }
        if self.matches(&[TokenKind::Punct(Punctuation::Semicolon)]) {
            self.advance_position();
        }
    }

    /// skips until next left paren
    fn skip_to_left_paren(&mut self) {
        self.eat_to_tokens(&[TokenKind::Delim(Delimiter::LeftParen)])
    }
}

impl Parser {
    /// current is the opening delimiter, end is the next token
    fn open_delimiter(&mut self, open_delim: TokenKind) -> ParseResult<()> {
        let current_token = self.current().clone();

        // this should never happen because it should always check if the current is the open_delim before
        if current_token.token_kind != open_delim {
            unreachable!()
        }

        match open_delim {
            TokenKind::Delim(Delimiter::LeftParen) | TokenKind::Delim(Delimiter::LeftBrace) | TokenKind::Delim(Delimiter::LeftBracket) => {
                self.delimiter_stack.push(Token {
                    token_kind: open_delim,
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
                })
            }
        }
    }

    /// current is closing delimiter, end is the next token
    fn close_delimiter(&mut self, close_delim: TokenKind) -> ParseResult<()> {
        // this should never happen because it should always check if the current is the open_delim before
        if self.current().token_kind != close_delim {
            unreachable!()
        }

        if self.delimiter_stack.is_empty() {
            self.advance_position();
            return Err(UnexpectedClosingDelimiter {
                src: self.source.to_string(),
                span: self.previous().span,
                delimiter: close_delim,
            });
        }

        let last_delimiter = self.delimiter_stack.pop().unwrap();
        let expected_closing = match last_delimiter.token_kind {
            TokenKind::Delim(Delimiter::LeftParen) => TokenKind::Delim(Delimiter::RightParen),
            TokenKind::Delim(Delimiter::LeftBrace) => TokenKind::Delim(Delimiter::RightBrace),
            TokenKind::Delim(Delimiter::LeftBracket) => TokenKind::Delim(Delimiter::RightBracket),
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

impl Parser {
    pub fn new(tokens: Vec<Token>, source: String) -> Self {
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
        if self.at_eof() {
            return ParserResult {
                ast: AstProgram {
                    statements,
                    span: self.create_span(left_program_span, self.current().span),
                },
                errors: &self.errors,
            };
        }

        while !self.at_eof() {
            let left_statement_span = self.current().span;
            let statement = self.declaration();
            let right_statement_span = self.previous().span;

            match statement {
                Ok(stmt) => statements.push(AstNode::new(stmt, self.create_span(left_statement_span, right_statement_span))),
                Err(err) => {
                    self.report(err);
                    self.skip_to_next_stmt();
                }
            }
        }

        ParserResult {
            ast: AstProgram {
                statements,
                span: self.create_span(left_program_span, self.current().span),
            },
            errors: &self.errors,
        }
    }

    fn declaration(&mut self) -> ParseResult<Stmt> {
        if self.matches(&[TokenKind::Keyword(Keyword::Let)]) {
            return self.var_declaration();
        } else if self.matches(&[TokenKind::Keyword(Keyword::Fn)]) {
            return self.fun_declaration();
        } else if self.matches(&[TokenKind::Keyword(Keyword::Struct)]) {
            return self.struct_declaration();
        }
        self.statement()
    }

    fn var_declaration(&mut self) -> ParseResult<Stmt> {
        self.advance_position();

        let variable_name = self.parse_identifier()?;

        let type_annotation = if self.matches(&[TokenKind::Punct(Punctuation::Colon)]) {
            Some(self.parse_type_annotation()?)
        } else {
            None
        };

        let initializer = self.parse_var_initializer()?;
        self.expect_semicolon();

        Ok(Stmt::VarDecl(VarDeclStmt {
            ident: variable_name,
            initializer,
            type_annotation,
        }))
    }

    /// start is the identifier, end is the next token
    fn parse_identifier(&mut self) -> ParseResult<Ident> {
        let ident_token = self.current().clone();

        let ident = match ident_token.token_kind {
            TokenKind::Ident(name) => {
                self.advance_position();
                AstNode::new(name.clone(), ident_token.span)
            }
            TokenKind::Literal(Literal::Float(_)) | TokenKind::Literal(Literal::Int(_)) => {
                if self.consume(&[TokenKind::Ident(String::new())]) {
                    self.report(InvalidIdentifier {
                        src: self.source.to_string(),
                        span: self.create_span(ident_token.span, self.current().span),
                        message: "identifiers cannot start with a number".to_string(),
                        found: format!("{}{}", self.previous().token_kind, self.current().token_kind),
                    })
                } else {
                    self.report(ExpectedIdentifier {
                        src: self.source.to_string(),
                        span: ident_token.span,
                    });
                }
                AstNode::new("dummy".to_string(), self.current().span)
            }
            _ => {
                return Err(ExpectedIdentifier {
                    src: self.source.to_string(),
                    span: ident_token.span,
                });
            }
        };
        Ok(ident)
    }

    fn parse_var_initializer(&mut self) -> ParseResult<Option<AstNode<Expr>>> {
        let initializer = if self.consume(&[TokenKind::Operator(Operator::Equal)]) {
            if self.consume(&[TokenKind::Punct(Punctuation::Semicolon)]) {
                return Err(ExpectedExpression {
                    src: self.source.to_string(),
                    span: self.previous().span,
                }
                .into());
            }
            let left_expr_span = self.current().span;
            Some(AstNode::new(
                self.expression()?,
                self.create_span(left_expr_span, self.previous().span),
            ))
        } else if self.matches(&[TokenKind::Punct(Punctuation::Semicolon)]) {
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
        self.advance_position();

        let function_name = self.parse_identifier()?;
        let generics = self.parse_function_generics()?;

        let parameters = self.parse_function_parameters()?;

        let return_type = self.parse_return_type()?;

        let body_left_span = self.current().span;
        let body = match self.block()? {
            Expr::Block(block) => block,
            _ => {
                return Err(MissingBlock {
                    src: self.source.to_string(),
                    span: self.create_span(body_left_span, self.previous().span),
                }
                .into());
            }
        };
        let body_right_span = self.previous().span;

        Ok(Stmt::FunDecl(FunDeclStmt {
            ident: function_name,
            params: parameters,
            generics,
            body: AstNode::new(body, self.create_span(body_left_span, body_right_span)),
            return_type,
        }))
    }

    /// current is struct name, ends at '{'
    fn struct_declaration(&mut self) -> ParseResult<Stmt> {
        self.advance_position();

        let struct_name = self.parse_identifier()?;
        self.open_delimiter(TokenKind::Delim(Delimiter::LeftBrace))?;
        let parameters = self.parse_typed_idents(TokenKind::Delim(Delimiter::RightBrace))?;

        Ok(Stmt::StructDecl(StructDeclStmt {
            ident: struct_name,
            fields: parameters,
        }))
    }

    fn parse_return_type(&mut self) -> ParseResult<AstNode<UnresolvedType>> {
        if !self.consume(&[TokenKind::Punct(Punctuation::Arrow)]) {
            return Ok(AstNode::new(
                UnresolvedType::Named(Ident::new("Nil".to_string(), SourceSpan::from(0))),
                SourceSpan::from(0),
            ));
        }

        let return_left_span = self.current().span;
        let ty = self.parse_type()?;
        let return_right_span = self.previous().span;

        Ok(AstNode::new(ty, self.create_span(return_left_span, return_right_span)))
    }

    /// current is potential `<` ends after `>`
    fn parse_function_generics(&mut self) -> ParseResult<Vec<Ident>> {
        if !self.consume(&[TokenKind::Operator(Operator::Less)]) {
            return Ok(vec![]);
        }

        let mut generics = vec![];

        loop {
            match &self.current().token_kind {
                TokenKind::Ident(name) => {
                    let span = self.current().span;
                    generics.push(AstNode::new(name.clone(), span));
                    self.advance_position();

                    if self.consume(&[TokenKind::Operator(Operator::Greater)]) {
                        break;
                    }
                    if !self.consume(&[TokenKind::Punct(Punctuation::Comma)]) {
                        return Err(UnexpectedToken {
                            src: self.source.to_string(),
                            span: self.current().span,
                            found: self.current().token_kind.clone(),
                            expected: "',' or '>'".to_string(),
                        }
                        .into());
                    }
                }
                TokenKind::Operator(Operator::Greater) => {
                    if generics.is_empty() {
                        return Err(ExpectedIdentifier {
                            src: self.source.to_string(),
                            span: self.current().span,
                        }
                        .into());
                    }
                    self.advance_position();
                    break;
                }
                _ => {
                    return Err(ExpectedIdentifier {
                        src: self.source.to_string(),
                        span: self.current().span,
                    }
                    .into());
                }
            }
        }
        Ok(generics)
    }

    /// current is `:` end is after type
    fn parse_type_annotation(&mut self) -> ParseResult<AstNode<UnresolvedType>> {
        if !self.consume(&[TokenKind::Punct(Punctuation::Colon)]) {
            return Err(UnexpectedToken {
                src: self.source.to_string(),
                span: self.current().span,
                expected: "colon".to_string(),
                found: self.current().token_kind.clone(),
            }
            .into());
        }

        let annotation_left_span = self.current().span;
        let ty = self.parse_type()?;
        let annotation_right_span = self.previous().span;

        Ok(AstNode::new(ty, self.create_span(annotation_left_span, annotation_right_span)))
    }

    /// current is the type annotation
    fn parse_type(&mut self) -> ParseResult<UnresolvedType> {
        if self.matches(&[TokenKind::Delim(Delimiter::LeftParen)]) {
            self.parse_function_type()
        } else {
            self.parse_named_or_generic()
        }
    }

    fn parse_function_type(&mut self) -> ParseResult<UnresolvedType> {
        self.open_delimiter(TokenKind::Delim(Delimiter::LeftParen))?;
        let mut param_types = vec![];

        if !self.matches(&[TokenKind::Delim(Delimiter::RightParen)]) {
            let left_param_span = self.current().span;
            param_types.push(AstNode::new(
                self.parse_type()?,
                self.create_span(left_param_span, self.previous().span),
            ));
            while self.consume(&[TokenKind::Punct(Punctuation::Comma)]) {
                let left_param_span = self.current().span;
                param_types.push(AstNode::new(
                    self.parse_type()?,
                    self.create_span(left_param_span, self.previous().span),
                ));
            }
        }

        self.close_delimiter(TokenKind::Delim(Delimiter::RightParen))?;

        if !self.consume(&[TokenKind::Punct(Punctuation::Arrow)]) {
            return Err(UnexpectedToken {
                src: self.source.to_string(),
                span: self.current().span,
                expected: "'->'".to_string(),
                found: self.current().token_kind.clone(),
            }
            .into());
        }

        let left_return_span = self.current().span;
        let return_type = Box::new(AstNode::new(
            self.parse_type()?,
            self.create_span(left_return_span, self.previous().span),
        ));
        Ok(UnresolvedType::Function {
            params: param_types,
            return_type,
        })
    }

    fn parse_named_or_generic(&mut self) -> ParseResult<UnresolvedType> {
        let left_base_span = self.current().span;
        let base = self.parse_identifier()?;
        let right_base_span = self.previous().span;

        let base = UnresolvedType::Named(base);

        if self.consume(&[TokenKind::Operator(Operator::Less)]) {
            let mut args = vec![];

            let left_arg_span = self.current().span;
            args.push(AstNode::new(
                self.parse_type()?,
                self.create_span(left_arg_span, self.previous().span),
            ));
            while self.consume(&[TokenKind::Punct(Punctuation::Comma)]) {
                let left_arg_span = self.current().span;
                args.push(AstNode::new(
                    self.parse_type()?,
                    self.create_span(left_arg_span, self.previous().span),
                ));
            }
            if !self.consume(&[TokenKind::Operator(Operator::Greater)]) {
                return Err(UnexpectedToken {
                    src: self.source.to_string(),
                    span: self.current().span,
                    expected: "'>'".to_string(),
                    found: self.current().token_kind.clone(),
                }
                .into());
            }
            Ok(UnresolvedType::Generic {
                base: Box::new(AstNode::new(base, self.create_span(left_base_span, right_base_span))),
                args,
            })
        } else {
            Ok(base)
        }
    }

    fn parse_parameter(&mut self) -> ParseResult<TypedIdent> {
        let curr_token = self.current().clone();

        match &curr_token.token_kind {
            TokenKind::Ident(name) => {
                let name_span = curr_token.span;
                self.advance_position();

                let type_annotation = self.parse_type_annotation()?;

                Ok(TypedIdent {
                    name: AstNode::new(name.clone(), name_span),
                    type_annotation,
                })
            }
            _ => Err(ExpectedIdentifier {
                src: self.source.to_string(),
                span: curr_token.span,
            }
            .into()),
        }
    }

    /// start at first `field` ends after the `closing_delimiter`
    fn parse_typed_idents(&mut self, closing_delimiter: TokenKind) -> ParseResult<Vec<TypedIdent>> {
        let mut fields = vec![];

        if self.matches(&[closing_delimiter.clone()]) {
            self.close_delimiter(closing_delimiter)?;
            return Ok(fields);
        }

        loop {
            let field = self.parse_parameter()?;
            fields.push(field);

            match self.current().token_kind.clone() {
                TokenKind::Punct(Punctuation::Comma) => {
                    self.advance_position();
                    if self.current_is(closing_delimiter.clone()) {
                        self.close_delimiter(closing_delimiter)?;
                        break;
                    }
                }
                kind if kind == closing_delimiter => {
                    self.close_delimiter(kind)?;
                    break;
                }
                TokenKind::EOF => {
                    return Err(UnexpectedEOF {
                        src: self.source.to_string(),
                        expected: format!("{closing_delimiter:?}"),
                    }
                    .into());
                }
                _ => {
                    return Err(UnexpectedToken {
                        src: self.source.to_string(),
                        span: self.current().span,
                        found: self.current().token_kind.clone(),
                        expected: format!("',', or {closing_delimiter:?}"),
                    }
                    .into());
                }
            }
        }
        Ok(fields)
    }
    /// current is '(' ends after ')'
    fn parse_function_parameters(&mut self) -> ParseResult<Vec<TypedIdent>> {
        self.open_delimiter(TokenKind::Delim(Delimiter::LeftParen))?;

        Ok(self.parse_typed_idents(TokenKind::Delim(Delimiter::RightParen))?)
    }

    /// current is the start of the statement
    fn statement(&mut self) -> ParseResult<Stmt> {
        if self.matches(&[TokenKind::Keyword(Keyword::While)]) {
            return self.while_stmt();
        } else if self.matches(&[TokenKind::Keyword(Keyword::For)]) {
            return self.for_stmt();
        } else if self.matches(&[TokenKind::Keyword(Keyword::Return)]) {
            return self.return_stmt();
        }
        self.expression_stmt()
    }

    /// current is start of the statement, end is next statement
    fn expression_stmt(&mut self) -> ParseResult<Stmt> {
        let expr_left_span = self.current().span;
        let value = self.expression()?;
        let expr_right_span = self.previous().span;

        match value {
            Expr::Block(_) => {}
            Expr::If(_) => {}
            _ => self.expect_semicolon(),
        }

        Ok(ExprStmtNode(ExprStmt {
            expr: AstNode::new(value, self.create_span(expr_left_span, expr_right_span)),
        }))
    }
    /// start is `if`, end is next statement
    fn if_expr(&mut self) -> ParseResult<Expr> {
        self.advance_position();

        let condition_left_span = self.current().span;
        let condition = self.parse_condition()?;
        let condition_right_span = self.previous().span;

        let then_branch_left_span = self.current().span;
        let then_branch = match self.block()? {
            Expr::Block(block) => block,
            _ => {
                return Err(MissingBlock {
                    src: self.source.to_string(),
                    span: self.create_span(then_branch_left_span, self.previous().span),
                }
                .into());
            }
        };
        let then_branch_right_span = self.previous().span;

        let else_branch_left_span = self.current().span;
        let mut else_branch = None;
        if self.consume(&[TokenKind::Keyword(Keyword::Else)]) {
            else_branch = if self.matches(&[TokenKind::Keyword(Keyword::If)]) {
                let if_expr = self.if_expr()?;
                Some(AstNode::new(
                    BlockExpr {
                        statements: vec![],
                        expr: Some(Box::new(AstNode::new(
                            if_expr,
                            self.create_span(else_branch_left_span, self.previous().span),
                        ))),
                    },
                    self.create_span(else_branch_left_span, self.previous().span),
                ))
            } else {
                match self.block()? {
                    Expr::Block(block) => Some(AstNode::new(block, self.create_span(else_branch_left_span, self.previous().span))),
                    _ => {
                        return Err(MissingBlock {
                            src: self.source.to_string(),
                            span: self.create_span(then_branch_left_span, self.previous().span),
                        }
                        .into());
                    }
                }
            };
        }

        Ok(Expr::If(IfExpr {
            condition: Box::new(AstNode::new(condition, self.create_span(condition_left_span, condition_right_span))),
            then_branch: AstNode::new(then_branch, self.create_span(then_branch_left_span, then_branch_right_span)),
            else_branch,
        }))
    }

    /// current is '{' and ends after '}'
    fn block(&mut self) -> ParseResult<Expr> {
        self.open_delimiter(TokenKind::Delim(Delimiter::LeftBrace))?;

        let mut statements = vec![];
        let mut expression = None;

        while !self.matches(&[TokenKind::Delim(Delimiter::RightBrace)]) && !self.at_eof() {
            let saved_pos = self.position;

            if let Ok(expr) = self.expression() {
                if self.current_is(TokenKind::Delim(Delimiter::RightBrace)) {
                    let span = self.create_span(self.previous().span, self.current().span);
                    expression = Some(Box::new(AstNode::new(expr, span)));
                    break;
                }
            }

            self.position = saved_pos;
            let left_stmt_span = self.current().span;
            match self.declaration() {
                Ok(stmt) => statements.push(AstNode::new(stmt, self.create_span(left_stmt_span, self.previous().span))),
                Err(err) => {
                    self.report(err);
                    self.skip_to_next_stmt();
                }
            }
        }

        self.close_delimiter(TokenKind::Delim(Delimiter::RightBrace))?;

        Ok(Expr::Block(BlockExpr {
            statements,
            expr: expression,
        }))
    }

    /// starts at first condition token, ends after the condition
    fn parse_condition(&mut self) -> ParseResult<Expr> {
        let expr_left_span = self.current().span;
        let expr = self.expression()?;

        if let Expr::Grouping(inner) = expr {
            self.report(
                RedundantParenthesis {
                    src: self.source.to_string(),
                    first: expr_left_span,
                    second: self.previous().span,
                }
                .into(),
            );
            Ok(inner.node)
        } else {
            Ok(expr)
        }
    }

    /// start is `while`, end is next statement
    fn while_stmt(&mut self) -> ParseResult<Stmt> {
        self.advance_position();

        let condition_span = self.current().span;
        let condition = AstNode::new(self.parse_condition()?, condition_span);

        let block_left_span = self.current().span;
        let block = match self.block()? {
            Expr::Block(block) => block,
            _ => {
                return Err(MissingBlock {
                    src: self.source.to_string(),
                    span: self.create_span(block_left_span, self.previous().span),
                }
                .into());
            }
        };

        let block_right_span = self.previous().span;

        Ok(While(WhileStmt {
            condition,
            body: AstNode::new(block, self.create_span(block_left_span, block_right_span)),
        }))
    }

    /// current is for, end is after block
    fn for_stmt(&mut self) -> ParseResult<Stmt> {
        self.advance_position();
        self.open_delimiter(TokenKind::Delim(LeftParen))?;

        let left_initializer_span = self.current().span;
        let initializer = if self.matches(&[TokenKind::Keyword(Keyword::Let)]) {
            Some(Box::new(AstNode::new(
                self.var_declaration()?,
                self.create_span(left_initializer_span, self.previous().span),
            )))
        } else if !self.consume(&[TokenKind::Punct(Punctuation::Semicolon)]) {
            Some(Box::new(AstNode::new(
                self.expression_stmt()?,
                self.create_span(left_initializer_span, self.previous().span),
            )))
        } else {
            None
        };

        let condition_span = self.current().span;
        let condition = if !self.matches(&[TokenKind::Punct(Punctuation::Semicolon)]) {
            self.expression()?
        } else {
            Expr::Literal(LiteralExpr::Bool(true))
        };
        let condition = AstNode::new(condition, condition_span);

        if !self.consume(&[TokenKind::Punct(Punctuation::Semicolon)]) {
            let error = MissingSemicolon {
                src: self.source.to_string(),
                span: self.previous().span,
            };
            self.report(error.into());
        }

        let inc_left_span = self.current().span;
        let increment = if !self.matches(&[TokenKind::Delim(Delimiter::LeftBrace)]) {
            Some(AstNode::new(
                self.expression()?,
                self.create_span(inc_left_span, self.previous().span),
            ))
        } else {
            None
        };

        self.close_delimiter(TokenKind::Delim(RightParen))?;
        let body_left_span = self.current().span;
        let body = match self.block()? {
            Expr::Block(block) => block,
            _ => {
                return Err(MissingBlock {
                    src: self.source.to_string(),
                    span: self.create_span(body_left_span, self.previous().span),
                }
                .into());
            }
        };
        Ok(Stmt::For(ForStmt {
            condition,
            initializer,
            increment,
            body: AstNode::new(body, self.create_span(body_left_span, self.previous().span)),
        }))
    }

    /// current is `return` end is next statement
    fn return_stmt(&mut self) -> ParseResult<Stmt> {
        self.advance_position();

        let value = if !self.matches(&[TokenKind::Punct(Punctuation::Semicolon)]) {
            let left_expr_span = self.current().span;
            if self.at_eof() {
                return Err(ExpectedExpression {
                    src: self.source.to_string(),
                    span: self.current().span,
                }
                .into());
            }
            Some(AstNode::new(
                self.expression()?,
                self.create_span(left_expr_span, self.previous().span),
            ))
        } else {
            None
        };

        self.expect_semicolon();
        Ok(Return(ReturnStmt { expr: value }))
    }

    /// starts at first token, ends after the last token of the expression
    fn expression(&mut self) -> ParseResult<Expr> {
        if self.matches(&[TokenKind::Keyword(Keyword::Fn)]) {
            return self.lambda_expr();
        } else if self.matches(&[TokenKind::Keyword(Keyword::If)]) {
            return self.if_expr();
        } else if self.matches(&[TokenKind::Delim(Delimiter::LeftBrace)]) {
            return self.block();
        }
        self.assignment()
    }

    fn parse_binary_operand(&mut self, parse_fn: fn(&mut Self) -> ParseResult<Expr>) -> ParseResult<Expr> {
        if self.matches(&[TokenKind::Delim(Delimiter::LeftBrace)]) {
            self.block()
        } else {
            parse_fn(self)
        }
    }

    fn lambda_expr(&mut self) -> ParseResult<Expr> {
        self.advance_position();

        let parameters = self.parse_function_parameters()?;

        let return_type = self.parse_return_type()?;

        let body_left_span = self.current().span;
        let body = match self.block()? {
            Expr::Block(block) => block,
            _ => {
                return Err(MissingBlock {
                    src: self.source.to_string(),
                    span: self.create_span(body_left_span, self.previous().span),
                }
                .into());
            }
        };
        let body_right_span = self.previous().span;

        Ok(Expr::Lambda(LambdaExpr {
            parameters,
            body: Box::new(AstNode::new(body, self.create_span(body_left_span, body_right_span))),
            return_type,
        }))
    }

    fn assignment(&mut self) -> ParseResult<Expr> {
        let left_assignment_span = self.current().span;
        let expr = self.logic_or()?;

        if self.consume(&[TokenKind::Operator(Operator::Equal)]) {
            let equal_span = self.previous().span;

            let left_result_span = self.current().span;
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
                Expr::Variable(name) => Ok(Expr::Assign(AssignExpr {
                    target: name,
                    value: Box::new(AstNode::new(value, self.create_span(left_assignment_span, self.previous().span))),
                })),
                Expr::FieldAccess(field_access) => Ok(Expr::FieldAssign(FieldAssignExpr {
                    receiver: field_access.receiver,
                    field: field_access.field,
                    value: Box::new(AstNode::new(value, self.create_span(left_result_span, self.previous().span))),
                })),
                _ => Err(ExpectedIdentifier {
                    src: self.source.to_string(),
                    span: equal_span,
                }
                .into()),
            };
        }
        Ok(expr)
    }

    fn logic_or(&mut self) -> ParseResult<Expr> {
        let expr_left_span = self.current().span;
        let mut expr = self.parse_binary_operand(Self::logic_and)?;
        let expr_right_span = self.previous().span;

        while self.consume(&[TokenKind::Keyword(Keyword::Or)]) {
            let operator = self.previous();

            let op = match operator.token_kind {
                TokenKind::Keyword(Keyword::Or) => LogicalOp::Or,
                _ => unreachable!(),
            };

            let operator_span = operator.span;
            let right_left_span = self.current().span;

            let result = self.parse_binary_operand(Self::logic_and);
            let right_right_span = self.previous().span;

            let right = self.expect_expr(result, "right", operator_span)?;

            expr = Expr::Logical(LogicalExpr {
                left: Box::new(AstNode::new(expr, self.create_span(expr_left_span, expr_right_span))),
                op: AstNode::new(op, operator_span),
                right: Box::new(AstNode::new(right, self.create_span(right_left_span, right_right_span))),
            })
        }
        Ok(expr)
    }

    fn logic_and(&mut self) -> ParseResult<Expr> {
        let expr_left_span = self.current().span;
        let mut expr = self.parse_binary_operand(Self::equality)?;
        let expr_right_span = self.previous().span;

        while self.consume(&[TokenKind::Keyword(Keyword::And)]) {
            let operator = self.previous();

            let op = match operator.token_kind {
                TokenKind::Keyword(Keyword::And) => LogicalOp::And,
                _ => unreachable!(),
            };

            let operator_span = operator.span;
            let right_left_span = self.current().span;

            let result = self.parse_binary_operand(Self::equality);
            let right_right_span = self.previous().span;

            let right = self.expect_expr(result, "right", operator_span)?;

            expr = Expr::Logical(LogicalExpr {
                left: Box::new(AstNode::new(expr, self.create_span(expr_left_span, expr_right_span))),
                op: AstNode::new(op, operator_span),
                right: Box::new(AstNode::new(right, self.create_span(right_left_span, right_right_span))),
            })
        }
        Ok(expr)
    }

    fn equality(&mut self) -> ParseResult<Expr> {
        let expr_left_span = self.current().span;
        let mut expr = self.parse_binary_operand(Self::comparison)?;
        let expr_right_span = self.previous().span;

        while self.consume(&[TokenKind::Operator(Operator::EqualEqual), TokenKind::Operator(Operator::BangEqual)]) {
            let operator = self.previous();

            let op = match operator.token_kind {
                TokenKind::Operator(Operator::BangEqual) => BinaryOp::BangEqual,
                TokenKind::Operator(Operator::EqualEqual) => BinaryOp::EqualEqual,
                _ => unreachable!(),
            };
            let operator_span = operator.span;

            let right_left_span = self.current().span;
            let result = self.parse_binary_operand(Self::comparison);
            let right_right_span = self.previous().span;

            let right = self.expect_expr(result, "right", operator_span)?;

            expr = Expr::Binary(BinaryExpr {
                left: Box::new(AstNode::new(expr, self.create_span(expr_left_span, expr_right_span))),
                op: AstNode::new(op, operator_span),
                right: Box::new(AstNode::new(right, self.create_span(right_left_span, right_right_span))),
            })
        }
        Ok(expr)
    }

    fn comparison(&mut self) -> ParseResult<Expr> {
        let expr_left_span = self.current().span;
        let mut expr = self.parse_binary_operand(Self::term)?;
        let expr_right_span = self.previous().span;

        while self.consume(&[
            TokenKind::Operator(Operator::Less),
            TokenKind::Operator(Operator::LessEqual),
            TokenKind::Operator(Operator::Greater),
            TokenKind::Operator(Operator::GreaterEqual),
        ]) {
            let operator = self.previous();

            let op = match operator.token_kind {
                TokenKind::Operator(Operator::Less) => BinaryOp::Less,
                TokenKind::Operator(Operator::LessEqual) => BinaryOp::LessEqual,
                TokenKind::Operator(Operator::Greater) => BinaryOp::Greater,
                TokenKind::Operator(Operator::GreaterEqual) => BinaryOp::GreaterEqual,
                _ => unreachable!(),
            };

            let operator_span = operator.span;

            let right_left_span = self.current().span;
            let result = self.parse_binary_operand(Self::term);
            let right_right_span = self.previous().span;

            let right = self.expect_expr(result, "right", operator_span)?;

            expr = Expr::Binary(BinaryExpr {
                left: Box::new(AstNode::new(expr, self.create_span(expr_left_span, expr_right_span))),
                op: AstNode::new(op, operator_span),
                right: Box::new(AstNode::new(right, self.create_span(right_left_span, right_right_span))),
            })
        }
        Ok(expr)
    }

    fn term(&mut self) -> ParseResult<Expr> {
        let expr_left_span = self.current().span;
        let mut expr = self.parse_binary_operand(Self::factor)?;
        let expr_right_span = self.previous().span;

        while self.consume(&[TokenKind::Operator(Operator::Plus), TokenKind::Operator(Operator::Minus)]) {
            let operator = self.previous();

            let op = match operator.token_kind {
                TokenKind::Operator(Operator::Plus) => BinaryOp::Plus,
                TokenKind::Operator(Operator::Minus) => BinaryOp::Minus,
                _ => unreachable!(),
            };

            let operator_span = operator.span;

            let right_left_span = self.current().span;
            let result = self.parse_binary_operand(Self::factor);
            let right_right_span = self.previous().span;
            let right = self.expect_expr(result, "right", operator_span)?;

            expr = Expr::Binary(BinaryExpr {
                left: Box::new(AstNode::new(expr, self.create_span(expr_left_span, expr_right_span))),
                op: AstNode::new(op, operator_span),
                right: Box::new(AstNode::new(right, self.create_span(right_left_span, right_right_span))),
            })
        }
        Ok(expr)
    }

    fn factor(&mut self) -> ParseResult<Expr> {
        let expr_left_span = self.current().span;
        let mut expr = self.parse_binary_operand(Self::unary)?;
        let expr_right_span = self.previous().span;

        while self.consume(&[TokenKind::Operator(Operator::Slash), TokenKind::Operator(Operator::Star)]) {
            let operator = self.previous();

            let op = match operator.token_kind {
                TokenKind::Operator(Operator::Slash) => BinaryOp::Slash,
                TokenKind::Operator(Operator::Star) => BinaryOp::Star,
                _ => unreachable!(),
            };

            let operator_span = operator.span;

            let right_left_span = self.current().span;
            let result = self.parse_binary_operand(Self::unary);
            let right_right_span = self.previous().span;

            let right = self.expect_expr(result, "right", operator_span)?;

            expr = Expr::Binary(BinaryExpr {
                left: Box::new(AstNode::new(expr, self.create_span(expr_left_span, expr_right_span))),
                op: AstNode::new(op, operator_span),
                right: Box::new(AstNode::new(right, self.create_span(right_left_span, right_right_span))),
            })
        }
        Ok(expr)
    }

    fn unary(&mut self) -> ParseResult<Expr> {
        if self.consume(&[TokenKind::Operator(Operator::Minus), TokenKind::Operator(Operator::Bang)]) {
            let operator = self.previous();

            let op = match operator.token_kind {
                TokenKind::Operator(Operator::Minus) => UnaryOp::Minus,
                TokenKind::Operator(Operator::Bang) => UnaryOp::Bang,
                _ => unreachable!(),
            };

            let operator_span = operator.span;

            let expr_left_span = self.current().span;
            let result = self.unary();
            let expr_right_span = self.previous().span;

            let expr = self.expect_expr(result, "right", operator_span)?;

            Ok(Expr::Unary(UnaryExpr {
                op: AstNode::new(op, operator_span),
                expr: Box::new(AstNode::new(expr, self.create_span(expr_left_span, expr_right_span))),
            }))
        } else {
            self.call()
        }
    }

    fn call(&mut self) -> ParseResult<Expr> {
        let mut expr = self.primary()?;

        loop {
            if self.matches(&[TokenKind::Delim(Delimiter::LeftParen)]) {
                expr = self.finish_call(expr)?;
            } else if self.matches(&[TokenKind::Punct(Punctuation::Dot)]) {
                expr = self.finish_method_call(expr)?;
            } else {
                break;
            }
        }
        Ok(expr)
    }

    // current is '('
    fn finish_call(&mut self, callee: Expr) -> ParseResult<Expr> {
        let left_paren_span = self.current().span;
        self.open_delimiter(self.current().token_kind.clone())?;

        if self.matches(&[TokenKind::EOF, TokenKind::Punct(Punctuation::Semicolon)]) {
            return Err(UnclosedDelimiter {
                src: self.source.to_string(),
                span: left_paren_span,
                delimiter: TokenKind::Delim(Delimiter::LeftParen),
            }
            .into());
        }

        let mut arguments = vec![];

        if !self.matches(&[TokenKind::Delim(Delimiter::RightParen)]) {
            let expr_left_span = self.current().span;
            arguments.push(AstNode::new(
                self.expression()?,
                self.create_span(expr_left_span, self.previous().span),
            ));
            while self.consume(&[TokenKind::Punct(Punctuation::Comma)]) {
                let expr_left_span = self.current().span;
                arguments.push(AstNode::new(
                    self.expression()?,
                    self.create_span(expr_left_span, self.previous().span),
                ));
            }
        }

        self.close_delimiter(self.current().token_kind.clone())?;

        Ok(Expr::Call(CallExpr {
            callee: Box::new(AstNode::new(callee, left_paren_span)),
            arguments,
        }))
    }

    fn finish_method_call(&mut self, receiver: Expr) -> ParseResult<Expr> {
        self.advance_position();

        let field = match self.current().token_kind.clone() {
            TokenKind::Ident(name) => {
                let span = self.current().span;
                self.advance_position();
                AstNode::new(name, span)
            }
            _ => {
                return Err(ExpectedIdentifier {
                    src: self.source.to_string(),
                    span: self.current().span,
                }
                .into());
            }
        };
        if self.matches(&[TokenKind::Delim(Delimiter::LeftParen)]) {
            let mut arguments = vec![];
            self.open_delimiter(TokenKind::Delim(Delimiter::LeftParen))?;

            if !self.matches(&[TokenKind::Delim(Delimiter::RightParen)]) {
                let expr_left_span = self.current().span;
                arguments.push(AstNode::new(
                    self.expression()?,
                    self.create_span(expr_left_span, self.previous().span),
                ));
                while self.consume(&[TokenKind::Punct(Punctuation::Comma)]) {
                    let expr_left_span = self.current().span;
                    arguments.push(AstNode::new(
                        self.expression()?,
                        self.create_span(expr_left_span, self.previous().span),
                    ));
                }
            }

            self.close_delimiter(TokenKind::Delim(Delimiter::RightParen))?;
            Ok(Expr::MethodCall(MethodCallExpr {
                receiver: Box::new(AstNode::new(receiver, self.previous().span)),
                method: field,
                arguments,
            }))
        } else {
            // It's a field access
            Ok(Expr::FieldAccess(FieldAccessExpr {
                receiver: Box::new(AstNode::new(receiver, self.previous().span)),
                field,
            }))
        }
    }

    /// current is token to parse, end is after the token
    fn primary(&mut self) -> ParseResult<Expr> {
        match self.current().token_kind {
            TokenKind::Delim(Delimiter::RightBrace)
            | TokenKind::Delim(Delimiter::RightParen)
            | TokenKind::Delim(Delimiter::RightBracket) => {
                let token = self.current();
                self.close_delimiter(token.token_kind.clone())?;
                Err(UnexpectedClosingDelimiter {
                    src: self.source.to_string(),
                    span: self.current().span,
                    delimiter: self.current().token_kind.clone(),
                }
                .into())
            }
            TokenKind::Delim(Delimiter::LeftBracket) => {
                self.open_delimiter(self.current().token_kind.clone())?;

                let mut elements = vec![];

                if !self.matches(&[TokenKind::Delim(Delimiter::RightBracket)]) {
                    let expr_left_span = self.current().span;
                    elements.push(AstNode::new(
                        self.expression()?,
                        self.create_span(expr_left_span, self.previous().span),
                    ));

                    while self.consume(&[TokenKind::Punct(Punctuation::Comma)]) {
                        if self.matches(&[TokenKind::Delim(Delimiter::RightBracket)]) {
                            return Err(ExpectedExpression {
                                src: self.source.to_string(),
                                span: self.current().span,
                            }
                            .into());
                        }
                        let expr_left_span = self.current().span;
                        elements.push(AstNode::new(
                            self.expression()?,
                            self.create_span(expr_left_span, self.previous().span),
                        ));
                    }
                }
                self.close_delimiter(TokenKind::Delim(Delimiter::RightBracket))?;
                Ok(Expr::Literal(LiteralExpr::VecLiteral(elements)))
            }
            TokenKind::Keyword(Keyword::False) => {
                self.advance_position();
                Ok(Expr::Literal(LiteralExpr::Bool(false)))
            }
            TokenKind::Keyword(Keyword::True) => {
                self.advance_position();
                Ok(Expr::Literal(LiteralExpr::Bool(true)))
            }
            TokenKind::Keyword(Keyword::Nil) => {
                self.advance_position();
                Ok(Expr::Literal(LiteralExpr::Nil))
            }
            TokenKind::Delim(Delimiter::LeftParen) => {
                let opening_paren_span = self.current().span;
                self.open_delimiter(self.current().token_kind.clone())?;

                let expr = if self.next_is(TokenKind::Delim(Delimiter::RightParen)) {
                    Err(ExpectedExpression {
                        src: self.source.to_string(),
                        span: self.create_span(opening_paren_span, self.peek().span),
                    }
                    .into())
                } else {
                    self.expression()
                }?;

                self.close_delimiter(self.current().token_kind.clone())?;

                Ok(Expr::Grouping(Box::new(AstNode::new(
                    expr,
                    self.create_span(opening_paren_span, self.current().span),
                ))))
            }
            TokenKind::Literal(Literal::Int(value)) => {
                let span = self.current().span;
                self.advance_position();

                if self.current_is(TokenKind::Ident(String::new())) {
                    return Err(InvalidIdentifier {
                        src: self.source.to_string(),
                        span,
                        message: "A variable cannot start with a number".to_string(),
                        found: self.current().token_kind.to_string(),
                    }
                    .into());
                }
                Ok(Expr::Literal(LiteralExpr::Int(value)))
            }
            TokenKind::Literal(Literal::Float(value)) => {
                let span = self.current().span;
                self.advance_position();

                if self.current_is(TokenKind::Ident(String::new())) {
                    return Err(InvalidIdentifier {
                        src: self.source.to_string(),
                        span,
                        message: "A variable cannot start with a number".to_string(),
                        found: self.current().token_kind.to_string(),
                    }
                    .into());
                }
                Ok(Expr::Literal(LiteralExpr::Float(value)))
            }
            TokenKind::Literal(Literal::String(ref value)) => {
                let string = value.clone();
                self.advance_position();
                Ok(Expr::Literal(LiteralExpr::String(string)))
            }
            TokenKind::Ident(ref name) => {
                let string = name.clone();
                let name_span = self.current().span;
                self.advance_position();

                if self.consume(&[TokenKind::Delim(Delimiter::LeftBrace)]) {
                    let mut fields = vec![];

                    while !self.matches(&[TokenKind::Delim(Delimiter::RightBrace)]) {
                        let field_name = match self.current().token_kind.clone() {
                            TokenKind::Ident(field_name) => {
                                let span = self.current().span;
                                self.advance_position();
                                AstNode::new(field_name, span)
                            }
                            _ => {
                                return Err(ExpectedIdentifier {
                                    src: self.source.to_string(),
                                    span: self.current().span,
                                }
                                .into());
                            }
                        };
                        if !self.consume(&[TokenKind::Punct(Punctuation::Colon)]) {
                            return Err(UnexpectedToken {
                                src: self.source.to_string(),
                                span: self.current().span,
                                found: self.current().token_kind.clone(),
                                expected: "':' after field name".to_string(),
                            }
                            .into());
                        }
                        let expr_left_span = self.current().span;
                        let value = self.expression()?;
                        let expr_right_span = self.previous().span;

                        fields.push((
                            field_name.clone(),
                            AstNode::new(value, self.create_span(expr_left_span, expr_right_span)),
                        ));
                        if !self.matches(&[TokenKind::Delim(Delimiter::RightBrace)]) {
                            if !self.consume(&[TokenKind::Punct(Punctuation::Comma)]) {
                                return Err(UnexpectedToken {
                                    src: self.source.to_string(),
                                    span: self.current().span,
                                    found: self.current().token_kind.clone(),
                                    expected: "',' or '}'".to_string(),
                                }
                                .into());
                            }
                        }
                    }

                    self.consume(&[TokenKind::Delim(Delimiter::RightBrace)]);

                    Ok(Expr::StructInit(StructInitExpr {
                        name: AstNode::new(string, name_span),
                        fields,
                    }))
                } else {
                    Ok(Expr::Variable(AstNode::new(string, name_span)))
                }
            }
            TokenKind::EOF => Err(UnexpectedEOF {
                src: self.source.to_string(),
                expected: "unexpected EOF".to_string(),
            }
            .into()),
            TokenKind::Punct(Punctuation::Semicolon) => {
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
