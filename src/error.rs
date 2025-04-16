use crate::TokenKind;
use miette::{diagnostic, Diagnostic, SourceSpan};
use thiserror::Error;

#[derive(Debug, Error, Diagnostic)]
pub enum ParseError {
    #[error("Unclosed parenthesis")]
    #[diagnostic(
        help("Make sure all opening parentheses are closed."),
        code(parser::unclosed_paren)
    )]
    UnclosedParenthesis {
        #[source_code]
        src: String,

        #[label("opening parenthesis here requires a matching closing one")]
        span: SourceSpan,
    },

    #[error("Expected identifier")]
    #[diagnostic(
        code(parser::expected_identifier),
        help("Expected {context} name here")
    )]
    ExpectedIdentifier {
        #[source_code]
        src: String,

        #[label("expected identifier here")]
        span: SourceSpan,

        context: String,
    },

    #[error("Expected statement after {keyword}")]
    #[diagnostic(
        help("A {keyword} statement must be followed by a body."),
        code(parser::missing_statement)
    )]
    MissingStatement {
        #[source_code]
        src: String,

        #[label("expected statement here")]
        span: SourceSpan,

        keyword: String,
    },

    #[error("Expected left parenthesis after `{paren_type}`")]
    #[diagnostic(
        help("The condition of {paren_type} must be enclosed in parenthesis"),
        code(parser::missing_left_paren)
    )]
    MissingLeftParenthesis {
        #[source_code]
        src: String,

        #[label("expected '(' here")]
        span: SourceSpan,
        paren_type: String,
    },

    #[error("Expected left brace")]
    #[diagnostic(help("A left brace is needed."), code(parser::missing_left_paren))]
    MissingLeftBrace {
        #[source_code]
        src: String,

        #[label("expected '{{' here")]
        span: SourceSpan,
    },

    #[error("Expected right parenthesis after `{paren_type}`")]
    #[diagnostic(
        help("The condition of {paren_type} must be enclosed in parenthesis"),
        code(parser::missing_right_paren)
    )]
    MissingRightParenthesis {
        #[source_code]
        src: String,

        #[label("expected ')' here")]
        span: SourceSpan,
        paren_type: String,
    },

    #[error("Unclosed brace")]
    #[diagnostic(
        help("Make sure all opening braces are closed."),
        code(parser::unclosed_paren)
    )]
    UnclosedBrace {
        #[source_code]
        src: String,

        #[label("opening brace here requires a matching closing one")]
        span: SourceSpan,
    },

    #[error("Unexpected closing brace")]
    #[diagnostic(
        help("This closing brace doesn't have a matching opening brace."),
        code(parser::unexpected_closing_brace)
    )]
    UnexpectedClosingBrace {
        #[source_code]
        src: String,

        #[label("unexpected closing brace with no matching opening brace")]
        span: SourceSpan,
    },

    #[error("Invalid condition in if statement")]
    #[diagnostic(
        help("The condition in an if statement must be a valid expression."),
        code(parser::invalid_condition)
    )]
    InvalidCondition {
        #[source_code]
        src: String,

        #[label("invalid condition here")]
        span: SourceSpan,
    },

    #[error("Expected block")]
    #[diagnostic(
        code(parser::missing_block),
        help("Expected a block enclosed in braces")
    )]
    MissingBlock {
        #[source_code]
        src: String,

        #[label("expected block here")]
        span: SourceSpan,
    },

    #[error("Expected {expected}, found {found:?}")]
    #[diagnostic(
        help("The parser expected a different token here."),
        code(parser::unexpected_token)
    )]
    UnexpectedToken {
        #[source_code]
        src: String,

        #[label("unexpected token found here")]
        span: SourceSpan,

        expected: String,
        found: TokenKind,
    },
    #[error("Missing semicolon")]
    #[diagnostic(
        help("statements must end with a semicolon (`;`)."),
        code(parser::missing_semicolon)
    )]
    MissingSemicolon {
        #[source_code]
        src: String,

        #[label("expected ';' here")]
        span: SourceSpan,
    },

    #[error("unnecessary trailing semicolon")]
    #[diagnostic(
        help("help: remove this semicolon"),
        code(parser::redundant_semicolon),
        severity(Warning)
    )]
    RedundantSemicolon {
        #[source_code]
        src: String,

        #[label("help: remove this semicolon")]
        span: SourceSpan,
    },

    #[error("unnecessary parenthesis")]
    #[diagnostic(
        help("these parentheses are not needed"),
        code(parser::redundant_parenthesis),
        severity(Warning)
    )]
    RedundantParenthesis {
        #[source_code]
        src: String,

        #[label("opening")]
        first: SourceSpan,

        #[label("closing")]
        second: SourceSpan,
    },

    #[error("Expected {expected:?}, found EOF")]
    #[diagnostic(help("Complete the expression"), code(parser::unexpected_eof))]
    UnexpectedEOF {
        #[source_code]
        src: String,

        expected: String,
    },

    #[error("Unmatched delimiter")]
    #[diagnostic(
        help("expected {expected:?}, found {found:?}"),
        code(parser::unmatched_delimiter)
    )]
    UnmatchedDelimiter {
        #[source_code]
        src: String,

        #[label("opening delimiter here")]
        opening_span: SourceSpan,

        #[label("mismatched closing delimiter here")]
        closing_span: SourceSpan,

        expected: TokenKind,
        found: TokenKind,
    },

    #[error("unclosed delimiter")]
    #[diagnostic(code(parse::unclosed_delimiter), help("missing closing {delimiter:?}"))]
    UnclosedDelimiter {
        #[source_code]
        src: String,

        #[label("unclosed delimiter here")]
        span: SourceSpan,

        delimiter: TokenKind,
    },

    #[error("unexpected closing delimiter: '{delimiter:?}'")]
    #[diagnostic(
        help("I have no clue which error message"),
        code(parser::unexpected_closing_delimiter)
    )]
    UnexpectedClosingDelimiter {
        #[source_code]
        src: String,

        #[label("no matching opening delimiter")]
        span: SourceSpan,
        delimiter: TokenKind,
    },

    #[error("expected '{expected:?}' but found '{found:?}'")]
    #[diagnostic(
        help("I have no clue which error message"),
        code(parser::mismatched_delimiter)
    )]
    MismatchedDelimiter {
        #[source_code]
        src: String,

        #[label("mismatched closing delimiter")]
        closing_span: SourceSpan,

        #[label("opening delimiter here")]
        opening_span: SourceSpan,

        found: TokenKind,
        expected: TokenKind,
    },

    #[error("Expected expression")]
    #[diagnostic(
        help("An expression was expected at this position."),
        code(parser::expected_expression)
    )]
    ExpectedExpression {
        #[source_code]
        src: String,

        #[label("expected an expression here")]
        span: SourceSpan,
    },

    #[error("Missing operand")]
    #[diagnostic(code(parse::missing_operand), help("Add the missing {side} operand"))]
    MissingOperand {
        #[source_code]
        src: String,
        #[label("Operator here")]
        span: SourceSpan,
        side: String,
    },

    #[error("Missing variable name in declaration")]
    #[diagnostic(
        help("Variable declarations must include a variable name."),
        code(parser::missing_variable_declaration_name)
    )]
    MissingVariableDeclarationName {
        #[source_code]
        src: String,

        #[label("variable name expected after 'var' keyword")]
        span: SourceSpan,
    },

    #[error("Missing variable name in assignment")]
    #[diagnostic(
        help("Variable assignments must include a variable name."),
        code(parser::missing_variable_assignment_name)
    )]
    MissingVariableAssignmentName {
        #[source_code]
        src: String,

        #[label("variable name expected")]
        span: SourceSpan,
    },

    #[error("Invalid assignment target: {message}")]
    #[diagnostic(
        help("Only variables can be assignment targets"),
        code(parser::invalid_assignment_target)
    )]
    InvalidAssignmentTarget {
        #[source_code]
        src: String,

        #[label("cannot assign to this")]
        span: SourceSpan,

        message: String,
    },
}

#[derive(Debug, Error, Diagnostic)]
pub enum LexError {
    #[error("Unexpected character: {character}")]
    #[diagnostic(
        help("This character isn't recognized by the lexer."),
        code(lexer::unexpected_char)
    )]
    UnexpectedCharacter {
        #[source_code]
        src: String,

        #[label("unexpected `{character}` found here")]
        span: SourceSpan,

        character: char,
    },

    #[error("Unterminated string literal")]
    #[diagnostic(
        help("Make sure all string literals are closed with a `\"`."),
        code(lexer::unterminated_string)
    )]
    UnterminatedString {
        #[source_code]
        src: String,

        #[label("string starts here but never ends")]
        span: SourceSpan,
    },
}
