use crate::TokenKind;
use miette::{diagnostic, Diagnostic, NamedSource, SourceSpan};
use thiserror::Error;

#[derive(Debug, Error, Diagnostic)]
pub enum ParseError {
    #[error("Unclosed paranthesis")]
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

    #[error("Expected {expected:?}, found {found:?}")]
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
    #[error("Missing semicolon at end of statement")]
    #[diagnostic(
        help("statements must end with a semicolon (`;`)."),
        code(parser::unexpected_eof)
    )]
    MissingSemicolon {
        #[source_code]
        src: String,

        #[label("expected ';' here")]
        span: SourceSpan,
    },

    #[error("Expected {expected:?}, found EOF")]
    #[diagnostic(help("Complete the expression"), code(parser::unexpected_eof))]
    UnexpectedEOF {
        #[source_code]
        src: String,

        expected: String,
    },
    #[error("Empty input")]
    #[diagnostic(help("Please provide code to parse."), code(parser::empty_input))]
    EmptyInput {
        #[source_code]
        src: String,
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
