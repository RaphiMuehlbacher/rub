use miette::{Diagnostic, SourceSpan};
use thiserror::Error;
use crate::TokenKind;

#[derive(Debug, Error, Diagnostic)]
pub enum ParseError {
    #[error("Expected closing ')' after expression")]
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

        expected: TokenKind,
        found: TokenKind,
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
