use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

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
