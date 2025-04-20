use crate::type_inferrer::Type;
use crate::TokenKind;
use miette::{diagnostic, Diagnostic, SourceSpan};
use thiserror::Error;

#[derive(Debug, Error, Diagnostic)]
pub enum TypeInferrerError {
    #[error("Type mismatch: expected {expected:?}, found {found:?}")]
    #[diagnostic(help("The types don't match"), code(type_inferrer::type_mismatch))]
    TypeMismatch {
        #[source_code]
        src: String,

        #[label("mismatched type here")]
        span: SourceSpan,

        expected: Type,
        found: Type,
    },

    #[error("Cannot infer type of variable '{name}'")]
    #[diagnostic(help("Variable needs an initial value or type annotation"), code(type_inferrer::cannot_infer_type))]
    CannotInferType {
        #[source_code]
        src: String,

        #[label("cannot infer type here")]
        span: SourceSpan,

        name: String,
    },

    #[error("Operation not supported between types {left:?} and {right:?}")]
    #[diagnostic(help("The operation cannot be performed with these types"), code(type_inferrer::invalid_operation))]
    InvalidOperation {
        #[source_code]
        src: String,

        #[label("invalid operation here")]
        span: SourceSpan,

        left: Type,
        right: Type,
    },
}

#[derive(Debug, Error, Diagnostic)]
pub enum ResolverError {
    #[error("Variable '{name}' used before initialization")]
    #[diagnostic(help("Make sure to initialize the variable before using it"), code(resolver::uninitialized_variable))]
    UninitializedVariable {
        #[source_code]
        src: String,

        #[label("variable used here before being initialized")]
        span: SourceSpan,

        name: String,
    },

    #[error("Undefined variable '{name}'")]
    #[diagnostic(help("Make sure the variable is declared before using it"), code(resolver::undefined_variable))]
    UndefinedVariable {
        #[source_code]
        src: String,

        #[label("undefined variable used here")]
        span: SourceSpan,

        name: String,
    },
    #[error("Call to undefined function '{name}'")]
    #[diagnostic(code(resolver::undefined_function))]
    UndefinedFunction {
        #[source_code]
        src: String,
        #[label("Function '{name}' is not defined")]
        span: SourceSpan,
        name: String,
    },

    #[error("Lambda functions cannot have duplicate parameter names")]
    #[diagnostic(help("Each parameter in a lambda function must have a unique name"), code(resolver::duplicate_lambda_parameter))]
    DuplicateLambdaParameter {
        #[source_code]
        src: String,

        #[label("duplicate parameter name")]
        span: SourceSpan,
    },

    #[error("Cannot declare function '{function_name}' with duplicate parameter names")]
    #[diagnostic(help("Function parameters must have unique names"), code(resolver::duplicate_parameter))]
    DuplicateParameter {
        #[source_code]
        src: String,

        #[label("duplicate parameter name")]
        span: SourceSpan,

        function_name: String,
    },
}

#[derive(Debug, Error, Diagnostic)]
pub enum ParseError {
    #[error("Expected identifier")]
    #[diagnostic(code(parser::expected_identifier), help("Expected {context} name here"))]
    ExpectedIdentifier {
        #[source_code]
        src: String,

        #[label("expected identifier here")]
        span: SourceSpan,

        context: String,
    },

    #[error("Expected block")]
    #[diagnostic(code(parser::missing_block), help("Expected a block enclosed in braces"))]
    MissingBlock {
        #[source_code]
        src: String,

        #[label("expected block here")]
        span: SourceSpan,
    },

    #[error("Expected {expected}, found {found:?}")]
    #[diagnostic(help("The parser expected a different token here."), code(parser::unexpected_token))]
    UnexpectedToken {
        #[source_code]
        src: String,

        #[label("unexpected token found here")]
        span: SourceSpan,

        expected: String,
        found: TokenKind,
    },
    #[error("Missing semicolon")]
    #[diagnostic(help("statements must end with a semicolon (`;`)."), code(parser::missing_semicolon))]
    MissingSemicolon {
        #[source_code]
        src: String,

        #[label("expected ';' here")]
        span: SourceSpan,
    },

    #[error("unnecessary trailing semicolon")]
    #[diagnostic(help("help: remove this semicolon"), code(parser::redundant_semicolon), severity(Warning))]
    RedundantSemicolon {
        #[source_code]
        src: String,

        #[label("help: remove this semicolon")]
        span: SourceSpan,
    },

    #[error("unnecessary parenthesis")]
    #[diagnostic(help("these parentheses are not needed"), code(parser::redundant_parenthesis), severity(Warning))]
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
    #[diagnostic(help("expected {expected:?}, found {found:?}"), code(parser::unmatched_delimiter))]
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
    #[diagnostic(help("I have no clue which error message"), code(parser::unexpected_closing_delimiter))]
    UnexpectedClosingDelimiter {
        #[source_code]
        src: String,

        #[label("no matching opening delimiter")]
        span: SourceSpan,
        delimiter: TokenKind,
    },

    #[error("expected '{expected:?}' but found '{found:?}'")]
    #[diagnostic(help("I have no clue which error message"), code(parser::mismatched_delimiter))]
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
    #[diagnostic(help("An expression was expected at this position."), code(parser::expected_expression))]
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

    #[error("Invalid variable name: {message}")]
    #[diagnostic(help("Only variables can be assignment targets"), code(parser::invalid_assignment_target))]
    InvalidVariableName {
        #[source_code]
        src: String,

        #[label("cannot assign to this")]
        span: SourceSpan,

        message: String,
    },

    #[error("Invalid function name: {message}")]
    #[diagnostic(help("change the function name"), code(parser::invalid_assignment_target))]
    InvalidFunctionName {
        #[source_code]
        src: String,

        #[label("this function")]
        span: SourceSpan,

        message: String,
    },
}

#[derive(Debug, Error, Diagnostic)]
pub enum LexError {
    #[error("Unexpected character: {character}")]
    #[diagnostic(help("This character isn't recognized by the lexer."), code(lexer::unexpected_char))]
    UnexpectedCharacter {
        #[source_code]
        src: String,

        #[label("unexpected `{character}` found here")]
        span: SourceSpan,

        character: char,
    },

    #[error("Unterminated string literal")]
    #[diagnostic(help("Make sure all string literals are closed with a `\"`."), code(lexer::unterminated_string))]
    UnterminatedString {
        #[source_code]
        src: String,

        #[label("string starts here but never ends")]
        span: SourceSpan,
    },
}
