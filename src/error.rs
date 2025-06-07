use crate::TokenKind;
use crate::interpreters::ControlFlow;
use crate::type_inferrer::Type;
use miette::{Diagnostic, SourceSpan, diagnostic};
use thiserror::Error;

#[derive(Debug)]
pub enum InterpreterError {
    RuntimeError(RuntimeError),
    ControlFlowError(ControlFlow),
}

#[derive(Debug, Error, Diagnostic)]
pub enum RuntimeError {
    #[error("Cannot print value of type '{type_name}'")]
    #[diagnostic(help("This type of value cannot be displayed"), code(runtime::unprintable_value))]
    UnprintableValue {
        #[source_code]
        src: String,

        #[label("attempted to print unprintable value here")]
        span: SourceSpan,

        type_name: String,
    },
    #[error("Division by zero")]
    #[diagnostic(help("Cannot divide by zero"), code(runtime::division_by_zero))]
    DivisionByZero {
        #[source_code]
        src: String,

        #[label("division by zero here")]
        span: SourceSpan,
    },

    #[error("Index out of bounds: {index} (length: {length})")]
    #[diagnostic(help("Array index is outside the valid range"), code(runtime::index_out_of_bounds))]
    IndexOutOfBounds {
        #[source_code]
        src: String,

        #[label("invalid index access here")]
        span: SourceSpan,

        index: usize,
        length: usize,
    },
}

#[derive(Debug, Error, Diagnostic)]
pub enum TypeInferrerError {
    #[error("Cannot declare struct '{name}' with duplicate field names")]
    #[diagnostic(help("Struct fields must have unique names"), code(type_inferrer::duplicate_field_on_declaration))]
    DuplicateFieldDeclaration {
        #[source_code]
        src: String,

        #[label("duplicate field name")]
        span: SourceSpan,

        name: String,
    },

    #[error("Cannot instantiate instance with duplicate field names")]
    #[diagnostic(help("Struct fields must have unique names"), code(type_inferrer::duplicate_field_on_instantation))]
    DuplicateFieldInstantiation {
        #[source_code]
        src: String,

        #[label("duplicate field name")]
        span: SourceSpan,

        name: String,
    },
    #[error("no field '{field}' on type '{struct_name}'")]
    #[diagnostic(code(type_inferrer::unknown_field))]
    UnknownField {
        #[source_code]
        src: String,

        #[label("unknown field")]
        span: SourceSpan,
        field: String,
        struct_name: String,
    },

    #[error("Missing required field '{field}' in struct '{struct_name}'")]
    #[diagnostic(code(type_inferrer::missing_field))]
    MissingField {
        #[source_code]
        src: String,

        #[label("missing field in struct initialization")]
        span: SourceSpan,
        field: String,
        struct_name: String,
    },

    #[error("Undefined field '{field}'in '{struct_name}'")]
    #[diagnostic(code(type_inferrer::undefined_field))]
    UndefinedField {
        #[source_code]
        src: String,

        #[label("undefined field")]
        span: SourceSpan,

        field: String,
        struct_name: String,
    },
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

    #[error("Type annotations needed for '{name}'")]
    #[diagnostic(help("Variable needs an initial value or type annotation"), code(type_inferrer::cannot_infer_type))]
    CannotInferType {
        #[source_code]
        src: String,

        #[label("cannot infer type here")]
        span: SourceSpan,

        name: String,
    },
    #[error("Wrong number of arguments: expected {expected}, found {found}")]
    #[diagnostic(help("Function call requires {expected} arguments"), code(type_inferrer::wrong_argument_count))]
    WrongArgumentCount {
        #[source_code]
        src: String,

        #[label("incorrect number of arguments")]
        span: SourceSpan,

        expected: usize,
        found: usize,
    },
    #[error("Cannot call non-function type '{found:?}'")]
    #[diagnostic(
        help("This value is not callable - only functions can be called"),
        code(type_inferrer::not_callable)
    )]
    NotCallable {
        #[source_code]
        src: String,

        #[label("attempted to call non-function here")]
        span: SourceSpan,

        found: Type,
    },

    #[error("Condition must be boolean")]
    #[diagnostic(
        help("If conditions, while loops, and other conditionals require boolean expressions"),
        code(type_inferrer::non_boolean_condition)
    )]
    NonBooleanCondition {
        #[source_code]
        src: String,

        #[label("non-boolean condition here")]
        span: SourceSpan,

        found: Type,
    },

    #[error("Method '{method}' does not exist on type {base_type:?}")]
    #[diagnostic(help("This type doesn't have the requested method"), code(type_inferrer::unknown_method))]
    UnknownMethod {
        #[source_code]
        src: String,

        #[label("unknown method")]
        span: SourceSpan,

        method: String,
        base_type: Type,
    },
}

#[derive(Debug, Error, Diagnostic)]
pub enum ResolverError {
    #[error("'{name}' is not a struct")]
    #[diagnostic(code(resolver::not_a_struct))]
    NotAStruct {
        #[source_code]
        src: String,

        #[label("not a struct type")]
        span: SourceSpan,
        name: String,
    },
    #[error("Return statement used outside of a function")]
    #[diagnostic(
        help("Return statements can only be used inside functions"),
        code(resolver::return_outside_function)
    )]
    ReturnOutsideFunction {
        #[source_code]
        src: String,

        #[label("invalid return statement here")]
        span: SourceSpan,
    },

    #[error("Variable '{name}' used before initialization")]
    #[diagnostic(
        help("Make sure to initialize the variable before using it"),
        code(resolver::uninitialized_variable)
    )]
    UninitializedVariable {
        #[source_code]
        src: String,

        #[label("variable used here before being initialized")]
        span: SourceSpan,

        name: String,
    },
    #[error("Undefined generic type parameter '{name}'")]
    #[diagnostic(help("This generic type parameter has not been declared"), code(resolver::undefined_generic))]
    UndefinedGeneric {
        #[source_code]
        src: String,

        #[label("undefined generic type parameter used here")]
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
    #[diagnostic(
        help("Each parameter in a lambda function must have a unique name"),
        code(resolver::duplicate_lambda_parameter)
    )]
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
    #[error("Function '{name}' is already defined")]
    #[diagnostic(help("A function with this name already exists in this scope"), code(resolver::duplicate_function))]
    DuplicateFunction {
        #[source_code]
        src: String,

        #[label("function already defined")]
        span: SourceSpan,

        name: String,
    },

    #[error("Struct '{name}' is already defined")]
    #[diagnostic(help("A struct with this name already exists in this scope"), code(resolver::duplicate_struct))]
    DuplicateStruct {
        #[source_code]
        src: String,

        #[label("struct already defined")]
        span: SourceSpan,

        name: String,
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
    #[diagnostic(help("change the function name"), code(parser::invalid_function_name))]
    InvalidFunctionName {
        #[source_code]
        src: String,

        #[label("this function")]
        span: SourceSpan,

        message: String,
    },

    #[error("Invalid struct name: {message}")]
    #[diagnostic(help("change the struct name"), code(parser::invalid_struct_name))]
    InvalidStructName {
        #[source_code]
        src: String,

        #[label("this struct")]
        span: SourceSpan,

        message: String,
    },
}

#[derive(Debug, Error, Diagnostic)]
pub enum LexError {
    #[error("Unterminated multiline comment")]
    #[diagnostic(code(lex::unterminated_comment))]
    UnterminatedComment {
        #[source_code]
        src: String,
        #[label("Comment started here but was never closed")]
        span: SourceSpan,
    },
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
