use rub::interpreters::Interpreter;
use rub::{Lexer, Parser, Resolver, TypeInferrer};
use std::fs;
use std::time::Instant;

macro_rules! time_log {
    ($start:expr, $phase:expr) => {
        #[cfg(feature = "timing")]
        println!("{} took {:?}", $phase, $start.elapsed());
    };
}

fn interpret(code: &str) {
    #[cfg(feature = "timing")]
    let start = Instant::now();

    let mut lexer = Lexer::new(&code);
    let lex_result = lexer.lex();
    time_log!(start, "Lexing");

    if !lex_result.errors.is_empty() {
        for err in lex_result.errors {
            println!("{:?}", err);
        }
        return;
    }

    let mut parser = Parser::new(lex_result.tokens, code);
    let parse_result = parser.parse();
    time_log!(start, "Parsing");

    if !parse_result.errors.is_empty() {
        for error in parse_result.errors {
            println!("{:?}", error);
        }
        return;
    }

    let mut resolver = Resolver::new(&parse_result.ast, code.to_string());
    let resolving_errors = resolver.resolve();
    time_log!(start, "Resolving");

    if !resolving_errors.is_empty() {
        for error in resolving_errors {
            println!("{:?}", error);
        }
        return;
    }

    let mut type_inferrer = TypeInferrer::new(&parse_result.ast, code.to_string());
    let type_inference_result = type_inferrer.infer();
    time_log!(start, "Type Inference");

    if !type_inference_result.errors.is_empty() {
        for error in type_inference_result.errors {
            println!("{:?}", error);
        }
        return;
    }

    // println!("{:?}", parse_result.ast);
    let mut interpreter = Interpreter::new(&parse_result.ast, type_inference_result.type_env, code.to_string());
    let error = interpreter.interpret().error;
    if let Some(err) = error {
        println!("{:?}", err);
    }
    time_log!(start, "Interpreting");
}

fn main() {
    let mut path = "source.rub".to_string();
    let source = fs::read_to_string(&mut path).expect(format!("Error reading file {}", path).as_str());
    let source = format!("{} ", source);
    interpret(&source);
}
