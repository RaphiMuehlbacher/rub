use rslox::{Lexer, Parser, Resolver, TypeInferrer};
use std::fs;

fn main() {
    let mut path = "source.lox".to_string();
    let source = fs::read_to_string(&mut path).expect(format!("Error reading file {}", path).as_str());
    let source = format!("{} ", source);

    let mut lexer = Lexer::new(&source);
    let lex_result = lexer.lex();

    if !lex_result.errors.is_empty() {
        for err in lex_result.errors {
            println!("Lexing error: {:?}", err);
        }
        return;
    }

    let mut parser = Parser::new(lex_result.tokens, source.as_str());
    let parse_result = parser.parse();

    if !parse_result.errors.is_empty() {
        for error in parse_result.errors {
            println!("{:?}", error);
        }
    }

    let mut resolver = Resolver::new(&parse_result.ast, source.clone());
    let resolving_errors = resolver.resolve();

    if !resolving_errors.is_empty() {
        for error in resolving_errors {
            println!("{:?}", error);
        }
    }

    let mut type_inferrer = TypeInferrer::new(&parse_result.ast, source.clone());
    let type_inference_result = type_inferrer.infer();

    if !type_inference_result.errors.is_empty() {
        for error in type_inference_result.errors {
            println!("{:?}", error);
        }
    }
}
