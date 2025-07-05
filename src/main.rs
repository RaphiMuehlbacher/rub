use rub::ast_lowerer::AstLowerer;
use rub::interpreter::Interpreter;
use rub::{Lexer, MethodRegistry, Parser, Resolver, TypeInferrer};
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

    let mut lexer = Lexer::new(code);
    let lex_result = lexer.lex();
    time_log!(start, "Lexing");

    if !lex_result.errors.is_empty() {
        for err in lex_result.errors {
            println!("{:?}", err);
        }
        return;
    }

    let mut parser = Parser::new(lex_result.tokens, code.to_string());
    let parse_result = parser.parse();
    time_log!(start, "Parsing");

    if !parse_result.errors.is_empty() {
        for error in parse_result.errors {
            println!("{:?}", error);
        }
        return;
    }

    let mut resolver = Resolver::new(&parse_result.ast, code.to_string());
    let resolve_result = resolver.resolve();
    time_log!(start, "Resolving");

    if !resolve_result.errors.is_empty() {
        for error in resolve_result.errors {
            println!("{:?}", error);
        }
        return;
    }

    let mut ast_lowerer = AstLowerer::new(
        &parse_result.ast,
        resolve_result.resolution_map,
        resolve_result.scope_tree,
        resolve_result.def_map,
    );
    let ast_lowerer_result = ast_lowerer.lower();
    time_log!(start, "Lowering");

    let mut cloned_def_map = resolve_result.def_map.clone();
    let method_registry = MethodRegistry::new(&mut cloned_def_map);

    let mut type_inferrer = TypeInferrer::new(
        &ast_lowerer_result.ir_program,
        &resolve_result.def_map,
        &ast_lowerer_result.function_bodies,
        &method_registry,
        code.to_string(),
    );
    let type_inference_result = type_inferrer.infer();
    time_log!(start, "Type Inference");

    if !type_inference_result.errors.is_empty() {
        for error in type_inference_result.errors {
            println!("{:?}", error);
        }
        return;
    }
    let mut interpreter = Interpreter::new(
        &ast_lowerer_result.ir_program,
        type_inference_result.type_env,
        resolve_result.def_map,
        &method_registry,
        code.to_string(),
    );
    let error = interpreter.interpret().error;
    if let Some(err) = error {
        println!("{:?}", err);
    }
    time_log!(start, "Interpreting");
}

fn main() {
    let mut path = "source.rub".to_string();
    let source = fs::read_to_string(&mut path).unwrap_or_else(|_| panic!("Error reading file {}", path));
    let source = format!("{} ", source);
    interpret(&source);
}
