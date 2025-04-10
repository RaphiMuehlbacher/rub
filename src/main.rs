use miette::Report;
use rslox::{Lexer, Parser};
use std::fs;

fn main() -> Result<(), Report> {
    let mut path = "source.lox".to_string();
    let source =
        fs::read_to_string(&mut path).expect(format!("Error reading file {}", path).as_str());
    let shifted_source = format!("{} ", source);

    let mut lexer = Lexer::new(source.as_str());
    let tokens_results = lexer.lex();
    let mut tokens = Vec::new();
    let mut errors = Vec::new();

    for res in tokens_results {
        match res {
            Ok(token) => tokens.push(token.clone()),
            Err(err) => errors.push(err),
        }
    }

    for err in errors {
        eprintln!("Lexing error: {:?}", err);
    }

    // for token in &tokens {
    //     println!("{:?}", token);
    // }

    let mut parser = Parser::new(tokens, shifted_source.as_str());
    let ast = parser.parse();

    if !parser.get_errors().is_empty() {
        for error in parser.get_errors() {
            eprintln!("{:?}", error);
        }
    }

    println!("{:?}", ast);

    Ok(())
}
