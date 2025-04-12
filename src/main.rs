use rslox::{Lexer, Parser};
use std::fs;

fn main() {
    let mut path = "source.lox".to_string();
    let source =
        fs::read_to_string(&mut path).expect(format!("Error reading file {}", path).as_str());
    let source = format!("{} ", source);

    let mut lexer = Lexer::new(&source);
    let tokens = lexer.lex();

    for err in lexer.get_errors() {
        eprintln!("Lexing error: {:?}", err);
    }

    let mut parser = Parser::new(tokens, source.as_str());
    let ast = parser.parse();

    for error in parser.get_errors() {
        eprintln!("{:?}", error);
    }

    println!("{:?}", ast);
}
