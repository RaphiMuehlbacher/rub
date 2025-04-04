use std::fs;
use miette::{Report};
use rslox::Lexer;

fn main() -> Result<(), Report> {
    let mut path = "source.lox".to_string();
    let source = fs::read_to_string(&mut path).expect(format!("Error reading file {}", path).as_str());

    let mut lexer = Lexer::new(&source);
    let tokens = lexer.lex();

    for token_result in tokens {
        match token_result {
            Ok(token) => {
                println!("{:?}", token);
            }
            Err(err) => {
                eprintln!("{:?}", err);
            }
        }
    }

    Ok(())
}
