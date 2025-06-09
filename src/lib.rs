pub mod ast;
// pub mod builtins;
pub mod error;
// pub mod interpreter;
pub mod ir;
pub mod lexer;
// pub mod method_registry;
pub mod ast_lowerer;
pub mod parser;
pub mod resolver;
// pub mod type_inferrer;

pub use lexer::{Lexer, Token, TokenKind};
// pub use method_registry::MethodRegistry;
pub use parser::Parser;
pub use resolver::Resolver;
// pub use type_inferrer::TypeInferrer;
