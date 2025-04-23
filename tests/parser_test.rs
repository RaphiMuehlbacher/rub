use rslox::parser::Expr::LiteralExpr;
use rslox::parser::{BinaryOp, Expr, Literal, Stmt};
use rslox::{Lexer, Parser};

fn parse(source: &str) -> (Vec<Stmt>, Vec<miette::Report>) {
    let source = format!("{source} ");
    let mut lexer = Lexer::new(&source);
    let tokens = lexer.lex();

    let mut parser = Parser::new(tokens, &source);
    let statements = parser.parse();

    (statements, errors)
}

#[test]
fn test_empty() {
    let (statements, errors) = parse("");
    assert_eq!(errors.len(), 0);
    assert_eq!(statements.len(), 0);
}

#[test]
fn test_binary() {
    let (statements, errors) = parse("3 + 1;");
    assert_eq!(errors.len(), 0);
    assert_eq!(statements.len(), 1);
    if let Stmt::ExprStmt { expr, .. } = &statements[0] {
        if let Expr::Binary { left, op, right, .. } = expr {
            if let LiteralExpr(Literal::Number { value, .. }) = **left {
                assert_eq!(value, 3.0);
            } else {
                panic!("Expected number literal for left operand");
            }

            assert!(matches!(op, BinaryOp::Plus));

            if let LiteralExpr(Literal::Number { value, .. }) = **right {
                assert_eq!(value, 1.0);
            } else {
                panic!("Expected number literal for right operand");
            }
        } else {
            panic!("Expected binary expression");
        }
    } else {
        panic!("Expected expression statement");
    }
}
