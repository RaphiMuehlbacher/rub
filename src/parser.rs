use crate::lexer;
use lexer::Token;

pub struct Parser<'a> {
    tokens: Vec<Token<'a>>,
    position: usize,
}

enum Expr {
    Literal,
    Unary,
    Binary,
    Grouping,
}

enum Literal {
    Number(f64),
    String(String),
    True,
    False,
    Nil,
}

struct Grouping {
    expr: Expr
}

struct Unary {
    op: UnaryOp,
    expr: Expr,
}

enum UnaryOp {
    Bang,
    Minus,
}

struct Binary {
    left: Expr,
    op: BinaryOp,
    right: Expr,
}

enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,

    GreaterEqual,
    LessEqual,
    Equal,
    EqualEqual,
    BangEqual,
}


impl<'a> Parser<'a> {
    pub fn new(tokens: Vec<Token<'a>>) -> Self {
        Parser {
            tokens,
            position: 0,
        }
    }

    pub fn parse(&self) {
        self.expression()
    }

    pub fn expression(&self) {
        todo!()
    }
}
