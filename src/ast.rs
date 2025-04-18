use crate::TokenKind;
use miette::SourceSpan;

#[derive(Debug, Clone, PartialEq)]
pub struct Typed<T> {
    pub node: T,
    pub span: SourceSpan,
    pub type_id: usize,
}

impl<T> Typed<T> {
    pub fn new(node: T, span: SourceSpan) -> Self {
        static mut TYPE_ID: usize = 0;

        let type_id = unsafe {
            let id = TYPE_ID;
            TYPE_ID += 1;
            id
        };

        Self {
            node,
            span,
            type_id,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Delimiter {
    pub delimiter: TokenKind,
    pub span: SourceSpan,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Ident {
    pub name: String,
    pub span: SourceSpan,
}

impl Ident {
    pub fn new(name: &str, span: SourceSpan) -> Self {
        Self {
            name: name.to_string(),
            span,
        }
    }
}
pub trait Visitor<T> {
    fn visit_program(&mut self, program: &Program) -> T;
    fn visit_stmt(&mut self, stmt: &Stmt) -> T;
    fn visit_expr(&mut self, expr: &Expr) -> T;
}

pub trait Accept<T> {
    fn accept(&self, visitor: &mut impl Visitor<T>) -> T;
}

#[derive(Debug, Clone, PartialEq)]
pub struct Program {
    pub statements: Vec<Stmt>,
    pub span: SourceSpan,
}

impl<T> Accept<T> for Program {
    fn accept(&self, visitor: &mut impl Visitor<T>) -> T {
        visitor.visit_program(self)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    ExprStmt(Typed<Expr>),
    PrintStmt(Typed<Expr>),
    VarDecl(Typed<VarDeclStmt>),
    FunDecl(Typed<FunDeclStmt>),
    Block(Typed<BlockStmt>),
    If(Typed<IfStmt>),
    While(Typed<WhileStmt>),
    Return(Typed<Option<Expr>>),
}

impl<T> Accept<T> for Stmt {
    fn accept(&self, visitor: &mut impl Visitor<T>) -> T {
        visitor.visit_stmt(self)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct VarDeclStmt {
    pub ident: Ident,
    pub initializer: Option<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunDeclStmt {
    pub ident: Ident,
    pub params: Vec<Ident>,
    pub body: Typed<BlockStmt>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BlockStmt {
    pub statements: Vec<Stmt>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct IfStmt {
    pub condition: Expr,
    pub then_branch: Typed<BlockStmt>,
    pub else_branch: Option<Typed<BlockStmt>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct WhileStmt {
    pub condition: Expr,
    pub body: Typed<BlockStmt>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Literal(Typed<LiteralExpr>),
    Unary(Typed<UnaryExpr>),
    Binary(Typed<BinaryExpr>),
    Grouping(Typed<Box<Expr>>),
    Variable(Ident),
    Assign(Typed<AssignExpr>),
    Logical(Typed<LogicalExpr>),
    Call(Typed<CallExpr>),
    Lambda(Typed<LambdaExpr>),
}

impl<T> Accept<T> for Expr {
    fn accept(&self, visitor: &mut impl Visitor<T>) -> T {
        visitor.visit_expr(self)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct UnaryExpr {
    pub op: UnaryOp,
    pub expr: Box<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BinaryExpr {
    pub left: Box<Expr>,
    pub op: BinaryOp,
    pub right: Box<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LogicalExpr {
    pub left: Box<Expr>,
    pub op: LogicalOp,
    pub right: Box<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct AssignExpr {
    pub target: Ident,
    pub value: Box<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CallExpr {
    pub callee: Box<Expr>,
    pub arguments: Vec<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LambdaExpr {
    pub parameters: Vec<Ident>,
    pub body: Typed<BlockStmt>,
}
#[derive(Debug, Clone, PartialEq)]
pub enum LiteralExpr {
    Number(f64),
    String(String),
    Bool(bool),
    Nil,
}

#[derive(Debug, Clone, PartialEq)]
pub enum UnaryOp {
    Bang,
    Minus,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LogicalOp {
    And,
    Or,
}

#[derive(Debug, Clone, PartialEq)]
pub enum BinaryOp {
    Plus,
    Minus,
    Star,
    Slash,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,
    Equal,
    EqualEqual,
    BangEqual,
}
