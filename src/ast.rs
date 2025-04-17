use crate::TokenKind;
use miette::SourceSpan;

#[derive(Debug, Clone, PartialEq)]
pub struct Spanned<T> {
    pub node: T,
    pub span: SourceSpan,
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

#[derive(Debug, Clone, PartialEq)]
pub struct Program {
    pub statements: Vec<Stmt>,
    pub span: SourceSpan,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    ExprStmt(Spanned<Expr>),
    PrintStmt(Spanned<Expr>),
    VarDecl(Spanned<VarDeclStmt>),
    FunDecl(Spanned<FunDeclStmt>),
    Block(Spanned<BlockStmt>),
    If(Spanned<IfStmt>),
    While(Spanned<WhileStmt>),
    Return(Spanned<Option<Expr>>),
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
    pub body: Spanned<BlockStmt>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BlockStmt {
    pub statements: Vec<Stmt>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct IfStmt {
    pub condition: Expr,
    pub then_branch: Spanned<BlockStmt>,
    pub else_branch: Option<Spanned<BlockStmt>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct WhileStmt {
    pub condition: Expr,
    pub body: Spanned<BlockStmt>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Literal(Spanned<LiteralExpr>),
    Unary(Spanned<UnaryExpr>),
    Binary(Spanned<BinaryExpr>),
    Grouping(Spanned<Box<Expr>>),
    Variable(Ident),
    Assign(Spanned<AssignExpr>),
    Logical(Spanned<LogicalExpr>),
    Call(Spanned<CallExpr>),
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
