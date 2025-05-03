use crate::TokenKind;
use crate::type_inferrer::Type;
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

        Self { node, span, type_id }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Delimiter {
    pub delimiter: TokenKind,
    pub span: SourceSpan,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Program {
    pub statements: Vec<Stmt>,
    pub span: SourceSpan,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    ExprStmt(Typed<Expr>),
    Print(Typed<PrintStmt>),
    VarDecl(Typed<VarDeclStmt>),
    FunDecl(Typed<FunDeclStmt>),
    Block(Typed<BlockStmt>),
    If(Typed<IfStmt>),
    While(Typed<WhileStmt>),
    Return(Typed<ReturnStmt>),
}

pub type Ident = Typed<String>;

#[derive(Debug, Clone, PartialEq)]
pub struct PrintStmt {
    pub expr: Typed<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct VarDeclStmt {
    pub ident: Ident,
    pub initializer: Option<Typed<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Parameter {
    pub name: Ident,
    pub type_annotation: Type,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunDeclStmt {
    pub ident: Ident,
    pub params: Vec<Typed<Parameter>>,
    pub body: Typed<BlockStmt>,
    pub return_type: Type,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BlockStmt {
    pub statements: Vec<Stmt>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct IfStmt {
    pub condition: Typed<Expr>,
    pub then_branch: Typed<BlockStmt>,
    pub else_branch: Option<Typed<BlockStmt>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct WhileStmt {
    pub condition: Typed<Expr>,
    pub body: Typed<BlockStmt>,
}
#[derive(Debug, Clone, PartialEq)]
pub struct ReturnStmt {
    pub expr: Option<Typed<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Literal(LiteralExpr),
    Unary(UnaryExpr),
    Binary(BinaryExpr),
    Grouping(Box<Typed<Expr>>),
    Variable(Ident),
    Assign(AssignExpr),
    Logical(LogicalExpr),
    Call(CallExpr),
    Lambda(LambdaExpr),
}

#[derive(Debug, Clone, PartialEq)]
pub struct UnaryExpr {
    pub op: Typed<UnaryOp>,
    pub expr: Box<Typed<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BinaryExpr {
    pub left: Box<Typed<Expr>>,
    pub op: Typed<BinaryOp>,
    pub right: Box<Typed<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LogicalExpr {
    pub left: Box<Typed<Expr>>,
    pub op: Typed<LogicalOp>,
    pub right: Box<Typed<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct AssignExpr {
    pub target: Ident,
    pub value: Box<Typed<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CallExpr {
    pub callee: Box<Typed<Expr>>,
    pub arguments: Vec<Typed<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LambdaExpr {
    pub parameters: Vec<Typed<Parameter>>,
    pub body: Typed<BlockStmt>,
    pub return_type: Type,
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
    EqualEqual,
    BangEqual,
}
