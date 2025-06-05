use crate::TokenKind;
use crate::type_inferrer::Type;
use miette::SourceSpan;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Typed<T> {
    pub node: T,
    pub span: SourceSpan,
    pub type_id: usize,
}

impl<T> Typed<T> {
    pub fn new(node: T, span: SourceSpan) -> Self {
        static mut TYPE_ID: usize = 1;

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
    ExprStmtNode(Typed<ExprStmt>),
    VarDecl(Typed<VarDeclStmt>),
    FunDecl(Typed<FunDeclStmt>),
    StructDecl(Typed<StructDeclStmt>),
    While(Typed<WhileStmt>),
    Return(Typed<ReturnStmt>),
}

impl Stmt {
    pub fn span(&self) -> SourceSpan {
        match self {
            Stmt::ExprStmtNode(stmt) => stmt.span,
            Stmt::VarDecl(stmt) => stmt.span,
            Stmt::FunDecl(stmt) => stmt.span,
            Stmt::StructDecl(stmt) => stmt.span,
            Stmt::While(stmt) => stmt.span,
            Stmt::Return(stmt) => stmt.span,
        }
    }
}

pub type Ident = Typed<String>;

#[derive(Debug, Clone, PartialEq)]
pub struct ExprStmt {
    pub expr: Typed<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct VarDeclStmt {
    pub ident: Ident,
    pub initializer: Option<Typed<Expr>>,
    pub type_annotation: Option<Typed<Type>>,
}

#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub struct TypedIdent {
    pub name: Ident,
    pub type_annotation: Typed<Type>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunDeclStmt {
    pub ident: Ident,
    pub params: Vec<TypedIdent>,
    pub body: Typed<BlockExpr>,
    pub generics: Vec<Ident>,
    pub return_type: Typed<Type>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StructDeclStmt {
    pub ident: Ident,
    pub fields: Vec<TypedIdent>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct WhileStmt {
    pub condition: Typed<Expr>,
    pub body: Typed<BlockExpr>,
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
    Block(BlockExpr),
    If(IfExpr),
    MethodCall(MethodCallExpr),
    StructInit(StructInitExpr),
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
    pub parameters: Vec<TypedIdent>,
    pub body: Box<Typed<BlockExpr>>,
    pub return_type: Typed<Type>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BlockExpr {
    pub statements: Vec<Stmt>,
    pub expr: Option<Box<Typed<Expr>>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct IfExpr {
    pub condition: Box<Typed<Expr>>,
    pub then_branch: Typed<BlockExpr>,
    pub else_branch: Option<Box<Typed<BlockExpr>>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MethodCallExpr {
    pub receiver: Box<Typed<Expr>>,
    pub method: Ident,
    pub arguments: Vec<Typed<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StructInitExpr {
    pub name: Ident,
    pub fields: Vec<(Ident, Box<Typed<Expr>>)>,
}
#[derive(Debug, Clone, PartialEq)]
pub enum LiteralExpr {
    Int(i64),
    Float(f64),
    String(String),
    Bool(bool),
    VecLiteral(Vec<Typed<Expr>>),
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
