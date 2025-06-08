use crate::TokenKind;
use miette::SourceSpan;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AstNode<T> {
    pub node: T,
    pub span: SourceSpan,
    pub node_id: usize,
}

impl<T> AstNode<T> {
    pub fn new(node: T, span: SourceSpan) -> Self {
        static mut NODE_ID: usize = 1;

        let node_id = unsafe {
            let id = NODE_ID;
            NODE_ID += 1;
            id
        };

        Self { node, span, node_id }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum UnresolvedType {
    /// Int, Bool, User, T
    Named(Ident),

    /// (Int, Bool) -> Bool
    Function {
        params: Vec<UnresolvedType>,
        return_type: Box<UnresolvedType>,
    },

    /// Option<T>, Vec<Int>, Result<A, B>
    Generic {
        base: Box<UnresolvedType>,
        args: Vec<UnresolvedType>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct Program {
    pub statements: Vec<AstNode<Stmt>>,
    pub span: SourceSpan,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    ExprStmtNode(ExprStmt),
    VarDecl(VarDeclStmt),
    FunDecl(FunDeclStmt),
    StructDecl(StructDeclStmt),
    While(WhileStmt),
    For(ForStmt),
    Return(ReturnStmt),
}

pub type Ident = AstNode<String>;

#[derive(Debug, Clone, PartialEq)]
pub struct ExprStmt {
    pub expr: AstNode<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct VarDeclStmt {
    pub ident: Ident,
    pub initializer: Option<AstNode<Expr>>,
    pub type_annotation: Option<AstNode<UnresolvedType>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedIdent {
    pub name: Ident,
    pub type_annotation: AstNode<UnresolvedType>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunDeclStmt {
    pub name: Ident,
    pub params: Vec<TypedIdent>,
    pub body: AstNode<BlockExpr>,
    pub generics: Vec<Ident>,
    pub return_type: AstNode<UnresolvedType>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StructDeclStmt {
    pub ident: Ident,
    pub fields: Vec<TypedIdent>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct WhileStmt {
    pub condition: AstNode<Expr>,
    pub body: AstNode<BlockExpr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ForStmt {
    pub initializer: Option<Box<AstNode<Stmt>>>,
    pub condition: AstNode<Expr>,
    pub increment: Option<AstNode<Expr>>,
    pub body: AstNode<BlockExpr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ReturnStmt {
    pub expr: Option<AstNode<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Literal(LiteralExpr),
    Unary(UnaryExpr),
    Binary(BinaryExpr),
    Grouping(Box<AstNode<Expr>>),
    Variable(Ident),
    Assign(AssignExpr),
    Logical(LogicalExpr),
    Call(CallExpr),
    Lambda(LambdaExpr),
    Block(BlockExpr),
    If(IfExpr),
    MethodCall(MethodCallExpr),
    StructInit(StructInitExpr),
    FieldAccess(FieldAccessExpr),
    FieldAssign(FieldAssignExpr),
}

#[derive(Debug, Clone, PartialEq)]
pub struct UnaryExpr {
    pub op: AstNode<UnaryOp>,
    pub expr: Box<AstNode<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BinaryExpr {
    pub left: Box<AstNode<Expr>>,
    pub op: AstNode<BinaryOp>,
    pub right: Box<AstNode<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LogicalExpr {
    pub left: Box<AstNode<Expr>>,
    pub op: AstNode<LogicalOp>,
    pub right: Box<AstNode<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct AssignExpr {
    pub target: Ident,
    pub value: Box<AstNode<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CallExpr {
    pub callee: Box<AstNode<Expr>>,
    pub arguments: Vec<AstNode<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LambdaExpr {
    pub parameters: Vec<TypedIdent>,
    pub body: Box<AstNode<BlockExpr>>,
    pub return_type: AstNode<UnresolvedType>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BlockExpr {
    pub statements: Vec<AstNode<Stmt>>,
    pub expr: Option<Box<AstNode<Expr>>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct IfExpr {
    pub condition: Box<AstNode<Expr>>,
    pub then_branch: AstNode<BlockExpr>,
    pub else_branch: Option<AstNode<BlockExpr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MethodCallExpr {
    pub receiver: Box<AstNode<Expr>>,
    pub method: Ident,
    pub arguments: Vec<AstNode<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StructInitExpr {
    pub name: Ident,
    pub fields: Vec<(Ident, AstNode<Expr>)>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FieldAccessExpr {
    pub receiver: Box<AstNode<Expr>>,
    pub field: Ident,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FieldAssignExpr {
    pub receiver: Box<AstNode<Expr>>,
    pub field: Ident,
    pub value: Box<AstNode<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LiteralExpr {
    Int(i64),
    Float(f64),
    String(String),
    Bool(bool),
    VecLiteral(Vec<AstNode<Expr>>),
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
