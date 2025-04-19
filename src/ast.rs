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

pub trait StmtVisitor {
    fn visit_program(&mut self, program: &Program);
    fn visit_stmt(&mut self, stmt: &Stmt);
}

pub trait ExprVisitor {
    type Output;
    fn visit_expr(&mut self, expr: &Expr) -> Self::Output;
}

pub trait Accept<V: ?Sized> {
    type Output;
    fn accept(&self, visitor: &mut V) -> Self::Output;
}

#[derive(Debug, Clone, PartialEq)]
pub struct Program {
    pub statements: Vec<Stmt>,
    pub span: SourceSpan,
}

impl<V: StmtVisitor> Accept<V> for Program {
    type Output = ();
    fn accept(&self, visitor: &mut V) -> Self::Output {
        visitor.visit_program(self)
    }
}

impl<V: StmtVisitor> Accept<V> for Stmt {
    type Output = ();
    fn accept(&self, visitor: &mut V) -> Self::Output {
        visitor.visit_stmt(self)
    }
}

impl<V: ExprVisitor> Accept<V> for Expr {
    type Output = V::Output;
    fn accept(&self, visitor: &mut V) -> Self::Output {
        visitor.visit_expr(self)
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

pub type Ident = Typed<String>;

#[derive(Debug, Clone, PartialEq)]
pub struct VarDeclStmt {
    pub ident: Typed<String>,
    pub initializer: Option<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunDeclStmt {
    pub ident: Typed<String>,
    pub params: Vec<Typed<String>>,
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
    Variable(Typed<String>),
    Assign(Typed<AssignExpr>),
    Logical(Typed<LogicalExpr>),
    Call(Typed<CallExpr>),
    Lambda(Typed<LambdaExpr>),
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
    pub target: Typed<String>,
    pub value: Box<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CallExpr {
    pub callee: Box<Expr>,
    pub arguments: Vec<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LambdaExpr {
    pub parameters: Vec<Typed<String>>,
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
