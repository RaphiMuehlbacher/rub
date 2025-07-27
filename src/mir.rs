use crate::hir;
use crate::hir::DefId;
use crate::type_inferrer::Type;
use miette::SourceSpan;

pub type MirId = usize;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MirNode<T> {
    pub node: T,
    pub span: SourceSpan,
    pub mir_id: MirId,
}

impl<T> MirNode<T> {
    pub fn new(node: T, span: SourceSpan) -> Self {
        static mut MIR_ID: usize = 1;

        let node_id = unsafe {
            let id = MIR_ID;
            MIR_ID += 1;
            id
        };

        Self {
            node,
            span,
            mir_id: node_id,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct MirProgram {
    pub statements: Vec<MirNode<Stmt>>,
    pub span: SourceSpan,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    ExprStmtNode(ExprStmt),
    VarDecl(VarDeclStmt),
    FunDecl(FunDeclStmt),
    StructDecl(StructDeclStmt),
    While(WhileStmt),
    Return(ReturnStmt),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Ident {
    pub name: MirNode<String>,
    pub def_id: DefId,
}

impl Ident {
    pub fn new(name: &str, span: SourceSpan, def_id: DefId) -> Self {
        Self {
            name: MirNode::new(name.to_string(), span),
            def_id,
        }
    }

    pub fn from_ir(ident: &hir::Ident) -> Self {
        Ident::new(&ident.name.node, ident.name.span, ident.def_id)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ExprStmt {
    pub expr: MirNode<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct VarDeclStmt {
    pub ident: Ident,
    pub initializer: Option<MirNode<Expr>>,
    pub type_annotation: Option<Type>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedIdent {
    pub name: Ident,
    pub type_annotation: Type,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunDeclStmt {
    pub ident: Ident,
    pub params: Vec<TypedIdent>,
    pub generics: Vec<Ident>,
    pub return_type: Type,
    pub body: MirNode<BlockExpr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StructDeclStmt {
    pub ident: Ident,
    pub fields: Vec<TypedIdent>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct WhileStmt {
    pub condition: MirNode<Expr>,
    pub body: MirNode<BlockExpr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ReturnStmt {
    pub expr: Option<MirNode<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Literal(LiteralExpr),
    Unary(UnaryExpr),
    Binary(BinaryExpr),
    Grouping(Box<MirNode<Expr>>),
    Variable(Ident),
    Assign(AssignExpr),
    Logical(LogicalExpr),
    Call(CallExpr),
    Lambda(LambdaExpr),
    Block(BlockExpr),
    If(IfExpr),
    StructInit(StructInitExpr),
    FieldAccess(FieldAccessExpr),
    FieldAssign(FieldAssignExpr),
}

#[derive(Debug, Clone, PartialEq)]
pub struct UnaryExpr {
    pub op: MirNode<UnaryOp>,
    pub expr: Box<MirNode<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BinaryExpr {
    pub left: Box<MirNode<Expr>>,
    pub op: MirNode<BinaryOp>,
    pub right: Box<MirNode<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LogicalExpr {
    pub left: Box<MirNode<Expr>>,
    pub op: MirNode<LogicalOp>,
    pub right: Box<MirNode<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct AssignExpr {
    pub target: Ident,
    pub value: Box<MirNode<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CallExpr {
    pub callee: Box<MirNode<Expr>>,
    pub arguments: Vec<MirNode<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LambdaExpr {
    pub parameters: Vec<TypedIdent>,
    pub body: Box<MirNode<BlockExpr>>,
    pub return_type: Type,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BlockExpr {
    pub statements: Vec<MirNode<Stmt>>,
    pub expr: Option<Box<MirNode<Expr>>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct IfExpr {
    pub condition: Box<MirNode<Expr>>,
    pub then_branch: MirNode<BlockExpr>,
    pub else_branch: Option<MirNode<BlockExpr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StructInitExpr {
    pub name: Ident,
    pub fields: Vec<(Ident, MirNode<Expr>)>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FieldAccessExpr {
    pub receiver: Box<MirNode<Expr>>,
    pub field: MirNode<String>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FieldAssignExpr {
    pub receiver: Box<MirNode<Expr>>,
    pub field: MirNode<String>,
    pub value: Box<MirNode<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LiteralExpr {
    Int(i64),
    Float(f64),
    String(String),
    Bool(bool),
    VecLiteral(Vec<MirNode<Expr>>),
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
