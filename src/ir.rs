use miette::SourceSpan;

pub type TypeVarId = usize;

#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub enum ResolvedType {
    Int,
    Float,
    Bool,
    String,
    Nil,
    Function {
        params: Vec<ResolvedType>,
        return_ty: Box<ResolvedType>,
    },
    Struct {
        name: String,
        fields: Vec<(String, ResolvedType)>,
    },
    Vec(Box<ResolvedType>),
    TypeVar(TypeVarId),
    Generic(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IrNode<T> {
    pub node: T,
    pub span: SourceSpan,
    pub ir_id: usize,
}

impl<T> IrNode<T> {
    pub fn new(node: T, span: SourceSpan) -> Self {
        static mut IR_ID: usize = 1;

        let node_id = unsafe {
            let id = IR_ID;
            IR_ID += 1;
            id
        };

        Self {
            node,
            span,
            ir_id: node_id,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Program {
    pub statements: Vec<IrNode<Stmt>>,
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

pub type Ident = IrNode<String>;

#[derive(Debug, Clone, PartialEq)]
pub struct ExprStmt {
    pub expr: IrNode<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct VarDeclStmt {
    pub ident: Ident,
    pub initializer: Option<IrNode<Expr>>,
    pub type_annotation: Option<IrNode<ResolvedType>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedIdent {
    pub name: Ident,
    pub type_annotation: IrNode<ResolvedType>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunDeclStmt {
    pub ident: Ident,
    pub params: Vec<TypedIdent>,
    pub body: IrNode<BlockExpr>,
    pub generics: Vec<Ident>,
    pub return_type: IrNode<ResolvedType>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StructDeclStmt {
    pub ident: Ident,
    pub fields: Vec<TypedIdent>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct WhileStmt {
    pub condition: IrNode<Expr>,
    pub body: IrNode<BlockExpr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ReturnStmt {
    pub expr: Option<IrNode<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Literal(LiteralExpr),
    Unary(UnaryExpr),
    Binary(BinaryExpr),
    Grouping(Box<IrNode<Expr>>),
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
    pub op: IrNode<UnaryOp>,
    pub expr: Box<IrNode<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BinaryExpr {
    pub left: Box<IrNode<Expr>>,
    pub op: IrNode<BinaryOp>,
    pub right: Box<IrNode<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LogicalExpr {
    pub left: Box<IrNode<Expr>>,
    pub op: IrNode<LogicalOp>,
    pub right: Box<IrNode<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct AssignExpr {
    pub target: Ident,
    pub value: Box<IrNode<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CallExpr {
    pub callee: Box<IrNode<Expr>>,
    pub arguments: Vec<IrNode<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LambdaExpr {
    pub parameters: Vec<TypedIdent>,
    pub body: Box<IrNode<BlockExpr>>,
    pub return_type: IrNode<ResolvedType>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BlockExpr {
    pub statements: Vec<IrNode<Stmt>>,
    pub expr: Option<Box<IrNode<Expr>>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct IfExpr {
    pub condition: Box<IrNode<Expr>>,
    pub then_branch: IrNode<BlockExpr>,
    pub else_branch: Option<IrNode<BlockExpr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MethodCallExpr {
    pub receiver: Box<IrNode<Expr>>,
    pub method: Ident,
    pub arguments: Vec<IrNode<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StructInitExpr {
    pub name: Ident,
    pub fields: Vec<(Ident, IrNode<Expr>)>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FieldAccessExpr {
    pub receiver: Box<IrNode<Expr>>,
    pub field: Ident,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FieldAssignExpr {
    pub receiver: Box<IrNode<Expr>>,
    pub field: Ident,
    pub value: Box<IrNode<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LiteralExpr {
    Int(i64),
    Float(f64),
    String(String),
    Bool(bool),
    VecLiteral(Vec<IrNode<Expr>>),
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
