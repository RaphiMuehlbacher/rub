use crate::ast;
use crate::ast::AstId;
use miette::SourceSpan;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub enum DefKind {
    Struct,
    Function,
    Parameter,
    Field,
    Variable,
    TypeParam,
    Builtin,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Definition {
    pub id: DefId,
    pub name: String,
    pub kind: DefKind,
    pub scope: ScopeId,
    pub span: SourceSpan,
    pub type_params: Vec<DefId>,
    pub parent: Option<DefId>,
}

impl Definition {
    pub fn builtin(id: DefId, name: &str, type_params: Vec<DefId>) -> Self {
        Self {
            id,
            name: name.to_string(),
            kind: DefKind::Builtin,
            scope: 0,
            span: SourceSpan::from(0),
            type_params,
            parent: None,
        }
    }
}

pub type ScopeId = usize;
pub type DefId = usize;

#[derive(Debug, Clone, PartialEq)]
pub struct DefMap {
    pub next_def_id: DefId,
    pub defs: HashMap<DefId, Definition>,
}

impl DefMap {
    pub fn new() -> Self {
        Self {
            next_def_id: 1,
            defs: HashMap::new(),
        }
    }
    pub fn with_builtins() -> Self {
        let mut defs = HashMap::new();
        defs.insert(0, Definition::builtin(0, "Int", vec![]));
        defs.insert(1, Definition::builtin(1, "Float", vec![]));
        defs.insert(2, Definition::builtin(2, "String", vec![]));
        defs.insert(3, Definition::builtin(3, "Bool", vec![]));
        defs.insert(4, Definition::builtin(4, "Nil", vec![]));
        let def_vec_id = 5;
        let def_t_id = 6;
        defs.insert(
            def_t_id,
            Definition {
                id: def_t_id,
                name: "T".to_string(),
                parent: Some(def_vec_id),
                kind: DefKind::TypeParam,
                scope: 0,
                span: SourceSpan::from(0),
                type_params: vec![],
            },
        );
        defs.insert(def_vec_id, Definition::builtin(5, "Vec", vec![def_t_id]));

        Self { next_def_id: 6, defs }
    }

    pub fn insert_with_id(
        &mut self,
        id: DefId,
        name: &str,
        kind: DefKind,
        scope: ScopeId,
        span: SourceSpan,
        parent: Option<DefId>,
        type_params: Vec<DefId>,
    ) {
        let def = Definition {
            id,
            name: name.to_string(),
            kind,
            scope,
            span,
            parent,
            type_params,
        };
        self.defs.insert(id, def);
    }
    pub fn insert(
        &mut self,
        name: &str,
        kind: DefKind,
        scope: ScopeId,
        span: SourceSpan,
        parent: Option<DefId>,
        type_params: Vec<DefId>,
    ) -> DefId {
        let id = self.next_def_id;
        self.next_def_id += 1;
        let def = Definition {
            id,
            name: name.to_string(),
            kind,
            scope,
            span,
            parent,
            type_params,
        };
        self.defs.insert(id, def);
        self.name_to_def.insert((scope, name.to_string()), id);
        id
    }

    pub fn allocate_id(&mut self) -> DefId {
        let id = self.next_def_id;
        self.next_def_id += 1;
        id
    }

    pub fn get(&self, id: DefId) -> Option<&Definition> {
        self.defs.get(&id)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Scope {
    pub id: ScopeId,
    pub parent: Option<ScopeId>,
    pub symbols: HashMap<String, DefId>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ScopeTree {
    pub scopes: HashMap<ScopeId, Scope>,
    next_id: ScopeId,
}

impl ScopeTree {
    pub fn new() -> Self {
        Self {
            scopes: HashMap::new(),
            next_id: 1,
        }
    }

    pub fn with_builtins() -> Self {
        let mut scopes = HashMap::new();
        let mut symbols = HashMap::new();

        symbols.insert("Int".to_string(), 0);
        symbols.insert("Float".to_string(), 1);
        symbols.insert("String".to_string(), 2);
        symbols.insert("Bool".to_string(), 3);
        symbols.insert("Nil".to_string(), 4);
        symbols.insert("Vec".to_string(), 5);

        let global_scope = Scope {
            id: 0,
            parent: None,
            symbols,
        };
        scopes.insert(0, global_scope);

        Self { next_id: 1, scopes }
    }

    pub fn new_scope(&mut self, parent: ScopeId) -> ScopeId {
        let id = self.next_id;
        self.next_id += 1;
        self.scopes.insert(
            id,
            Scope {
                id,
                parent: Some(parent),
                symbols: HashMap::new(),
            },
        );
        id
    }

    pub fn insert_symbol(&mut self, scope_id: ScopeId, name: &str, def_id: DefId) {
        if let Some(scope) = self.scopes.get_mut(&scope_id) {
            scope.symbols.insert(name.to_string(), def_id);
        }
    }

    pub fn resolve_name(&self, start_scope: ScopeId, name: &str) -> Option<DefId> {
        let mut current = Some(start_scope);
        while let Some(scope_id) = current {
            if let Some(scope) = self.scopes.get(&scope_id) {
                if let Some(def_id) = scope.symbols.get(name) {
                    return Some(*def_id);
                }
                current = scope.parent
            } else {
                break;
            }
        }
        None
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ResolutionMap {
    resolutions: HashMap<AstId, DefId>,
}

impl ResolutionMap {
    pub fn new() -> Self {
        Self {
            resolutions: HashMap::new(),
        }
    }

    pub fn insert(&mut self, node_id: AstId, def_id: DefId) {
        self.resolutions.insert(node_id, def_id);
    }

    pub fn get(&self, node_id: AstId) -> DefId {
        *self.resolutions.get(&node_id).unwrap()
    }
}

pub type IrId = usize;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IrNode<T> {
    pub node: T,
    pub span: SourceSpan,
    pub ir_id: IrId,
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
pub enum ResolvedType {
    Named(DefId),
    Function {
        params: Vec<ResolvedType>,
        return_type: Box<ResolvedType>,
    },
    Generic {
        base: DefId,
        args: Vec<ResolvedType>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct IrProgram {
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

#[derive(Debug, Clone, PartialEq)]
pub struct Ident {
    pub name: IrNode<String>,
    pub def_id: DefId,
}

impl Ident {
    pub fn new(name: &str, span: SourceSpan, def_id: DefId) -> Self {
        Self {
            name: IrNode::new(name.to_string(), span),
            def_id,
        }
    }

    pub fn from_ast(ident: &ast::AstNode<String>, resolution_map: &ResolutionMap) -> Self {
        Ident::new(&ident.node, ident.span, resolution_map.get(ident.node_id))
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ExprStmt {
    pub expr: IrNode<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct VarDeclStmt {
    pub ident: Ident,
    pub initializer: Option<IrNode<Expr>>,
    pub type_annotation: Option<ResolvedType>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedIdent {
    pub name: Ident,
    pub type_annotation: ResolvedType,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunDeclStmt {
    pub ident: Ident,
    pub params: Vec<TypedIdent>,
    pub body: IrNode<BlockExpr>,
    pub generics: Vec<Ident>,
    pub return_type: ResolvedType,
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
    pub return_type: ResolvedType,
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
