use crate::ast;
use crate::ast::AstId;
use miette::SourceSpan;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub enum Definition {
    Struct {
        def_id: DefId,
        name: String,
        scope: ScopeId,
        span: SourceSpan,
        type_params: Vec<DefId>, // TypeParam
        fields: Vec<DefId>,      // Field
    },
    Field {
        def_id: DefId,
        name: String,
        scope: ScopeId,
        span: SourceSpan,
    },
    Function {
        def_id: DefId,
        name: String,
        scope: ScopeId,
        span: SourceSpan,
        type_params: Vec<DefId>, // TypeParam
        params: Vec<DefId>,      // Param
    },
    Param {
        def_id: DefId,
        name: String,
        scope: ScopeId,
        span: SourceSpan,
    },
    NativeParam {
        def_id: DefId,
        name: String,
    },
    TypeParam {
        def_id: DefId,
        name: String,
        scope: ScopeId,
        span: SourceSpan,
    },
    Variable {
        def_id: DefId,
        name: String,
        scope: ScopeId,
        span: SourceSpan,
    },
    Builtin {
        def_id: DefId,
        name: String,
        type_params: Vec<DefId>,
    },
    NativeFunction {
        def_id: DefId,
        name: String,
        native_params: Vec<DefId>, // NativeParam
    },
}

impl Definition {
    pub fn span(&self) -> SourceSpan {
        match self {
            Definition::Struct { span, .. } => *span,
            Definition::Field { span, .. } => *span,
            Definition::Function { span, .. } => *span,
            Definition::Param { span, .. } => *span,
            Definition::TypeParam { span, .. } => *span,
            Definition::Variable { span, .. } => *span,
            _ => panic!(),
        }
    }

    pub fn name(&self) -> &str {
        match self {
            Definition::Struct { name, .. } => name,
            Definition::Field { name, .. } => name,
            Definition::Function { name, .. } => name,
            Definition::Param { name, .. } => name,
            Definition::TypeParam { name, .. } => name,
            Definition::Variable { name, .. } => name,
            Definition::NativeFunction { name, .. } => name,
            Definition::Builtin { name, .. } => name,
            Definition::NativeParam { name, .. } => name,
        }
    }

    pub fn def_id(&self) -> DefId {
        match self {
            Definition::Struct { def_id, .. } => *def_id,
            Definition::Field { def_id, .. } => *def_id,
            Definition::Function { def_id, .. } => *def_id,
            Definition::Param { def_id, .. } => *def_id,
            Definition::TypeParam { def_id, .. } => *def_id,
            Definition::Variable { def_id, .. } => *def_id,
            Definition::NativeFunction { def_id, .. } => *def_id,
            Definition::Builtin { def_id, .. } => *def_id,
            Definition::NativeParam { def_id, .. } => *def_id,
        }
    }

    pub fn scope(&self) -> ScopeId {
        match self {
            Definition::Struct { scope, .. } => *scope,
            Definition::Field { scope, .. } => *scope,
            Definition::Function { scope, .. } => *scope,
            Definition::Param { scope, .. } => *scope,
            Definition::TypeParam { scope, .. } => *scope,
            Definition::Variable { scope, .. } => *scope,
            _ => panic!(),
        }
    }

    pub fn fields(&self) -> &Vec<DefId> {
        match self {
            Definition::Struct { fields, .. } => fields,
            _ => panic!(),
        }
    }
    pub fn params(&self) -> &Vec<DefId> {
        match self {
            Definition::Function { params, .. } => params,
            _ => panic!(),
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
            next_def_id: 0,
            defs: HashMap::new(),
        }
    }

    pub fn with_builtins() -> Self {
        let mut def_map = DefMap::new();

        def_map.insert_builtin("Int", vec![]);
        def_map.insert_builtin("Float", vec![]);
        def_map.insert_builtin("String", vec![]);
        def_map.insert_builtin("Bool", vec![]);
        def_map.insert_builtin("Nil", vec![]);

        def_map.insert_builtin("Vec", vec!["T"]);

        def_map.insert_native_function("clock", vec![]);
        def_map.insert_native_function("print", vec!["T"]);
        def_map.insert_native_function("len", vec!["T"]);
        def_map.insert_native_function("sum", vec!["T"]);
        def_map.insert_native_function("first", vec!["T"]);

        def_map
    }

    pub fn insert_native_function(&mut self, name: &str, native_params: Vec<&str>) -> DefId {
        let native_param_ids = native_params.iter().map(|p| self.insert_native_param(p)).collect();

        let def_id = self.allocate_id();
        self.defs.insert(
            def_id,
            Definition::NativeFunction {
                def_id,
                name: name.to_string(),
                native_params: native_param_ids,
            },
        );

        def_id
    }

    pub fn insert_native_param(&mut self, name: &str) -> DefId {
        let def_id = self.allocate_id();
        self.defs.insert(
            def_id,
            Definition::NativeParam {
                def_id,
                name: name.to_string(),
            },
        );
        def_id
    }

    pub fn insert_builtin(&mut self, name: &str, type_params: Vec<&str>) -> DefId {
        let type_param_ids = type_params
            .iter()
            .map(|p| self.insert_type_param((p, 0, SourceSpan::from(0))))
            .collect();

        let def_id = self.allocate_id();
        self.defs.insert(
            def_id,
            Definition::Builtin {
                def_id,
                name: name.to_string(),
                type_params: type_param_ids,
            },
        );
        def_id
    }

    pub fn insert_variable(&mut self, name: &str, scope: ScopeId, span: SourceSpan) -> DefId {
        let def_id = self.allocate_id();
        self.defs.insert(
            def_id,
            Definition::Variable {
                def_id,
                name: name.to_string(),
                scope,
                span,
            },
        );
        def_id
    }

    pub fn insert_place_holder_struct(&mut self, name: &str, scope: ScopeId, span: SourceSpan) -> DefId {
        self.insert_struct(name, scope, span, vec![], vec![])
    }

    pub fn complete_struct(&mut self, def_id: DefId, fields: Vec<DefId>, type_params: Vec<DefId>) {
        let def = self.defs.get_mut(&def_id).unwrap();
        match def {
            Definition::Struct {
                type_params: old_type_params,
                fields: old_fields,
                ..
            } => {
                *old_type_params = type_params;
                *old_fields = fields;
            }
            _ => panic!(),
        }
    }

    pub fn insert_struct(
        &mut self,
        name: &str,
        scope: ScopeId,
        span: SourceSpan,
        type_params: Vec<(&str, ScopeId, SourceSpan)>,
        fields: Vec<(&str, ScopeId, SourceSpan)>,
    ) -> DefId {
        let type_param_ids = type_params.into_iter().map(|p| self.insert_type_param(p)).collect();
        let field_ids = fields.into_iter().map(|f| self.insert_field(f)).collect();

        let def_id = self.allocate_id();
        self.defs.insert(
            def_id,
            Definition::Struct {
                def_id,
                name: name.to_string(),
                scope,
                span,
                type_params: type_param_ids,
                fields: field_ids,
            },
        );
        def_id
    }
    pub fn insert_placeholder_function(&mut self, name: &str, scope: ScopeId, span: SourceSpan) -> DefId {
        self.insert_function(name, scope, span, vec![], vec![])
    }

    pub fn complete_function(&mut self, def_id: DefId, params: Vec<DefId>, type_params: Vec<DefId>) {
        let def = self.defs.get_mut(&def_id).unwrap();
        match def {
            Definition::Function {
                type_params: old_type_params,
                params: old_params,
                ..
            } => {
                *old_type_params = type_params;
                *old_params = params;
            }
            _ => panic!(),
        }
    }

    pub fn insert_function(
        &mut self,
        name: &str,
        scope: ScopeId,
        span: SourceSpan,
        params: Vec<(&str, ScopeId, SourceSpan)>,
        type_params: Vec<(&str, ScopeId, SourceSpan)>,
    ) -> DefId {
        let type_param_ids = type_params.into_iter().map(|p| self.insert_type_param(p)).collect();
        let param_ids = params.into_iter().map(|p| self.insert_param(p)).collect();

        let def_id = self.allocate_id();
        self.defs.insert(
            def_id,
            Definition::Function {
                def_id,
                name: name.to_string(),
                scope,
                span,
                type_params: type_param_ids,
                params: param_ids,
            },
        );
        def_id
    }

    pub fn insert_field(&mut self, field: (&str, ScopeId, SourceSpan)) -> DefId {
        let def_id = self.allocate_id();
        self.defs.insert(
            def_id,
            Definition::Field {
                def_id,
                name: field.0.to_string(),
                scope: field.1,
                span: field.2,
            },
        );
        def_id
    }
    pub fn insert_param(&mut self, param: (&str, ScopeId, SourceSpan)) -> DefId {
        let def_id = self.allocate_id();
        self.defs.insert(
            def_id,
            Definition::Param {
                def_id,
                name: param.0.to_string(),
                scope: param.1,
                span: param.2,
            },
        );
        def_id
    }

    pub fn insert_type_param(&mut self, type_param: (&str, ScopeId, SourceSpan)) -> DefId {
        let def_id = self.allocate_id();
        self.defs.insert(
            def_id,
            Definition::TypeParam {
                def_id,
                name: type_param.0.to_string(),
                scope: type_param.1,
                span: type_param.2,
            },
        );
        def_id
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
        symbols.insert("Vec".to_string(), 6);
        symbols.insert("clock".to_string(), 7);
        symbols.insert("print".to_string(), 9);
        symbols.insert("len".to_string(), 11);
        symbols.insert("sum".to_string(), 13);
        symbols.insert("first".to_string(), 15);

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

    pub fn from_ast(ident: &ast::AstNode<String>, scope_tree: &ScopeTree, current_scope: ScopeId) -> Self {
        Ident::new(
            &ident.node,
            ident.span,
            scope_tree.resolve_name(current_scope, &ident.node).unwrap(),
        )
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
    pub generics: Vec<Ident>,
    pub return_type: ResolvedType,
    pub body: IrNode<BlockExpr>,
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
    pub field: IrNode<String>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FieldAssignExpr {
    pub receiver: Box<IrNode<Expr>>,
    pub field: IrNode<String>,
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
