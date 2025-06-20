use crate::ast::{AstNode, AstProgram, Expr, Ident, Stmt, TypedIdent, UnresolvedType};
use crate::error::ResolverError;
use crate::error::ResolverError::{
    DuplicateLambdaParameter, DuplicateParameter, ReturnOutsideFunction, UndefinedFunction, UndefinedType, UndefinedVariable,
    UninitializedVariable,
};

use crate::ir::{DefKind, DefMap, ResolutionMap, ScopeId, ScopeTree};
use miette::Report;
use std::collections::{HashMap, HashSet};
use std::ops::Deref;

#[derive(Debug, Clone, PartialEq)]
pub enum Symbol {
    Variable { initialized: bool },
    Function { params: Vec<TypedIdent>, generics: Vec<Ident> },
    Struct { fields: Vec<TypedIdent> },
}

pub struct ResolverResult<'a> {
    pub errors: &'a Vec<Report>,
    pub resolution_map: &'a ResolutionMap,
    pub def_map: &'a DefMap,
}

pub struct Resolver<'a> {
    source: String,
    program: &'a AstProgram,
    errors: Vec<Report>,
    var_env: Vec<HashMap<String, Symbol>>,
    inside_fn: bool,

    def_map: DefMap,
    resolution_map: ResolutionMap,
    scope_tree: ScopeTree,
    current_scope: ScopeId,
}

impl<'a> Resolver<'a> {
    pub fn new(program: &'a AstProgram, source: String) -> Self {
        let mut var_env = HashMap::new();
        var_env.insert(
            "clock".to_string(),
            Symbol::Function {
                params: vec![],
                generics: vec![],
            },
        );
        var_env.insert(
            "print".to_string(),
            Symbol::Function {
                params: vec![],
                generics: vec![],
            },
        );

        Self {
            source,
            program,
            errors: vec![],
            var_env: vec![var_env],
            inside_fn: false,
            resolution_map: ResolutionMap::new(),
            def_map: DefMap::with_builtins(),
            scope_tree: ScopeTree::with_builtins(),
            current_scope: 0,
        }
    }

    pub fn resolve(&mut self) -> ResolverResult {
        for stmt in &self.program.statements {
            self.declare_stmt(&stmt.node);
        }

        for stmt in &self.program.statements {
            self.resolve_stmt(stmt);
        }

        ResolverResult {
            errors: &self.errors,
            resolution_map: &self.resolution_map,
            def_map: &self.def_map,
        }
    }

    fn resolve_unresolved_type(&mut self, ty: &AstNode<UnresolvedType>) {
        match &ty.node {
            UnresolvedType::Named(ident) => match self.scope_tree.resolve_name(self.current_scope, &ident.node) {
                None => self.report(UndefinedType {
                    src: self.source.clone(),
                    span: ident.span,
                    name: ident.node.clone(),
                }),
                Some(def_id) => {
                    self.resolution_map.insert(ty.node_id, def_id);
                }
            },

            UnresolvedType::Function { params, return_type } => {
                for param in params {
                    self.resolve_unresolved_type(param);
                }
                self.resolve_unresolved_type(return_type);
            }
            UnresolvedType::Generic { base, args } => {
                self.resolve_unresolved_type(base);
                for arg in args {
                    self.resolve_unresolved_type(arg);
                }
            }
        }
    }

    fn report(&mut self, error: ResolverError) {
        self.errors.push(error.into());
    }

    fn lookup_symbol(&self, key: &str) -> Option<&Symbol> {
        for scope in self.var_env.iter().rev() {
            if let Some(symbol) = scope.get(key) {
                return Some(symbol);
            }
        }
        None
    }

    fn curr_scope(&mut self) -> &mut HashMap<String, Symbol> {
        self.var_env.last_mut().unwrap()
    }

    fn enter_scope(&mut self) {
        let new_scope = self.scope_tree.new_scope(self.current_scope);
        self.current_scope = new_scope;
    }

    fn exit_scope(&mut self) {
        self.current_scope = self.scope_tree.scopes[&self.current_scope].parent.unwrap();
    }

    fn declare_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::FunDecl(fun_decl) => {
                let name = &fun_decl.ident.node;

                let function_def_id = self
                    .def_map
                    .insert(name, DefKind::Function, self.current_scope, fun_decl.ident.span, None, vec![]);
                self.scope_tree.insert_symbol(self.current_scope, name, function_def_id);

                if self
                    .curr_scope()
                    .insert(
                        name.clone(),
                        Symbol::Function {
                            params: fun_decl.params.clone(),
                            generics: fun_decl.generics.clone(),
                        },
                    )
                    .is_some()
                {
                    self.report(ResolverError::DuplicateFunction {
                        src: self.source.to_string(),
                        span: fun_decl.ident.span,
                        name: name.clone(),
                    });
                    return;
                }
            }
            Stmt::StructDecl(struct_decl) => {
                let name = &struct_decl.ident.node;

                let struct_def_id = self
                    .def_map
                    .insert(name, DefKind::Struct, self.current_scope, struct_decl.ident.span, None, vec![]);

                self.scope_tree.insert_symbol(self.current_scope, name, struct_def_id);
                if self
                    .curr_scope()
                    .insert(
                        name.clone(),
                        Symbol::Struct {
                            fields: struct_decl.fields.clone(),
                        },
                    )
                    .is_some()
                {
                    self.report(ResolverError::DuplicateStruct {
                        src: self.source.clone(),
                        span: struct_decl.ident.span,
                        name: name.clone(),
                    })
                }
            }
            _ => {}
        }
    }
    fn resolve_stmt(&mut self, stmt: &AstNode<Stmt>) {
        match &stmt.node {
            Stmt::ExprStmtNode(expr_stmt) => self.resolve_expr(&expr_stmt.expr),
            Stmt::VarDecl(var_decl) => {
                let var_def = self.def_map.insert(
                    &var_decl.ident.node,
                    DefKind::Variable,
                    self.current_scope,
                    var_decl.ident.span,
                    None,
                    vec![],
                );
                self.scope_tree.insert_symbol(self.current_scope, &var_decl.ident.node, var_def);

                if let Some(annotation) = &var_decl.type_annotation {
                    self.resolve_unresolved_type(annotation);
                }

                if let Some(init) = &var_decl.initializer {
                    self.resolve_expr(init);
                }

                self.curr_scope().insert(
                    var_decl.ident.node.clone(),
                    Symbol::Variable {
                        initialized: var_decl.initializer.is_some(),
                    },
                );
            }
            Stmt::FunDecl(fun_decl) => {
                let function_def_id = self.def_map.allocate_id();
                self.scope_tree
                    .insert_symbol(self.current_scope, &fun_decl.ident.node, function_def_id);

                self.enter_scope();

                self.curr_scope().insert(
                    fun_decl.ident.node.clone(),
                    Symbol::Function {
                        params: fun_decl.params.clone(),
                        generics: fun_decl.generics.clone(),
                    },
                );

                self.var_env.push(HashMap::new());

                let mut generic_param_ids = vec![];
                for generic_param in &fun_decl.generics {
                    let def_id_t = self.def_map.insert(
                        &generic_param.node,
                        DefKind::TypeParam,
                        self.current_scope,
                        generic_param.span,
                        Some(function_def_id),
                        vec![],
                    );
                    self.scope_tree.insert_symbol(self.current_scope, &generic_param.node, def_id_t);
                    generic_param_ids.push(def_id_t);
                }
                self.def_map.insert(
                    &fun_decl.ident.node,
                    DefKind::Function,
                    self.current_scope,
                    fun_decl.ident.span,
                    None,
                    generic_param_ids,
                );

                let mut seen_params = HashSet::new();

                for param in &fun_decl.params {
                    let param_name = &param.name.node;
                    if !seen_params.insert(param_name.clone()) {
                        self.report(DuplicateParameter {
                            src: self.source.to_string(),
                            span: param.name.span,
                            function_name: fun_decl.ident.node.clone(),
                        });
                        continue;
                    }

                    let param_def_id = self.def_map.insert(
                        param_name,
                        DefKind::Parameter,
                        self.current_scope,
                        param.name.span,
                        Some(function_def_id),
                        vec![],
                    );
                    self.scope_tree.insert_symbol(self.current_scope, &param.name.node, param_def_id);

                    self.resolve_unresolved_type(&param.type_annotation);
                    self.curr_scope()
                        .insert(param.name.node.clone(), Symbol::Variable { initialized: true });
                }

                self.resolve_unresolved_type(&fun_decl.return_type);

                let prev_inside_fn = self.inside_fn;
                self.inside_fn = true;
                for stmt in &fun_decl.body.node.statements {
                    self.resolve_stmt(stmt);
                }
                self.inside_fn = prev_inside_fn;
                self.var_env.pop();
                self.exit_scope();
            }
            Stmt::StructDecl(struct_decl) => {
                let name = struct_decl.ident.node.clone();
                self.curr_scope().insert(
                    name.clone(),
                    Symbol::Struct {
                        fields: struct_decl.fields.clone(),
                    },
                );

                for field in &struct_decl.fields {
                    self.resolve_unresolved_type(&field.type_annotation);
                }
            }
            Stmt::While(while_stmt) => {
                self.resolve_expr(&while_stmt.condition);
                self.resolve_stmts(&while_stmt.body.node.statements);
            }
            Stmt::For(for_stmt) => {
                if let Some(init) = &for_stmt.initializer {
                    self.resolve_stmt(init);
                }
                self.resolve_expr(&for_stmt.condition);

                if let Some(incr) = &for_stmt.increment {
                    self.resolve_expr(incr);
                }
                self.resolve_stmts(&for_stmt.body.node.statements);
            }
            Stmt::Return(return_stmt) => {
                if !self.inside_fn {
                    self.report(ReturnOutsideFunction {
                        src: self.source.clone(),
                        span: stmt.span,
                    });
                } else if let Some(return_expr) = &return_stmt.expr {
                    self.resolve_expr(return_expr);
                }
            }
        }
    }

    fn resolve_stmts(&mut self, stmts: &Vec<AstNode<Stmt>>) {
        self.var_env.push(HashMap::new());
        for stmt in stmts {
            self.resolve_stmt(stmt);
        }
        self.var_env.pop();
    }

    fn resolve_expr(&mut self, expr: &AstNode<Expr>) {
        match &expr.node {
            Expr::FieldAssign(field_assign) => {
                self.resolve_expr(&field_assign.receiver);
                self.resolve_expr(&field_assign.value);
            }
            Expr::FieldAccess(field_access) => {
                self.resolve_expr(&field_access.receiver);
            }
            Expr::StructInit(struct_init) => match self.lookup_symbol(&struct_init.name.node).cloned() {
                None => {
                    self.report(UndefinedVariable {
                        src: self.source.clone(),
                        span: struct_init.name.span,
                        name: struct_init.name.node.clone(),
                    });
                }
                Some(Symbol::Struct { fields: _ }) => {
                    for (_, value) in &struct_init.fields {
                        self.resolve_expr(value);
                    }
                }
                Some(_) => {
                    self.report(ResolverError::NotAStruct {
                        src: self.source.clone(),
                        span: struct_init.name.span,
                        name: struct_init.name.node.clone(),
                    });
                }
            },
            Expr::Literal(_) => {}
            Expr::Block(block) => {
                self.var_env.push(HashMap::new());
                for stmt in &block.statements {
                    self.resolve_stmt(stmt);
                }
                if let Some(expr) = &block.expr {
                    self.resolve_expr(expr)
                }

                self.var_env.pop();
            }
            Expr::If(if_expr) => {
                self.resolve_expr(&if_expr.condition);
                self.resolve_stmts(&if_expr.then_branch.node.statements);
                if let Some(else_branch) = &if_expr.else_branch {
                    self.resolve_stmts(&else_branch.node.statements);
                }
            }
            Expr::MethodCall(method_call) => {
                self.resolve_expr(&method_call.receiver);

                for arg in &method_call.arguments {
                    self.resolve_expr(arg);
                }
            }
            Expr::Unary(unary_expr) => {
                self.resolve_expr(unary_expr.expr.deref());
            }
            Expr::Binary(binary_expr) => {
                self.resolve_expr(binary_expr.left.deref());
                self.resolve_expr(binary_expr.right.deref());
            }
            Expr::Grouping(grouping) => {
                self.resolve_expr(grouping.deref());
            }
            Expr::Variable(variable_expr) => match self.lookup_symbol(variable_expr.node.as_str()) {
                Some(Symbol::Variable { initialized: false }) => self.report(UninitializedVariable {
                    src: self.source.clone(),
                    span: variable_expr.span,
                    name: variable_expr.node.clone(),
                }),
                None => self.report(UndefinedVariable {
                    src: self.source.clone(),
                    span: variable_expr.span,
                    name: variable_expr.node.clone(),
                }),
                _ => {}
            },
            Expr::Assign(assign) => {
                match self.lookup_symbol(assign.target.node.as_str()) {
                    None => self.report(UndefinedVariable {
                        src: self.source.clone(),
                        span: assign.target.span,
                        name: assign.target.node.clone(),
                    }),
                    Some(_) => {
                        for scope in self.var_env.iter_mut().rev() {
                            if let Some(symbol) = scope.get_mut(&assign.target.node) {
                                *symbol = Symbol::Variable { initialized: true };
                                break;
                            }
                        }
                    }
                }

                self.resolve_expr(&assign.value);
            }
            Expr::Logical(logical_expr) => {
                self.resolve_expr(logical_expr.left.deref());
                self.resolve_expr(logical_expr.right.deref());
            }
            Expr::Call(call) => {
                if let Expr::Variable(ident) = &call.callee.deref().node {
                    if self.lookup_symbol(&ident.node).is_none() {
                        self.report(UndefinedFunction {
                            src: self.source.clone(),
                            span: ident.span,
                            name: ident.node.clone(),
                        })
                    }
                }
                for argument in &call.arguments {
                    self.resolve_expr(argument);
                }
            }
            Expr::Lambda(lambda) => {
                self.var_env.push(HashMap::new());
                for param in &lambda.parameters {
                    if self.curr_scope().get(param.name.node.as_str()).is_some() {
                        self.report(DuplicateLambdaParameter {
                            src: self.source.to_string(),
                            span: param.name.span,
                        })
                    } else {
                        self.curr_scope()
                            .insert(param.name.node.clone(), Symbol::Variable { initialized: true });
                    }
                }

                let prev_inside_fn = self.inside_fn;
                self.inside_fn = true;
                for stmt in &lambda.body.node.statements {
                    self.resolve_stmt(stmt);
                }
                self.inside_fn = prev_inside_fn;
                self.var_env.pop();
            }
        }
    }
}
