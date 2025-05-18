use crate::ast::{Expr, ExprStmt, FunDeclStmt, Parameter, Program, ReturnStmt, Stmt, Typed, VarDeclStmt, WhileStmt};
use crate::error::ResolverError;
use crate::error::ResolverError::{
    DuplicateLambdaParameter, DuplicateParameter, UndefinedFunction, UndefinedVariable, UninitializedVariable,
};
use miette::Report;
use std::collections::HashMap;
use std::ops::Deref;

#[derive(Debug, Clone, PartialEq)]
pub enum Symbol {
    Variable { initialized: bool },
    Function { params: Vec<Typed<Parameter>> },
}

pub struct Resolver<'a> {
    source: String,
    program: &'a Program,
    errors: Vec<Report>,
    scopes: Vec<HashMap<String, Symbol>>,
}

impl<'a> Resolver<'a> {
    pub fn new(ast: &'a Program, source: String) -> Self {
        let mut var_env = HashMap::new();
        var_env.insert("clock".to_string(), Symbol::Function { params: vec![] });
        var_env.insert("print".to_string(), Symbol::Function { params: vec![] });

        Self {
            source,
            program: ast,
            errors: vec![],
            scopes: vec![var_env],
        }
    }

    pub fn resolve(&mut self) -> &Vec<Report> {
        for stmt in &self.program.statements {
            self.declare_stmt(&stmt);
        }

        for stmt in &self.program.statements {
            self.resolve_stmt(&stmt);
        }
        &self.errors
    }

    fn report(&mut self, error: ResolverError) {
        self.errors.push(error.into());
    }

    fn lookup_symbol(&self, key: &str) -> Option<&Symbol> {
        for scope in self.scopes.iter().rev() {
            if let Some(symbol) = scope.get(key) {
                return Some(symbol);
            }
        }
        None
    }

    fn curr_scope(&mut self) -> &mut HashMap<String, Symbol> {
        self.scopes.last_mut().unwrap()
    }

    fn declare_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::FunDecl(fun_decl) => {
                let name = &fun_decl.node.ident.node;
                self.curr_scope().insert(
                    name.clone(),
                    Symbol::Function {
                        params: fun_decl.node.params.clone(),
                    },
                );
            }
            _ => {}
        }
    }

    fn resolve_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::ExprStmtNode(expr_stmt) => self.resolve_expr_stmt(expr_stmt),
            Stmt::VarDecl(var_decl) => self.resolve_var_decl(var_decl),
            Stmt::FunDecl(fun_decl) => self.resolve_fun_decl(fun_decl),
            Stmt::While(while_stmt) => self.resolve_while_stmt(while_stmt),
            Stmt::Return(return_stmt) => self.resolve_return_stmt(return_stmt),
        }
    }
    fn resolve_expr_stmt(&mut self, expr_stmt: &Typed<ExprStmt>) {
        self.resolve_expr(&expr_stmt.node.expr);
    }

    fn resolve_var_decl(&mut self, var_decl: &Typed<VarDeclStmt>) {
        if let Some(init) = &var_decl.node.initializer {
            self.resolve_expr(init);
        }
        self.curr_scope().insert(
            var_decl.node.ident.node.clone(),
            Symbol::Variable {
                initialized: var_decl.node.initializer.is_some(),
            },
        );
    }

    fn resolve_fun_decl(&mut self, fun_decl: &Typed<FunDeclStmt>) {
        self.curr_scope().insert(
            fun_decl.node.ident.node.clone(),
            Symbol::Function {
                params: fun_decl.node.params.clone(),
            },
        );

        self.scopes.push(HashMap::new());
        for param in &fun_decl.node.params {
            if self.curr_scope().get(param.node.name.node.as_str()).is_some() {
                self.report(DuplicateParameter {
                    src: self.source.to_string(),
                    span: param.span,
                    function_name: fun_decl.node.ident.node.clone(),
                })
            } else {
                self.curr_scope()
                    .insert(param.node.name.node.clone(), Symbol::Variable { initialized: true });
            }
        }

        for stmt in &fun_decl.node.body.node.statements {
            self.resolve_stmt(stmt);
        }
        self.scopes.pop();
    }

    fn resolve_stmts(&mut self, stmts: &Vec<Stmt>) {
        self.scopes.push(HashMap::new());
        for stmt in stmts {
            self.resolve_stmt(stmt);
        }
        self.scopes.pop();
    }

    fn resolve_while_stmt(&mut self, while_stmt: &Typed<WhileStmt>) {
        self.resolve_expr(&while_stmt.node.condition);
        self.resolve_stmts(&while_stmt.node.body.node.statements);
    }

    fn resolve_return_stmt(&mut self, return_stmt: &Typed<ReturnStmt>) {
        if let Some(return_expr) = &return_stmt.node.expr {
            self.resolve_expr(return_expr);
        }
    }

    fn resolve_expr(&mut self, expr: &Typed<Expr>) {
        match &expr.node {
            Expr::Literal(_) => {}
            Expr::Block(block) => {
                self.scopes.push(HashMap::new());
                for stmt in &block.statements {
                    self.resolve_stmt(stmt);
                }
                if let Some(expr) = &block.expr {
                    self.resolve_expr(expr)
                }

                self.scopes.pop();
            }
            Expr::If(if_expr) => {
                self.resolve_expr(&if_expr.condition);
                self.resolve_stmts(&if_expr.then_branch.node.statements);
                if let Some(else_branch) = &if_expr.else_branch {
                    self.resolve_stmts(&else_branch.node.statements);
                }
            }
            Expr::MethodCall(method_call) => {
                todo!()
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
                        for scope in self.scopes.iter_mut().rev() {
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
                    if let None = self.lookup_symbol(&ident.node) {
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
                self.scopes.push(HashMap::new());
                for param in &lambda.parameters {
                    if self.curr_scope().get(param.node.name.node.as_str()).is_some() {
                        self.report(DuplicateLambdaParameter {
                            src: self.source.to_string(),
                            span: param.span,
                        })
                    } else {
                        self.curr_scope()
                            .insert(param.node.name.node.clone(), Symbol::Variable { initialized: true });
                    }
                }

                for stmt in &lambda.body.node.statements {
                    self.resolve_stmt(stmt);
                }
                self.scopes.pop();
            }
        }
    }
}
