use crate::ast::{
    AssignExpr, BinaryExpr, CallExpr, Expr, FunDeclStmt, Ident, IfStmt, LogicalExpr, Program,
    Spanned, Stmt, UnaryExpr, VarDeclStmt, WhileStmt,
};
use crate::error::ResolverError;
use crate::error::ResolverError::{UndefinedVariable, UninitializedVariable};
use miette::Report;
use std::collections::HashMap;
use std::ops::Deref;

#[derive(Debug, Clone, PartialEq)]
pub enum Symbol {
    Variable { initialized: bool },
    Function { params: Vec<Ident> },
}

pub struct Resolver<'a> {
    source: String,
    program: &'a Program,
    errors: Vec<Report>,
    scope: HashMap<String, Symbol>,
}

impl<'a> Resolver<'a> {
    pub fn new(ast: &'a Program, source: String) -> Self {
        let mut scope = HashMap::new();
        Self {
            source,
            program: ast,
            errors: vec![],
            scope,
        }
    }

    fn report(&mut self, error: ResolverError) {
        self.errors.push(error.into());
    }

    pub fn resolve(mut self) -> Vec<Report> {
        for stmt in &self.program.statements {
            self.resolve_stmt(stmt);
        }
        self.errors
    }

    fn resolve_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::ExprStmt(expr_stmt) => self.resolve_expr_stmt(expr_stmt),
            Stmt::PrintStmt(print_stmt) => self.resolve_print_stmt(print_stmt),
            Stmt::VarDecl(var_decl) => self.resolve_var_decl(var_decl),
            Stmt::FunDecl(fun_decl) => self.resolve_fun_decl(fun_decl),
            Stmt::Block(block) => self.resolve_block(block),
            Stmt::If(if_stmt) => self.resolve_if_stmt(if_stmt),
            Stmt::While(while_stmt) => self.resolve_while_stmt(while_stmt),
            Stmt::Return(return_stmt) => self.resolve_return_stmt(return_stmt),
        }
    }

    fn resolve_expr_stmt(&mut self, expr_stmt: &Spanned<Expr>) {
        self.resolve_expr(&expr_stmt.node);
    }

    fn resolve_print_stmt(&mut self, print_stmt: &Spanned<Expr>) {
        self.resolve_expr(&print_stmt.node);
    }

    fn resolve_var_decl(&mut self, var_decl: &Spanned<VarDeclStmt>) {
        self.scope.insert(
            var_decl.node.ident.name.clone(),
            Symbol::Variable {
                initialized: var_decl.node.initializer.is_some(),
            },
        );
    }

    fn resolve_fun_decl(&mut self, fun_decl: &Spanned<FunDeclStmt>) {
        self.scope.insert(
            fun_decl.node.ident.name.clone(),
            Symbol::Function {
                params: fun_decl.node.params.clone(),
            },
        );
    }

    fn resolve_block(&mut self, block: &Spanned<Vec<Stmt>>) {
        todo!()
    }

    fn resolve_if_stmt(&mut self, if_stmt: &Spanned<IfStmt>) {
        todo!()
    }

    fn resolve_while_stmt(&mut self, while_stmt: &Spanned<WhileStmt>) {
        todo!()
    }

    fn resolve_return_stmt(&mut self, return_stmt: &Spanned<Option<Expr>>) {
        if let Some(node) = &return_stmt.node {
            self.resolve_expr(node);
        }
    }

    fn resolve_expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Literal(_) => {}
            Expr::Unary(unary_expr) => self.resolve_unary_expr(unary_expr),
            Expr::Binary(binary_expr) => self.resolve_binary_expr(binary_expr),
            Expr::Grouping(grouping) => self.resolve_grouping_expr(grouping),
            Expr::Variable(variable_expr) => self.resolve_variable_expr(variable_expr),
            Expr::Assign(assign) => self.resolve_assign_expr(assign),
            Expr::Logical(logical_expr) => self.resolve_logical_expr(logical_expr),
            Expr::Call(call) => self.resolve_call_expr(call),
        }
    }

    fn resolve_unary_expr(&mut self, unary_expr: &Spanned<UnaryExpr>) {
        self.resolve_expr(&unary_expr.node.expr);
    }

    fn resolve_binary_expr(&mut self, binary_expr: &Spanned<BinaryExpr>) {
        self.resolve_expr(&binary_expr.node.left);
        self.resolve_expr(&binary_expr.node.right);
    }

    fn resolve_grouping_expr(&mut self, grouping_expr: &Spanned<Box<Expr>>) {
        self.resolve_expr(grouping_expr.node.deref());
    }

    fn resolve_variable_expr(&mut self, variable_expr: &Ident) {
        match self.scope.get(variable_expr.name.as_str()) {
            Some(Symbol::Variable { initialized: false }) => self.report(UninitializedVariable {
                src: self.source.clone(),
                span: variable_expr.span,
                name: variable_expr.name.clone(),
            }),
            None => self.report(UndefinedVariable {
                src: self.source.clone(),
                span: variable_expr.span,
                name: variable_expr.name.clone(),
            }),
            _ => {}
        }
    }

    fn resolve_assign_expr(&mut self, assign_expr: &Spanned<AssignExpr>) {
        if let None = self.scope.get(assign_expr.node.target.name.as_str()) {
            self.report(UndefinedVariable {
                src: self.source.clone(),
                span: assign_expr.node.target.span,
                name: assign_expr.node.target.name.clone(),
            })
        }
    }

    fn resolve_logical_expr(&mut self, logical_expr: &Spanned<LogicalExpr>) {
        self.resolve_expr(&logical_expr.node.left);
        self.resolve_expr(&logical_expr.node.right);
    }

    fn resolve_call_expr(&mut self, call_expr: &Spanned<CallExpr>) {
        todo!()
    }
}
