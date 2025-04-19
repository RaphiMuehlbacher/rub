use crate::ast::{
    Accept, AssignExpr, BinaryExpr, BlockStmt, CallExpr, Expr, ExprVisitor, FunDeclStmt, IfStmt,
    LambdaExpr, LiteralExpr, LogicalExpr, Program, Stmt, StmtVisitor, Typed, UnaryExpr,
    VarDeclStmt, WhileStmt,
};
use crate::type_inferrer::Type::TypeVar;
use miette::Report;
use std::collections::HashMap;

pub type TypeVarId = usize;

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Float,
    Bool,
    String,
    Nil,
    TypeVar(TypeVarId),
}

pub struct TypeInferrer<'a> {
    program: &'a Program,
    source: String,
    errors: Vec<Report>,
    type_env: HashMap<TypeVarId, Type>,
    var_env: HashMap<String, TypeVarId>,
}

impl<'a> TypeInferrer<'a> {
    pub fn new(ast: &'a Program, source: String) -> Self {
        Self {
            program: ast,
            source,
            errors: vec![],
            type_env: HashMap::new(),
            var_env: HashMap::new(),
        }
    }

    fn lookup_type(&self, type_id: &TypeVarId) -> Type {
        let var_type = self.type_env.get(type_id).unwrap();

        if let TypeVar(id) = var_type {
            return self.lookup_type(id);
        }
        var_type.clone()
    }

    pub fn infer(&mut self) -> &Vec<Report> {
        self.program.accept(self);
        &self.errors
    }

    fn infer_expr_stmt(&mut self, expr_stmt: &Typed<Expr>) {
        todo!()
    }

    fn infer_print_stmt(&mut self, print_stmt: &Typed<Expr>) {
        todo!()
    }

    fn infer_var_decl(&mut self, var_decl: &Typed<VarDeclStmt>) {
        self.var_env
            .insert(var_decl.node.ident.node.clone(), var_decl.type_id);
        if let Some(init) = &var_decl.node.initializer {
            let init_type = init.accept(self);
            self.type_env.insert(var_decl.type_id, init_type);
        }
    }

    fn infer_fun_decl(&mut self, fun_decl: &Typed<FunDeclStmt>) {
        todo!()
    }

    fn infer_block(&mut self, block: &Typed<BlockStmt>) {
        todo!()
    }

    fn infer_if_stmt(&mut self, if_stmt: &Typed<IfStmt>) {
        todo!()
    }

    fn infer_while_stmt(&mut self, while_stmt: &Typed<WhileStmt>) {
        todo!()
    }

    fn infer_return_stmt(&mut self, return_stmt: &Typed<Option<Expr>>) {
        todo!()
    }

    fn infer_literal_expr(&mut self, literal_expr: &Typed<LiteralExpr>) -> Type {
        let ty = match literal_expr.node {
            LiteralExpr::Number(_) => Type::Float,
            LiteralExpr::String(_) => Type::String,
            LiteralExpr::Bool(_) => Type::Bool,
            LiteralExpr::Nil => Type::Nil,
        };

        // self.type_env[literal_expr.type_id] = ty.clone();
        ty
    }

    fn infer_unary_expr(&mut self, unary_expr: &Typed<UnaryExpr>) -> Type {
        todo!()
    }

    fn infer_binary_expr(&mut self, binary_expr: &Typed<BinaryExpr>) -> Type {
        todo!()
    }

    fn infer_grouping_expr(&mut self, grouping_expr: &Typed<Box<Expr>>) -> Type {
        todo!()
    }

    fn infer_variable_expr(&mut self, variable_expr: &Typed<String>) -> Type {
        Type::TypeVar(0)
    }

    fn infer_assign_expr(&mut self, assign_expr: &Typed<AssignExpr>) -> Type {
        let value_type = assign_expr.node.value.accept(self);
        // self.type_env[assign_expr.type_id] = value_type.clone();
        value_type
    }

    fn infer_logical_expr(&mut self, logical_expr: &Typed<LogicalExpr>) -> Type {
        todo!()
    }

    fn infer_call_expr(&mut self, call_expr: &Typed<CallExpr>) -> Type {
        todo!()
    }

    fn lambda_expr(&mut self, lambda: &Typed<LambdaExpr>) -> Type {
        todo!()
    }
}

impl<'a> StmtVisitor for TypeInferrer<'a> {
    fn visit_program(&mut self, program: &Program) {
        for stmt in &program.statements {
            stmt.accept(self);
        }
    }

    fn visit_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::ExprStmt(expr_stmt) => self.infer_expr_stmt(expr_stmt),
            Stmt::PrintStmt(print_stmt) => self.infer_print_stmt(print_stmt),
            Stmt::VarDecl(var_decl) => self.infer_var_decl(var_decl),
            Stmt::FunDecl(fun_decl) => self.infer_fun_decl(fun_decl),
            Stmt::Block(block) => self.infer_block(block),
            Stmt::If(if_stmt) => self.infer_if_stmt(if_stmt),
            Stmt::While(while_stmt) => self.infer_while_stmt(while_stmt),
            Stmt::Return(return_stmt) => self.infer_return_stmt(return_stmt),
        }
    }
}
impl<'a> ExprVisitor for TypeInferrer<'a> {
    type Output = Type;
    fn visit_expr(&mut self, expr: &Expr) -> Self::Output {
        match expr {
            Expr::Literal(literal_expr) => self.infer_literal_expr(literal_expr),
            Expr::Unary(unary_expr) => self.infer_unary_expr(unary_expr),
            Expr::Binary(binary_expr) => self.infer_binary_expr(binary_expr),
            Expr::Grouping(grouping) => self.infer_grouping_expr(grouping),
            Expr::Variable(variable_expr) => self.infer_variable_expr(variable_expr),
            Expr::Assign(assign) => self.infer_assign_expr(assign),
            Expr::Logical(logical_expr) => self.infer_logical_expr(logical_expr),
            Expr::Call(call) => self.infer_call_expr(call),
            Expr::Lambda(lambda) => self.lambda_expr(lambda),
        }
    }
}
