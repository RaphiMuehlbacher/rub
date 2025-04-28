use crate::ast::{
    AssignExpr, BinaryExpr, BlockStmt, CallExpr, Expr, FunDeclStmt, IfStmt, LambdaExpr, LiteralExpr, LogicalExpr, Program, Stmt, Typed,
    UnaryExpr, VarDeclStmt, WhileStmt,
};
use miette::Report;

pub struct Interpreter<'a> {
    source: String,
    program: &'a Program,
    errors: Vec<Report>,
}

impl<'a> Interpreter<'a> {
    pub fn new(source: String, program: &'a Program) -> Self {
        Self {
            source,
            program,
            errors: vec![],
        }
    }

    fn interpret_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::ExprStmt(expr) => self.expr_stmt(expr),
            Stmt::PrintStmt(print) => self.print_stmt(print),
            Stmt::VarDecl(var_decl) => self.var_decl(var_decl),
            Stmt::FunDecl(fun_decl) => self.fun_decl(fun_decl),
            Stmt::Block(block) => self.block(block),
            Stmt::If(if_stmt) => self.if_stmt(if_stmt),
            Stmt::While(while_stmt) => self.while_stmt(while_stmt),
            Stmt::Return(return_stmt) => self.return_stmt(return_stmt),
        }
    }

    fn expr_stmt(&mut self, expr: &Typed<Expr>) {
        self.interpret_expr(&expr);
    }

    fn print_stmt(&mut self, print: &Typed<Expr>) {
        self.interpret_expr(&print);
    }

    fn var_decl(&mut self, var_decl: &Typed<VarDeclStmt>) {
        todo!()
    }

    fn fun_decl(&mut self, fun_decl: &Typed<FunDeclStmt>) {
        todo!()
    }

    fn block(&mut self, block: &Typed<BlockStmt>) {
        for stmt in &block.node.statements {
            self.interpret_stmt(stmt);
        }
    }

    fn if_stmt(&mut self, if_stmt: &Typed<IfStmt>) {
        todo!()
    }

    fn while_stmt(&mut self, while_stmt: &Typed<WhileStmt>) {
        todo!()
    }

    fn return_stmt(&mut self, return_stmt: &Typed<Option<Expr>>) {
        todo!()
    }

    fn interpret_expr(&mut self, expr: &Typed<Expr>) -> () {
        match &expr.node {
            Expr::Literal(lit) => self.literal(lit),
            Expr::Unary(unary) => self.unary(unary),
            Expr::Binary(binary) => self.binary(binary),
            Expr::Grouping(grouping) => self.grouping(grouping),
            Expr::Variable(variable) => self.variable(variable),
            Expr::Assign(assign) => self.assign(assign),
            Expr::Logical(logical) => self.logical(logical),
            Expr::Call(call) => self.call_stmt(call),
            Expr::Lambda(lambda) => self.lambda(lambda),
        }
    }

    fn literal(&mut self, lit: &Typed<LiteralExpr>) {
        match &lit.node {
            LiteralExpr::Number(num) => {}
            LiteralExpr::String(str) => {}
            LiteralExpr::Bool(bool) => {}
            LiteralExpr::Nil => {}
        }
    }

    fn unary(&mut self, unary: &Typed<UnaryExpr>) {
        todo!()
    }

    fn binary(&mut self, binary: &Typed<BinaryExpr>) {
        todo!()
    }

    fn grouping(&mut self, grouping: &Typed<Box<Expr>>) {
        todo!()
    }

    fn variable(&mut self, variable: &Typed<String>) {
        todo!()
    }

    fn assign(&mut self, assign: &Typed<AssignExpr>) {
        todo!()
    }

    fn logical(&mut self, logical: &Typed<LogicalExpr>) {
        todo!()
    }

    fn call_stmt(&mut self, call: &Typed<CallExpr>) {
        todo!()
    }

    fn lambda(&mut self, lambda: &Typed<LambdaExpr>) {
        todo!()
    }
}
