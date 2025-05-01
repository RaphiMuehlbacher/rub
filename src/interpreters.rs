use crate::ast::{
    BinaryOp, BlockStmt, Expr, FunDeclStmt, IfStmt, LiteralExpr, Program, ReturnStmt, Stmt, Typed, UnaryOp, VarDeclStmt, WhileStmt,
};
use miette::Report;
use std::cmp::PartialEq;
use std::fmt;

#[derive(Debug, PartialEq)]
pub enum Value {
    Number(f64),
    String(String),
    Bool(bool),
    Nil,
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Number(num) => write!(f, "{num}"),
            Value::String(str) => write!(f, "{str}"),
            Value::Bool(bool) => write!(f, "{bool}"),
            Value::Nil => write!(f, "nil"),
        }
    }
}

impl Value {
    fn to_number(self) -> f64 {
        match self {
            Value::Number(num) => num,
            _ => panic!(),
        }
    }
    fn to_string(self) -> String {
        match self {
            Value::String(str) => str,
            _ => panic!(),
        }
    }
    fn to_bool(self) -> bool {
        match self {
            Value::Bool(bool) => bool,
            _ => panic!(),
        }
    }
}

pub struct InterpreterResult<'a> {
    pub errors: &'a Vec<Report>,
}

pub struct Interpreter<'a> {
    source: String,
    program: &'a Program,
    errors: Vec<Report>,
}

impl<'a> Interpreter<'a> {
    pub fn new(program: &'a Program, source: String) -> Self {
        Self {
            source,
            program,
            errors: vec![],
        }
    }

    pub fn interpret(&mut self) -> InterpreterResult {
        for stmt in &self.program.statements {
            self.interpret_stmt(stmt);
        }
        InterpreterResult { errors: &self.errors }
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
        let value = self.interpret_expr(&print);
        println!("{value}");
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

    fn return_stmt(&mut self, return_stmt: &Typed<ReturnStmt>) {
        todo!()
    }

    fn interpret_expr(&mut self, expr: &Typed<Expr>) -> Value {
        match &expr.node {
            Expr::Literal(lit) => match &lit {
                LiteralExpr::Number(num) => Value::Number(*num),
                LiteralExpr::String(str) => Value::String(str.clone()),
                LiteralExpr::Bool(bool) => Value::Bool(*bool),
                LiteralExpr::Nil => Value::Nil,
            },
            Expr::Unary(unary) => {
                let right = self.interpret_expr(&unary.expr);

                match unary.op.node {
                    UnaryOp::Bang => Value::Bool(!right.to_bool()),

                    UnaryOp::Minus => Value::Number(-right.to_number()),
                }
            }
            Expr::Binary(binary) => {
                let left = self.interpret_expr(&binary.left);
                let right = self.interpret_expr(&binary.right);

                match binary.op.node {
                    BinaryOp::Plus => Value::Number(left.to_number() + right.to_number()),
                    BinaryOp::Minus => Value::Number(left.to_number() - right.to_number()),
                    BinaryOp::Star => Value::Number(left.to_number() + right.to_number()),
                    BinaryOp::Slash => Value::Number(left.to_number() / right.to_number()),
                    BinaryOp::Greater => Value::Bool(left.to_number() > right.to_number()),
                    BinaryOp::GreaterEqual => Value::Bool(left.to_number() >= right.to_number()),
                    BinaryOp::Less => Value::Bool(left.to_number() < right.to_number()),
                    BinaryOp::LessEqual => Value::Bool(left.to_number() <= right.to_number()),
                    BinaryOp::EqualEqual => Value::Bool(left == right),
                    BinaryOp::BangEqual => Value::Bool(left != right),
                }
            }
            Expr::Grouping(grouping) => {
                todo!()
            }
            Expr::Variable(variable) => {
                todo!()
            }
            Expr::Assign(assign) => {
                todo!()
            }
            Expr::Logical(logical) => {
                todo!()
            }
            Expr::Call(call) => {
                todo!()
            }
            Expr::Lambda(lambda) => {
                todo!()
            }
        }
    }
}
