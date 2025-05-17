use crate::ast::{
    BinaryOp, BlockExpr, Expr, ExprStmt, FunDeclStmt, LiteralExpr, LogicalOp, Parameter, Program, ReturnStmt, Stmt, Typed, UnaryOp,
    VarDeclStmt, WhileStmt,
};
use crate::builtins::{clock_native, print_native};
use crate::error::{InterpreterError, RuntimeError};
use crate::interpreters::Function::{NativeFunction, UserFunction};
use crate::type_inferrer::{Type, TypeVarId};
use miette::Report;
use std::cmp::PartialEq;
use std::collections::HashMap;
use std::ops::Deref;
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Number(f64),
    String(Rc<str>),
    Bool(bool),
    Function(Rc<Function>),
    Array(Vec<Value>),
    Nil,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Function {
    NativeFunction(fn(Vec<Value>) -> Result<Value, String>),
    UserFunction {
        name: Option<String>,
        params: Rc<Vec<Typed<Parameter>>>,
        body: Rc<Typed<BlockExpr>>,
    },
}

impl Value {
    pub fn to_printable_value(&self) -> String {
        match self {
            Value::Number(num) => format!("{num}"),
            Value::String(str) => format!("{str}"),
            Value::Bool(bool) => format!("{bool}"),
            Value::Array(array) => {
                let elements: Vec<String> = array.iter().map(|value| value.to_printable_value()).collect();
                format!("[{}]", elements.join(", "))
            }
            Value::Function(function) => match function.as_ref() {
                NativeFunction(_) => "<native_fn>".to_string(),
                UserFunction { name, params, body: _ } => {
                    let param_strings: Vec<String> = params.iter().map(|p| p.node.name.node.clone()).collect();
                    match name {
                        None => format!("<fn ({})>", param_strings.join(", ")),
                        Some(name) => {
                            format!("<fn {name}({})>", param_strings.join(", "))
                        }
                    }
                }
            },
            Value::Nil => "nil".to_string(),
        }
    }

    fn to_number(&self) -> f64 {
        match self {
            Value::Number(num) => *num,
            _ => panic!(),
        }
    }

    fn to_string(&self) -> &str {
        match self {
            Value::String(str) => str,
            _ => panic!(),
        }
    }

    fn to_bool(&self) -> bool {
        match self {
            Value::Bool(bool) => *bool,
            _ => panic!(),
        }
    }

    fn to_fn(&self) -> &Function {
        match self {
            Value::Function(func) => func,
            _ => panic!(),
        }
    }
}

pub struct InterpreterResult {
    pub error: Option<Report>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ControlFlow {
    Return(Value),
}

pub struct Interpreter<'a> {
    source: String,
    program: &'a Program,
    type_env: &'a HashMap<TypeVarId, Type>,
    var_env: Vec<HashMap<String, Value>>,
}

impl<'a> Interpreter<'a> {
    pub fn new(program: &'a Program, type_env: &'a HashMap<TypeVarId, Type>, source: String) -> Self {
        let mut var_env = HashMap::new();
        var_env.insert("clock".to_string(), Value::Function(Rc::new(NativeFunction(clock_native))));
        var_env.insert("print".to_string(), Value::Function(Rc::new(NativeFunction(print_native))));

        Self {
            source,
            program,
            type_env,
            var_env: vec![var_env],
        }
    }

    fn insert_var(&mut self, name: String, value: Value) {
        self.var_env.last_mut().unwrap().insert(name, value);
    }

    fn get_var(&mut self, name: &str) -> &Value {
        for env in self.var_env.iter().rev() {
            if let Some(val) = env.get(name) {
                return val;
            }
        }
        panic!()
    }

    pub fn interpret(&mut self) -> InterpreterResult {
        for stmt in &self.program.statements {
            self.declare_stmt(stmt);
        }
        for stmt in &self.program.statements {
            let result = self.interpret_stmt(stmt);
            match result {
                Ok(_) => {}
                Err(InterpreterError::RuntimeError(err)) => {
                    return InterpreterResult {
                        error: Some(Report::from(err)),
                    };
                }
                Err(InterpreterError::ControlFlowError(ControlFlow::Return(_))) => {
                    return InterpreterResult {
                        error: Some(
                            RuntimeError::ReturnOutsideFunction {
                                src: self.source.to_string(),
                                span: stmt.span(),
                            }
                            .into(),
                        ),
                    };
                }
            }
        }
        InterpreterResult { error: None }
    }

    fn declare_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::FunDecl(fun_decl) => {
                let value = Value::Function(Rc::new(UserFunction {
                    name: Some(fun_decl.node.ident.node.clone()),
                    params: Rc::new(fun_decl.node.params.clone()),
                    body: Rc::new(fun_decl.node.body.clone()),
                }));
                self.insert_var(fun_decl.node.ident.node.clone(), value);
            }
            _ => {}
        }
    }

    fn interpret_stmt(&mut self, stmt: &Stmt) -> Result<(), InterpreterError> {
        match stmt {
            Stmt::ExprStmtNode(expr) => self.expr_stmt(expr),
            Stmt::VarDecl(var_decl) => self.var_decl(var_decl),
            Stmt::FunDecl(fun_decl) => self.fun_decl(fun_decl),
            Stmt::While(while_stmt) => self.while_stmt(while_stmt),
            Stmt::Return(return_stmt) => self.return_stmt(return_stmt),
        }
    }

    fn interpret_stmts(&mut self, stmts: &Vec<Stmt>) -> Result<(), InterpreterError> {
        for stmt in stmts {
            self.interpret_stmt(stmt)?;
        }
        Ok(())
    }

    fn expr_stmt(&mut self, expr: &Typed<ExprStmt>) -> Result<(), InterpreterError> {
        self.interpret_expr(&expr.node.expr)?;
        Ok(())
    }

    fn var_decl(&mut self, var_decl: &Typed<VarDeclStmt>) -> Result<(), InterpreterError> {
        if let Some(init) = &var_decl.node.initializer {
            let value = self.interpret_expr(&init)?;
            self.insert_var(var_decl.node.ident.node.clone(), value);
        } else {
            self.insert_var(var_decl.node.ident.node.clone(), Value::Nil);
        }

        Ok(())
    }

    fn fun_decl(&mut self, fun_decl: &Typed<FunDeclStmt>) -> Result<(), InterpreterError> {
        self.insert_var(
            fun_decl.node.ident.node.clone(),
            Value::Function(Rc::new(UserFunction {
                name: Some(fun_decl.node.ident.node.clone()),
                params: Rc::new(fun_decl.node.params.clone()),
                body: Rc::new(fun_decl.node.body.clone()),
            })),
        );

        Ok(())
    }

    fn while_stmt(&mut self, while_stmt: &Typed<WhileStmt>) -> Result<(), InterpreterError> {
        let mut cond_value = self.interpret_expr(&while_stmt.node.condition)?.to_bool();
        while cond_value {
            self.interpret_stmts(&while_stmt.node.body.node.statements)?;
            cond_value = self.interpret_expr(&while_stmt.node.condition)?.to_bool();
        }

        Ok(())
    }

    fn return_stmt(&mut self, return_stmt: &Typed<ReturnStmt>) -> Result<(), InterpreterError> {
        let value = if let Some(expr) = &return_stmt.node.expr {
            self.interpret_expr(expr)?
        } else {
            Value::Nil
        };
        Err(InterpreterError::ControlFlowError(ControlFlow::Return(value)))
    }

    fn interpret_block_expr(&mut self, block: &BlockExpr) -> Result<Value, InterpreterError> {
        for stmt in &block.statements {
            self.interpret_stmt(stmt)?;
        }

        if let Some(expr) = &block.expr {
            Ok(self.interpret_expr(expr.deref())?)
        } else {
            Ok(Value::Nil)
        }
    }

    fn interpret_expr(&mut self, expr: &Typed<Expr>) -> Result<Value, InterpreterError> {
        match &expr.node {
            Expr::Block(block) => Ok(self.interpret_block_expr(block)?),
            Expr::If(if_expr) => {
                let cond_value = self.interpret_expr(&if_expr.condition)?;

                let return_value = if cond_value.to_bool() {
                    self.interpret_block_expr(&if_expr.then_branch.node)?
                } else if let Some(else_branch) = &if_expr.else_branch {
                    self.interpret_block_expr(&else_branch.node)?
                } else {
                    Value::Nil
                };

                Ok(return_value)
            }
            Expr::Literal(lit) => match &lit {
                LiteralExpr::Number(num) => Ok(Value::Number(*num)),
                LiteralExpr::String(str) => Ok(Value::String(Rc::from(str.as_str()))),
                LiteralExpr::Bool(bool) => Ok(Value::Bool(*bool)),
                LiteralExpr::Nil => Ok(Value::Nil),
                LiteralExpr::Array(array) => {
                    let mut values = vec![];
                    for expr in array {
                        values.push(self.interpret_expr(expr)?);
                    }
                    Ok(Value::Array(values))
                }
            },

            Expr::Unary(unary) => {
                let right = self.interpret_expr(&unary.expr)?;

                match unary.op.node {
                    UnaryOp::Bang => Ok(Value::Bool(!right.to_bool())),
                    UnaryOp::Minus => Ok(Value::Number(-right.to_number())),
                }
            }

            Expr::Binary(binary) => {
                let left = self.interpret_expr(&binary.left)?;
                let right = self.interpret_expr(&binary.right)?;

                let left_type = self.type_env.get(&expr.type_id).unwrap();

                match binary.op.node {
                    BinaryOp::Plus => match left_type {
                        Type::Float => Ok(Value::Number(left.to_number() + right.to_number())),
                        Type::String => {
                            let left_string = left.to_string();
                            let right_string = right.to_string();
                            let mut buffer = String::with_capacity(left_string.len() + right_string.len());
                            buffer.push_str(left_string);
                            buffer.push_str(right_string);

                            Ok(Value::String(Rc::from(buffer)))
                        }
                        _ => panic!(),
                    },
                    BinaryOp::Minus => Ok(Value::Number(left.to_number() - right.to_number())),
                    BinaryOp::Star => Ok(Value::Number(left.to_number() * right.to_number())),
                    BinaryOp::Slash => Ok(Value::Number(left.to_number() / right.to_number())),
                    BinaryOp::Greater => Ok(Value::Bool(left.to_number() > right.to_number())),
                    BinaryOp::GreaterEqual => Ok(Value::Bool(left.to_number() >= right.to_number())),
                    BinaryOp::Less => Ok(Value::Bool(left.to_number() < right.to_number())),
                    BinaryOp::LessEqual => Ok(Value::Bool(left.to_number() <= right.to_number())),
                    BinaryOp::EqualEqual => Ok(Value::Bool(left == right)),
                    BinaryOp::BangEqual => Ok(Value::Bool(left != right)),
                }
            }

            Expr::Grouping(grouping) => self.interpret_expr(grouping),
            Expr::Variable(variable) => Ok(self.get_var(&variable.node).clone()),

            Expr::Assign(assign) => {
                let value = self.interpret_expr(&assign.value)?;
                self.insert_var(assign.target.node.clone(), value.clone());
                Ok(value)
            }

            Expr::Logical(logical) => {
                let left = self.interpret_expr(&logical.left)?;
                let right = self.interpret_expr(&logical.right)?;

                match logical.op.node {
                    LogicalOp::And => Ok(Value::Bool(left.to_bool() && right.to_bool())),
                    LogicalOp::Or => Ok(Value::Bool(left.to_bool() || right.to_bool())),
                }
            }

            Expr::Call(call) => {
                let callee = self.interpret_expr(call.callee.deref())?;

                let func = callee.to_fn();

                match func {
                    NativeFunction(native_fun) => {
                        let mut arguments = Vec::new();
                        for arg in call.arguments.iter() {
                            let value = self.interpret_expr(arg)?;
                            arguments.push(value);
                        }
                        Ok(native_fun(arguments).expect("error handling for native functions not yet implemented"))
                    }
                    UserFunction { name: _, params, body } => {
                        self.var_env.push(HashMap::new());
                        for (arg, param) in call.arguments.iter().zip(params.as_ref()) {
                            let value = self.interpret_expr(arg)?;
                            self.insert_var(param.node.name.node.clone(), value);
                        }
                        let return_val = match self.interpret_stmts(&body.node.statements) {
                            Ok(_) => Value::Nil,
                            Err(InterpreterError::RuntimeError(err)) => return Err(InterpreterError::RuntimeError(err)),
                            Err(InterpreterError::ControlFlowError(ControlFlow::Return(val))) => val,
                        };

                        self.var_env.pop();
                        Ok(return_val)
                    }
                }
            }

            Expr::Lambda(lambda) => Ok(Value::Function(Rc::new(UserFunction {
                name: None,
                params: Rc::new(lambda.parameters.clone()),
                body: Rc::new(lambda.body.deref().clone()),
            }))),
        }
    }
}
