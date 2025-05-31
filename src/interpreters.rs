use crate::MethodRegistry;
use crate::ast::{
    BinaryOp, BlockExpr, Expr, ExprStmt, FunDeclStmt, LiteralExpr, LogicalOp, Parameter, Program, ReturnStmt, Stmt, Typed, UnaryOp,
    VarDeclStmt, WhileStmt,
};
use crate::builtins::{clock_native, print_native};
use crate::error::RuntimeError::DivisionByZero;
use crate::error::{InterpreterError, RuntimeError};
use crate::interpreters::Function::{NativeFunction, UserFunction};
use crate::type_inferrer::{Type, TypeVarId};
use miette::Report;
use std::cell::RefCell;
use std::cmp::PartialEq;
use std::collections::HashMap;
use std::ops::Deref;
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Int(i64),
    Float(f64),
    String(Rc<str>),
    Bool(bool),
    Function(Rc<Function>),
    Vec(Rc<RefCell<Vec<Value>>>),
    Nil,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Function {
    NativeFunction(fn(Vec<Value>) -> Result<Value, InterpreterError>),
    UserFunction {
        name: Option<String>,
        params: Rc<Vec<Parameter>>,
        body: Rc<Typed<BlockExpr>>,
        env: Env,
    },
}

impl Value {
    pub fn to_printable_value(&self) -> String {
        match self {
            Value::Int(int) => format!("{int}"),
            Value::Float(num) => format!("{num}"),
            Value::String(str) => format!("{str}"),
            Value::Bool(bool) => format!("{bool}"),
            Value::Vec(vec) => {
                let elements: Vec<String> = vec.borrow().iter().map(|value| value.to_printable_value()).collect();
                format!("[{}]", elements.join(", "))
            }
            Value::Function(function) => match function.as_ref() {
                NativeFunction(_) => "<native_fn>".to_string(),
                UserFunction {
                    name,
                    params,
                    body: _,
                    env: _,
                } => {
                    let param_strings: Vec<String> = params.iter().map(|p| p.name.node.clone()).collect();
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

    pub fn to_int(&self) -> i64 {
        match self {
            Value::Int(num) => *num,
            _ => panic!(),
        }
    }
    pub fn to_float(&self) -> f64 {
        match self {
            Value::Float(num) => *num,
            _ => panic!(),
        }
    }

    pub fn to_string(&self) -> &str {
        match self {
            Value::String(str) => str,
            _ => panic!(),
        }
    }

    pub fn to_bool(&self) -> bool {
        match self {
            Value::Bool(bool) => *bool,
            _ => panic!(),
        }
    }

    pub fn to_fn(&self) -> &Function {
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

type Env = Rc<RefCell<Environment>>;

#[derive(Debug, Clone, PartialEq)]
pub struct Environment {
    values: HashMap<String, Value>,
    parent: Option<Env>,
}

impl Environment {
    pub fn new() -> Env {
        Rc::new(RefCell::new(Self {
            values: HashMap::new(),
            parent: None,
        }))
    }

    pub fn with_parent(parent: Env) -> Env {
        Rc::new(RefCell::new(Self {
            values: HashMap::new(),
            parent: Some(parent),
        }))
    }

    pub fn define(&mut self, name: String, value: Value) {
        self.values.insert(name, value);
    }

    pub fn assign(&mut self, name: String, value: Value) {
        if self.values.contains_key(&name) {
            self.values.insert(name, value);
        } else if let Some(parent) = &self.parent {
            parent.borrow_mut().assign(name, value);
        } else {
            panic!()
        }
    }

    pub fn get(&self, name: String) -> Value {
        if let Some(val) = self.values.get(&name) {
            val.clone()
        } else if let Some(parent) = &self.parent {
            parent.borrow().get(name)
        } else {
            panic!()
        }
    }
}

pub struct Interpreter<'a> {
    source: String,
    program: &'a Program,
    type_env: &'a HashMap<TypeVarId, Type>,
    var_env: Env,
    method_registry: MethodRegistry,
}

impl<'a> Interpreter<'a> {
    pub fn new(program: &'a Program, type_env: &'a HashMap<TypeVarId, Type>, source: String) -> Self {
        let mut var_env = Environment::new();
        var_env
            .borrow_mut()
            .define("clock".to_string(), Value::Function(Rc::new(NativeFunction(clock_native))));
        var_env
            .borrow_mut()
            .define("print".to_string(), Value::Function(Rc::new(NativeFunction(print_native))));

        let method_registry = MethodRegistry::new();

        Self {
            source,
            program,
            type_env,
            var_env,
            method_registry,
        }
    }

    fn define_var(&mut self, name: String, value: Value) {
        self.var_env.borrow_mut().define(name, value);
    }

    fn get_var(&self, name: String) -> Value {
        self.var_env.borrow().get(name)
    }

    fn assign_var(&mut self, name: String, value: Value) {
        self.var_env.borrow_mut().assign(name, value);
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
                _ => panic!(),
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
                    env: self.var_env.clone(),
                }));
                self.define_var(fun_decl.node.ident.node.clone(), value)
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
            self.define_var(var_decl.node.ident.node.clone(), value);
        } else {
            self.define_var(var_decl.node.ident.node.clone(), Value::Nil);
        }

        Ok(())
    }

    fn fun_decl(&mut self, fun_decl: &Typed<FunDeclStmt>) -> Result<(), InterpreterError> {
        self.define_var(
            fun_decl.node.ident.node.clone(),
            Value::Function(Rc::new(UserFunction {
                name: Some(fun_decl.node.ident.node.clone()),
                params: Rc::new(fun_decl.node.params.clone()),
                body: Rc::new(fun_decl.node.body.clone()),
                env: self.var_env.clone(),
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
            Expr::MethodCall(method_call) => {
                let receiver = self.interpret_expr(&method_call.receiver)?;
                let method_name = &method_call.method.node;
                let receiver_ty = self.type_env.get(&method_call.receiver.type_id).expect("should work");

                let mut args = vec![receiver];
                for arg in &method_call.arguments {
                    args.push(self.interpret_expr(arg)?)
                }

                if let Some((_, function)) = self.method_registry.lookup_method(receiver_ty, method_name) {
                    match function {
                        NativeFunction(native_fn) => native_fn(args),
                        _ => panic!(),
                    }
                } else {
                    panic!()
                }
            }

            Expr::Literal(lit) => match &lit {
                LiteralExpr::Int(int) => Ok(Value::Int(*int)),
                LiteralExpr::Float(num) => Ok(Value::Float(*num)),
                LiteralExpr::String(str) => Ok(Value::String(Rc::from(str.as_str()))),
                LiteralExpr::Bool(bool) => Ok(Value::Bool(*bool)),
                LiteralExpr::Nil => Ok(Value::Nil),
                LiteralExpr::VecLiteral(vec) => {
                    let mut values = vec![];
                    for expr in vec {
                        values.push(self.interpret_expr(expr)?);
                    }
                    Ok(Value::Vec(Rc::new(RefCell::new(values))))
                }
            },

            Expr::Unary(unary) => {
                let right = self.interpret_expr(&unary.expr)?;
                let expr_type = self.type_env.get(&expr.type_id).unwrap();

                match unary.op.node {
                    UnaryOp::Bang => Ok(Value::Bool(!right.to_bool())),
                    UnaryOp::Minus => match expr_type {
                        Type::Int => Ok(Value::Int(-right.to_int())),
                        Type::Float => Ok(Value::Float(-right.to_float())),
                        _ => panic!(),
                    },
                }
            }

            Expr::Binary(binary) => {
                let left = self.interpret_expr(&binary.left)?;
                let right = self.interpret_expr(&binary.right)?;

                let expr_type = self.type_env.get(&expr.type_id).unwrap();

                match binary.op.node {
                    BinaryOp::Plus => match expr_type {
                        Type::Int => Ok(Value::Int(left.to_int() + right.to_int())),
                        Type::Float => Ok(Value::Float(left.to_float() + right.to_float())),
                        Type::String => {
                            let left_string = left.to_string();
                            let right_string = right.to_string();
                            let mut buffer = String::with_capacity(left_string.len() + right_string.len());
                            buffer.push_str(left_string);
                            buffer.push_str(right_string);

                            Ok(Value::String(Rc::from(buffer)))
                        }
                        _ => panic!("{:?}", expr_type),
                    },
                    BinaryOp::Minus => match expr_type {
                        Type::Int => Ok(Value::Int(left.to_int() - right.to_int())),
                        Type::Float => Ok(Value::Float(left.to_float() - right.to_float())),
                        _ => panic!(),
                    },
                    BinaryOp::Star => match expr_type {
                        Type::Int => Ok(Value::Int(left.to_int() * right.to_int())),
                        Type::Float => Ok(Value::Float(left.to_float() * right.to_float())),
                        _ => panic!(),
                    },
                    BinaryOp::Slash => match expr_type {
                        Type::Int => Ok(Value::Int(left.to_int() / right.to_int())),
                        Type::Float => {
                            if right.to_float() == 0.0 {
                                return Err(InterpreterError::RuntimeError(DivisionByZero {
                                    src: self.source.to_string(),
                                    span: expr.span,
                                }));
                            }
                            Ok(Value::Float(left.to_float() / right.to_float()))
                        }
                        _ => panic!(),
                    },
                    BinaryOp::Greater | BinaryOp::GreaterEqual | BinaryOp::Less | BinaryOp::LessEqual => match expr_type {
                        Type::Int => match binary.op.node {
                            BinaryOp::Greater => Ok(Value::Bool(left.to_int() > right.to_int())),
                            BinaryOp::GreaterEqual => Ok(Value::Bool(left.to_int() >= right.to_int())),
                            BinaryOp::Less => Ok(Value::Bool(left.to_int() < right.to_int())),
                            BinaryOp::LessEqual => Ok(Value::Bool(left.to_int() <= right.to_int())),
                            _ => unreachable!(),
                        },
                        Type::Float => match binary.op.node {
                            BinaryOp::Greater => Ok(Value::Bool(left.to_float() > right.to_float())),
                            BinaryOp::GreaterEqual => Ok(Value::Bool(left.to_float() >= right.to_float())),
                            BinaryOp::Less => Ok(Value::Bool(left.to_float() < right.to_float())),
                            BinaryOp::LessEqual => Ok(Value::Bool(left.to_float() <= right.to_float())),
                            _ => unreachable!(),
                        },
                        _ => panic!("{:?}", expr_type),
                    },
                    BinaryOp::EqualEqual => Ok(Value::Bool(left == right)),
                    BinaryOp::BangEqual => Ok(Value::Bool(left != right)),
                }
            }

            Expr::Grouping(grouping) => self.interpret_expr(grouping),
            Expr::Variable(variable) => Ok(self.get_var(variable.node.clone()).clone()),

            Expr::Assign(assign) => {
                let value = self.interpret_expr(&assign.value)?;
                self.assign_var(assign.target.node.clone(), value.clone());
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
                    UserFunction {
                        name: _,
                        params,
                        body,
                        env,
                    } => {
                        let local_env = Environment::with_parent(env.clone());

                        for (arg, param) in call.arguments.iter().zip(params.as_ref()) {
                            let value = self.interpret_expr(arg)?;
                            local_env.borrow_mut().define(param.name.node.clone(), value);
                        }

                        let old_env = self.var_env.clone();
                        self.var_env = local_env;

                        let return_val = match self.interpret_stmts(&body.node.statements) {
                            Ok(_) => {
                                if let Some(expr) = &body.node.expr {
                                    self.interpret_expr(expr)?
                                } else {
                                    Value::Nil
                                }
                            }
                            Err(InterpreterError::RuntimeError(err)) => return Err(InterpreterError::RuntimeError(err)),
                            Err(InterpreterError::ControlFlowError(ControlFlow::Return(val))) => val,
                        };

                        self.var_env = old_env;
                        Ok(return_val)
                    }
                }
            }

            Expr::Lambda(lambda) => Ok(Value::Function(Rc::new(UserFunction {
                name: None,
                params: Rc::new(lambda.parameters.clone()),
                body: Rc::new(lambda.body.deref().clone()),
                env: self.var_env.clone(),
            }))),
        }
    }
}
