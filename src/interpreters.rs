use crate::ast::{
    BinaryOp, BlockStmt, Expr, FunDeclStmt, IfStmt, LiteralExpr, LogicalOp, Parameter, Program, ReturnStmt, Stmt, Typed, UnaryOp,
    VarDeclStmt, WhileStmt,
};
use crate::builtins::clock_native;
use crate::interpreters::Function::{NativeFunction, UserFunction};
use crate::type_inferrer::{Type, TypeVarId};
use miette::Report;
use std::cmp::PartialEq;
use std::collections::HashMap;
use std::fmt;
use std::ops::Deref;
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Number(f64),
    String(Rc<str>),
    Bool(bool),
    Function(Rc<Function>),
    Nil,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Function {
    NativeFunction(fn(Vec<Value>) -> Result<Value, String>),
    UserFunction {
        params: Rc<Vec<Typed<Parameter>>>,
        body: Rc<Typed<BlockStmt>>,
    },
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Number(num) => write!(f, "{num}"),
            Value::String(str) => write!(f, "{str}"),
            Value::Bool(bool) => write!(f, "{bool}"),
            Value::Function(function) => match function.as_ref() {
                NativeFunction(native_fun) => write!(f, "nativeFn<{:?}", native_fun),
                UserFunction { params, body: _ } => write!(f, "Fn<({params:?})"),
            },
            Value::Nil => write!(f, "nil"),
        }
    }
}

impl Value {
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

pub struct InterpreterResult<'a> {
    pub errors: &'a Vec<Report>,
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
    errors: Vec<Report>,
}

impl<'a> Interpreter<'a> {
    pub fn new(program: &'a Program, type_env: &'a HashMap<TypeVarId, Type>, source: String) -> Self {
        let mut var_env = HashMap::new();
        var_env.insert("clock".to_string(), Value::Function(Rc::new(NativeFunction(clock_native))));

        Self {
            source,
            program,
            type_env,
            var_env: vec![var_env],
            errors: vec![],
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
            match self.interpret_stmt(stmt) {
                Ok(_) => {}
                Err(ControlFlow::Return(..)) => {
                    panic!()
                }
            }
        }
        InterpreterResult { errors: &self.errors }
    }

    fn declare_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::FunDecl(fun_decl) => {
                let value = Value::Function(Rc::new(UserFunction {
                    params: Rc::new(fun_decl.node.params.clone()),
                    body: Rc::new(fun_decl.node.body.clone()),
                }));
                self.insert_var(fun_decl.node.ident.node.clone(), value);
            }
            _ => {}
        }
    }

    fn interpret_stmt(&mut self, stmt: &Stmt) -> Result<(), ControlFlow> {
        match stmt {
            Stmt::ExprStmt(expr) => self.expr_stmt(expr),
            Stmt::PrintStmt(print) => self.print_stmt(print),
            Stmt::VarDecl(var_decl) => self.var_decl(var_decl),
            Stmt::FunDecl(fun_decl) => self.fun_decl(fun_decl),
            Stmt::Block(block) => self.block(block),
            Stmt::If(if_stmt) => self.if_stmt(if_stmt),
            Stmt::While(while_stmt) => self.while_stmt(while_stmt),
            Stmt::Return(return_stmt) => Err(self.return_stmt(return_stmt)),
        }
    }

    fn expr_stmt(&mut self, expr: &Typed<Expr>) -> Result<(), ControlFlow> {
        self.interpret_expr(&expr);
        Ok(())
    }

    fn print_stmt(&mut self, print: &Typed<Expr>) -> Result<(), ControlFlow> {
        let value = self.interpret_expr(&print);
        println!("{value}");
        Ok(())
    }

    fn var_decl(&mut self, var_decl: &Typed<VarDeclStmt>) -> Result<(), ControlFlow> {
        if let Some(init) = &var_decl.node.initializer {
            let value = self.interpret_expr(&init);
            self.insert_var(var_decl.node.ident.node.clone(), value);
        } else {
            self.insert_var(var_decl.node.ident.node.clone(), Value::Nil);
        }

        Ok(())
    }

    fn fun_decl(&mut self, fun_decl: &Typed<FunDeclStmt>) -> Result<(), ControlFlow> {
        self.insert_var(
            fun_decl.node.ident.node.clone(),
            Value::Function(Rc::new(UserFunction {
                params: Rc::new(fun_decl.node.params.clone()),
                body: Rc::new(fun_decl.node.body.clone()),
            })),
        );

        Ok(())
    }

    fn block(&mut self, block: &Typed<BlockStmt>) -> Result<(), ControlFlow> {
        for stmt in &block.node.statements {
            self.interpret_stmt(stmt)?;
        }
        Ok(())
    }

    fn if_stmt(&mut self, if_stmt: &Typed<IfStmt>) -> Result<(), ControlFlow> {
        let cond_value = self.interpret_expr(&if_stmt.node.condition);

        if cond_value.to_bool() {
            self.block(&if_stmt.node.then_branch)?;
        } else if let Some(else_branch) = &if_stmt.node.else_branch {
            self.block(else_branch)?;
        }

        Ok(())
    }

    fn while_stmt(&mut self, while_stmt: &Typed<WhileStmt>) -> Result<(), ControlFlow> {
        let mut cond_value = self.interpret_expr(&while_stmt.node.condition).to_bool();
        while cond_value {
            self.block(&while_stmt.node.body)?;
            cond_value = self.interpret_expr(&while_stmt.node.condition).to_bool();
        }

        Ok(())
    }

    fn return_stmt(&mut self, return_stmt: &Typed<ReturnStmt>) -> ControlFlow {
        let value = if let Some(expr) = &return_stmt.node.expr {
            self.interpret_expr(expr)
        } else {
            Value::Nil
        };
        ControlFlow::Return(value)
    }

    fn interpret_expr(&mut self, expr: &Typed<Expr>) -> Value {
        match &expr.node {
            Expr::Literal(lit) => match &lit {
                LiteralExpr::Number(num) => Value::Number(*num),
                LiteralExpr::String(str) => Value::String(Rc::from(str.as_str())),
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

                let left_type = self.type_env.get(&expr.type_id).unwrap();

                match binary.op.node {
                    BinaryOp::Plus => match left_type {
                        Type::Float => Value::Number(left.to_number() + right.to_number()),
                        Type::String => {
                            let left_string = left.to_string();
                            let right_string = right.to_string();
                            let mut buffer = String::with_capacity(left_string.len() + right_string.len());
                            buffer.push_str(left_string);
                            buffer.push_str(right_string);

                            Value::String(buffer.into())
                        }
                        _ => panic!(),
                    },
                    BinaryOp::Minus => Value::Number(left.to_number() - right.to_number()),
                    BinaryOp::Star => Value::Number(left.to_number() * right.to_number()),
                    BinaryOp::Slash => Value::Number(left.to_number() / right.to_number()),
                    BinaryOp::Greater => Value::Bool(left.to_number() > right.to_number()),
                    BinaryOp::GreaterEqual => Value::Bool(left.to_number() >= right.to_number()),
                    BinaryOp::Less => Value::Bool(left.to_number() < right.to_number()),
                    BinaryOp::LessEqual => Value::Bool(left.to_number() <= right.to_number()),
                    BinaryOp::EqualEqual => Value::Bool(left == right),
                    BinaryOp::BangEqual => Value::Bool(left != right),
                }
            }

            Expr::Grouping(grouping) => self.interpret_expr(grouping),
            Expr::Variable(variable) => self.get_var(&variable.node).clone(),

            Expr::Assign(assign) => {
                let value = self.interpret_expr(&assign.value);
                self.insert_var(assign.target.node.clone(), value.clone());
                value
            }

            Expr::Logical(logical) => {
                let left = self.interpret_expr(&logical.left);
                let right = self.interpret_expr(&logical.right);

                match logical.op.node {
                    LogicalOp::And => Value::Bool(left.to_bool() && right.to_bool()),
                    LogicalOp::Or => Value::Bool(left.to_bool() || right.to_bool()),
                }
            }

            Expr::Call(call) => {
                let callee = self.interpret_expr(call.callee.deref());

                let func = callee.to_fn();

                match func {
                    NativeFunction(native_fun) => native_fun(vec![]).expect("error handling for native functions not yet implemented"),
                    UserFunction { params, body } => {
                        self.var_env.push(HashMap::new());
                        for (arg, param) in call.arguments.iter().zip(params.as_ref()) {
                            let value = self.interpret_expr(arg);
                            self.insert_var(param.node.name.node.clone(), value);
                        }
                        let return_val = if let Err(ControlFlow::Return(val)) = self.block(&body) {
                            val
                        } else {
                            Value::Nil
                        };

                        self.var_env.pop();
                        return_val
                    }
                }
            }

            Expr::Lambda(lambda) => Value::Function(Rc::new(UserFunction {
                params: Rc::new(lambda.parameters.clone()),
                body: Rc::new(lambda.body.clone()),
            })),
        }
    }
}
