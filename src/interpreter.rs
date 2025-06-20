use crate::MethodRegistry;
use crate::ir::{
    BinaryOp, BlockExpr, DefMap, Expr, ExprStmt, FunDeclStmt, IrNode, IrProgram, LiteralExpr, LogicalOp, ReturnStmt, Stmt, TypedIdent,
    UnaryOp, VarDeclStmt, WhileStmt,
};

use crate::builtins::{clock_native, print_native};
use crate::error::InterpreterError;
use crate::error::RuntimeError::DivisionByZero;
use crate::interpreter::Function::{NativeFunction, UserFunction};
use crate::ir::TypeVarId;
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
    Struct(Rc<RefCell<HashMap<String, Value>>>),
    Nil,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Function {
    NativeFunction(fn(Vec<Value>) -> Result<Value, InterpreterError>),
    UserFunction {
        name: Option<String>,
        params: Rc<Vec<TypedIdent>>,
        body: Rc<IrNode<BlockExpr>>,
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
            Value::Struct(fields) => {
                let fields_str: Vec<String> = fields
                    .borrow()
                    .iter()
                    .map(|(name, value)| format!("{}:{}", name, value.to_printable_value()))
                    .collect();
                format!("{{{}}}", fields_str.join(", "))
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

#[derive(Debug)]
pub enum InterpreterError {
    RuntimeError(RuntimeError),
    ControlFlowError(ControlFlow),
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
    program: &'a IrProgram,
    type_env: &'a HashMap<TypeVarId, ResolvedType>,
    var_env: Env,
    method_registry: &'a MethodRegistry<'a>,
    defs: &'a mut DefMap,
}

impl<'a> Interpreter<'a> {
    pub fn new(
        program: &'a IrProgram,
        type_env: &'a HashMap<TypeVarId, ResolvedType>,
        defs: &'a mut DefMap,
        method_registry: &'a MethodRegistry,
        source: String,
    ) -> Self {
        let var_env = Environment::new();
        var_env
            .borrow_mut()
            .define("clock".to_string(), Value::Function(Rc::new(NativeFunction(clock_native))));
        var_env
            .borrow_mut()
            .define("print".to_string(), Value::Function(Rc::new(NativeFunction(print_native))));

        Self {
            source,
            program,
            type_env,
            var_env,
            method_registry,
            defs,
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

    fn declare_stmt(&mut self, stmt: &IrNode<Stmt>) {
        match &stmt.node {
            Stmt::FunDecl(fun_decl) => {
                let value = Value::Function(Rc::new(UserFunction {
                    name: Some(fun_decl.ident.node.clone()),
                    params: Rc::new(fun_decl.params.clone()),
                    body: Rc::new(fun_decl.body.clone()),
                    env: self.var_env.clone(),
                }));
                self.define_var(fun_decl.ident.node.clone(), value)
            }
            _ => {}
        }
    }

    fn interpret_stmt(&mut self, stmt: &IrNode<Stmt>) -> Result<(), InterpreterError> {
        match &stmt.node {
            Stmt::ExprStmtNode(expr) => {
                self.interpret_expr(&expr.expr)?;
                Ok(())
            }
            Stmt::VarDecl(var_decl) => {
                if let Some(init) = &var_decl.initializer {
                    let value = self.interpret_expr(&init)?;
                    self.define_var(var_decl.ident.node.clone(), value);
                } else {
                    self.define_var(var_decl.ident.node.clone(), Value::Nil);
                }

                Ok(())
            }
            Stmt::FunDecl(fun_decl) => {
                self.define_var(
                    fun_decl.ident.node.clone(),
                    Value::Function(Rc::new(UserFunction {
                        name: Some(fun_decl.ident.node.clone()),
                        params: Rc::new(fun_decl.params.clone()),
                        body: Rc::new(fun_decl.body.clone()),
                        env: self.var_env.clone(),
                    })),
                );

                Ok(())
            }
            Stmt::StructDecl(_) => Ok(()),
            Stmt::While(while_stmt) => {
                let mut cond_value = self.interpret_expr(&while_stmt.condition)?.to_bool();
                while cond_value {
                    self.interpret_stmts(&while_stmt.body.node.statements)?;
                    cond_value = self.interpret_expr(&while_stmt.condition)?.to_bool();
                }

                Ok(())
            }
            Stmt::Return(return_stmt) => {
                let value = if let Some(expr) = &return_stmt.expr {
                    self.interpret_expr(expr)?
                } else {
                    Value::Nil
                };
                Err(InterpreterError::ControlFlowError(ControlFlow::Return(value)))
            }
        }
    }

    fn interpret_stmts(&mut self, stmts: &Vec<IrNode<Stmt>>) -> Result<(), InterpreterError> {
        for stmt in stmts {
            self.interpret_stmt(stmt)?;
        }
        Ok(())
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

    fn interpret_expr(&mut self, expr: &IrNode<Expr>) -> Result<Value, InterpreterError> {
        match &expr.node {
            Expr::FieldAssign(field_assign) => {
                let receiver = self.interpret_expr(&field_assign.receiver)?;
                let value = self.interpret_expr(&field_assign.value)?;

                match receiver {
                    Value::Struct(fields) => {
                        fields.borrow_mut().insert(field_assign.field.node.clone(), value.clone());
                        Ok(value)
                    }
                    _ => panic!(),
                }
            }
            Expr::FieldAccess(field_access) => {
                let receiver = self.interpret_expr(&field_access.receiver)?;

                match receiver {
                    Value::Struct(fields) => {
                        if let Some(value) = fields.borrow().get(&field_access.field.node) {
                            Ok(value.clone())
                        } else {
                            panic!()
                        }
                    }
                    _ => panic!(),
                }
            }
            Expr::StructInit(struct_init) => {
                let mut field_values = HashMap::new();
                for (field_name, field_expr) in &struct_init.fields {
                    let value = self.interpret_expr(field_expr)?;
                    field_values.insert(field_name.node.clone(), value);
                }
                Ok(Value::Struct(Rc::new(RefCell::new(field_values))))
            }
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
                let receiver_ty = self.type_env.get(&method_call.receiver.ir_id).expect("should work");

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
                let expr_type = self.type_env.get(&expr.ir_id).unwrap();

                match unary.op.node {
                    UnaryOp::Bang => Ok(Value::Bool(!right.to_bool())),
                    UnaryOp::Minus => match expr_type {
                        ResolvedType::Int => Ok(Value::Int(-right.to_int())),
                        ResolvedType::Float => Ok(Value::Float(-right.to_float())),
                        _ => panic!(),
                    },
                }
            }

            Expr::Binary(binary) => {
                let left = self.interpret_expr(&binary.left)?;
                let right = self.interpret_expr(&binary.right)?;

                let expr_type = self.type_env.get(&expr.ir_id).unwrap();

                match binary.op.node {
                    BinaryOp::Plus => match expr_type {
                        ResolvedType::Int => Ok(Value::Int(left.to_int() + right.to_int())),
                        ResolvedType::Float => Ok(Value::Float(left.to_float() + right.to_float())),
                        ResolvedType::String => {
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
                        ResolvedType::Int => Ok(Value::Int(left.to_int() - right.to_int())),
                        ResolvedType::Float => Ok(Value::Float(left.to_float() - right.to_float())),
                        _ => panic!(),
                    },
                    BinaryOp::Star => match expr_type {
                        ResolvedType::Int => Ok(Value::Int(left.to_int() * right.to_int())),
                        ResolvedType::Float => Ok(Value::Float(left.to_float() * right.to_float())),
                        _ => panic!(),
                    },
                    BinaryOp::Slash => match expr_type {
                        ResolvedType::Int => Ok(Value::Int(left.to_int() / right.to_int())),
                        ResolvedType::Float => {
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
                    BinaryOp::Greater | BinaryOp::GreaterEqual | BinaryOp::Less | BinaryOp::LessEqual => {
                        let operand_type = self.type_env.get(&binary.left.ir_id).unwrap();
                        match operand_type {
                            ResolvedType::Int => match binary.op.node {
                                BinaryOp::Greater => Ok(Value::Bool(left.to_int() > right.to_int())),
                                BinaryOp::GreaterEqual => Ok(Value::Bool(left.to_int() >= right.to_int())),
                                BinaryOp::Less => Ok(Value::Bool(left.to_int() < right.to_int())),
                                BinaryOp::LessEqual => Ok(Value::Bool(left.to_int() <= right.to_int())),
                                _ => unreachable!(),
                            },
                            ResolvedType::Float => match binary.op.node {
                                BinaryOp::Greater => Ok(Value::Bool(left.to_float() > right.to_float())),
                                BinaryOp::GreaterEqual => Ok(Value::Bool(left.to_float() >= right.to_float())),
                                BinaryOp::Less => Ok(Value::Bool(left.to_float() < right.to_float())),
                                BinaryOp::LessEqual => Ok(Value::Bool(left.to_float() <= right.to_float())),
                                _ => unreachable!(),
                            },
                            _ => panic!("{:?}", expr_type),
                        }
                    }
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
