use crate::MethodRegistry;
use crate::ast::{
    BinaryOp, BlockExpr, Expr, ExprStmt, FunDeclStmt, LiteralExpr, Program, ReturnStmt, Stmt, Typed, UnaryOp, VarDeclStmt, WhileStmt,
};
use crate::error::TypeInferrerError;
use crate::error::TypeInferrerError::{NonBooleanCondition, NotCallable, TypeMismatch, UnknownMethod, WrongArgumentCount};
use crate::type_inferrer::Type::TypeVar;
use miette::{Report, SourceOffset, SourceSpan};
use std::collections::HashMap;
use std::hash::Hash;
use std::ops::Deref;

pub type TypeVarId = usize;

#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub enum Type {
    Int,
    Float,
    Bool,
    String,
    Nil,
    Function { params: Vec<Type>, return_ty: Box<Type> },
    Vec(Box<Type>),
    TypeVar(TypeVarId),
    Generic(String),
}

#[derive(Debug, Clone, PartialEq)]
pub struct VarEnv {
    scopes: Vec<HashMap<String, TypeVarId>>,
}

impl VarEnv {
    pub fn new() -> Self {
        Self {
            scopes: vec![HashMap::new()],
        }
    }

    pub fn enter_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    pub fn exit_scope(&mut self) {
        self.scopes.pop();
    }

    pub fn insert(&mut self, name: String, ty: TypeVarId) {
        self.scopes.last_mut().unwrap().insert(name, ty);
    }

    pub fn lookup(&mut self, name: &str) -> Option<TypeVarId> {
        for scope in self.scopes.iter().rev() {
            if let Some(id) = scope.get(name) {
                return Some(*id);
            }
        }
        None
    }
}

pub struct TypeInferrer<'a> {
    program: &'a Program,
    source: String,
    errors: Vec<Report>,
    current_function_return_ty: Option<Type>,
    pub var_env: VarEnv,
    pub type_env: HashMap<TypeVarId, Type>,
    method_registry: MethodRegistry,
}

pub struct TypeInferenceResult<'a> {
    pub errors: &'a Vec<Report>,
    pub type_env: &'a HashMap<TypeVarId, Type>,
}

impl<'a> TypeInferrer<'a> {
    pub fn new(ast: &'a Program, source: String) -> Self {
        let method_registry = MethodRegistry::new();

        Self {
            program: ast,
            source,
            errors: vec![],
            current_function_return_ty: None,
            var_env: VarEnv::new(),
            type_env: HashMap::new(),
            method_registry,
        }
    }

    fn report(&mut self, error: TypeInferrerError) {
        self.errors.push(error.into());
    }
    pub fn lookup_type(&mut self, ty: &Type) -> Type {
        match ty {
            TypeVar(id) => {
                if let Some(inner) = self.type_env.get(id).cloned() {
                    let resolved = self.lookup_type(&inner);
                    self.type_env.insert(*id, resolved.clone());
                    resolved
                } else {
                    ty.clone()
                }
            }
            Type::Vec(elem_ty) => {
                let resolved_elem = self.lookup_type(elem_ty);
                Type::Vec(Box::new(resolved_elem))
            }
            _ => ty.clone(),
        }
    }

    fn substitute(&mut self, ty: &Type, substitutions: &HashMap<String, Type>) -> Type {
        let t = self.lookup_type(ty);

        match t {
            Type::Float | Type::Bool | Type::String | Type::Nil | Type::Int => t,
            Type::Generic(ref name) => substitutions.get(name).cloned().unwrap_or(t),
            Type::Function { params, return_ty } => {
                let new_params = params.iter().map(|p| self.substitute(p, substitutions)).collect();
                let new_return = self.substitute(&return_ty, substitutions);

                Type::Function {
                    params: new_params,
                    return_ty: Box::new(new_return),
                }
            }
            Type::Vec(elem_ty) => {
                let new_elem = self.substitute(elem_ty.deref(), substitutions);
                match new_elem {
                    Type::Generic(ref name) => {
                        if let Some(concrete_ty) = substitutions.get(name) {
                            Type::Vec(Box::new(concrete_ty.clone()))
                        } else {
                            Type::Vec(Box::new(new_elem))
                        }
                    }
                    _ => Type::Vec(Box::new(new_elem)),
                }
            }
            TypeVar(id) => {
                if let Some(resolved) = self.type_env.get(&id).cloned() {
                    self.substitute(&resolved, substitutions)
                } else {
                    t
                }
            }
        }
    }

    fn unify(&mut self, found: Type, expected: Type, span: SourceSpan) -> Result<Type, TypeInferrerError> {
        let found_ty = self.lookup_type(&found);
        let expected_ty = self.lookup_type(&expected);

        match (found_ty, expected_ty) {
            (Type::Int, Type::Int) => Ok(Type::Int),
            (Type::Float, Type::Float) => Ok(Type::Float),
            (Type::String, Type::String) => Ok(Type::String),
            (Type::Bool, Type::Bool) => Ok(Type::Bool),
            (Type::Nil, Type::Nil) => Ok(Type::Nil),

            (Type::Vec(elem_ty1), Type::Vec(elem_ty2)) => {
                let unified_elem = self.unify(*elem_ty1.clone(), *elem_ty2, span)?;
                Ok(Type::Vec(Box::new(unified_elem)))
            }

            (Type::Function { params: p1, return_ty: r1 }, Type::Function { params: p2, return_ty: r2 }) => {
                if p1.len() != p2.len() {
                    return Err(TypeMismatch {
                        src: self.source.clone(),
                        span,
                        expected: Type::Function { params: p1, return_ty: r1 },
                        found: Type::Function { params: p2, return_ty: r2 },
                    });
                }

                for (param1, param2) in p1.iter().zip(p2.iter()) {
                    self.unify(param1.clone(), param2.clone(), span)?;
                }

                self.unify(*r1.clone(), *r2, span)?;
                Ok(Type::Function { params: p1, return_ty: r1 })
            }

            (ty, TypeVar(id)) | (TypeVar(id), ty) => {
                self.type_env.insert(id, ty);
                Ok(TypeVar(id))
            }

            (t1, t2) => Err(TypeMismatch {
                src: self.source.clone(),
                span,
                expected: t2,
                found: t1,
            }),
        }
    }

    pub fn infer(&mut self) -> TypeInferenceResult {
        self.declare_native_functions();

        for stmt in &self.program.statements {
            self.declare_stmt(stmt);
        }

        for stmt in &self.program.statements {
            if let Err(err) = self.infer_stmt(stmt) {
                self.report(err);
            }
        }

        TypeInferenceResult {
            errors: &self.errors,
            type_env: &self.type_env,
        }
    }

    fn fresh_type_var(&mut self) -> TypeVarId {
        let typed = Typed::new(
            LiteralExpr::String("if you see this something is wrong".to_string()),
            SourceSpan::new(SourceOffset::from(0), 0),
        );
        typed.type_id
    }

    fn declare_native_functions(&mut self) {
        let clock_type = Type::Function {
            params: vec![],
            return_ty: Box::new(Type::Float),
        };

        let clock_type_id = self.fresh_type_var();
        self.type_env.insert(clock_type_id, clock_type);
        self.var_env.insert("clock".to_string(), clock_type_id);

        let print_type = Type::Function {
            params: vec![Type::Generic("T".to_string())],
            return_ty: Box::new(Type::Nil),
        };
        let print_type_id = self.fresh_type_var();
        self.type_env.insert(print_type_id, print_type);
        self.var_env.insert("print".to_string(), print_type_id);
    }

    fn declare_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::FunDecl(fun_decl) => {
                let name = &fun_decl.node.ident.node;

                let fn_type = Type::Function {
                    params: fun_decl.node.params.iter().map(|p| p.type_annotation.node.clone()).collect(),
                    return_ty: Box::new(fun_decl.node.return_type.node.clone()),
                };

                self.type_env.insert(fun_decl.node.ident.type_id, fn_type);
                self.var_env.insert(name.clone(), fun_decl.node.ident.type_id);
            }
            _ => {}
        }
    }

    fn infer_stmt(&mut self, stmt: &Stmt) -> Result<(), TypeInferrerError> {
        match stmt {
            Stmt::ExprStmtNode(expr_stmt) => self.infer_expr_stmt(expr_stmt),
            Stmt::VarDecl(var_decl) => self.infer_var_decl(var_decl),
            Stmt::FunDecl(fun_decl) => self.infer_fun_decl(fun_decl),
            Stmt::While(while_stmt) => self.infer_while_stmt(while_stmt),
            Stmt::Return(return_stmt) => self.infer_return_stmt(return_stmt),
        }
    }

    fn infer_expr_stmt(&mut self, expr_stmt: &Typed<ExprStmt>) -> Result<(), TypeInferrerError> {
        self.infer_expr(&expr_stmt.node.expr)?;
        Ok(())
    }

    fn infer_var_decl(&mut self, var_decl: &Typed<VarDeclStmt>) -> Result<(), TypeInferrerError> {
        let var_decl_id = var_decl.node.ident.type_id.clone();
        self.var_env.insert(var_decl.node.ident.node.clone(), var_decl_id);

        if let Some(type_annotation) = &var_decl.node.type_annotation {
            self.type_env.insert(var_decl_id, type_annotation.node.clone());
        }
        if let Some(init) = &var_decl.node.initializer {
            let init_type = match &init.node {
                Expr::Literal(LiteralExpr::VecLiteral(elements)) if elements.is_empty() => {
                    if let Some(type_annotation) = &var_decl.node.type_annotation {
                        type_annotation.node.clone()
                    } else {
                        return Err(TypeInferrerError::CannotInferType {
                            src: self.source.clone(),
                            span: var_decl.span,
                            name: "Vec".to_string(),
                        });
                    }
                }
                _ => self.infer_expr(init)?,
            };
            self.unify(TypeVar(var_decl_id), init_type, var_decl.node.ident.span)?;
        }

        Ok(())
    }

    fn infer_fun_decl(&mut self, fun_decl: &Typed<FunDeclStmt>) -> Result<(), TypeInferrerError> {
        let name = &fun_decl.node.ident.node;

        let fn_type = Type::Function {
            params: fun_decl.node.params.iter().map(|p| p.type_annotation.node.clone()).collect(),
            return_ty: Box::new(fun_decl.node.return_type.node.clone()),
        };

        self.type_env.insert(fun_decl.node.ident.type_id, fn_type);
        self.var_env.insert(name.clone(), fun_decl.node.ident.type_id);

        if fun_decl.node.generics.is_empty() {
            self.var_env.enter_scope();

            for param in &fun_decl.node.params {
                let param_id = param.name.type_id;
                self.type_env.insert(param_id, param.type_annotation.node.clone());
                self.var_env.insert(param.name.node.clone(), param_id);
            }

            let old_ret_ty = self.current_function_return_ty.clone();
            self.current_function_return_ty = Some(fun_decl.node.return_type.node.clone());

            self.infer_stmts(&fun_decl.node.body.node.statements)?;

            if let Some(expr) = &fun_decl.node.body.node.expr {
                let body_ty = self.infer_expr(expr)?;
                self.unify(fun_decl.node.return_type.node.clone(), body_ty, fun_decl.node.ident.span)?;
            } else if !fun_decl
                .node
                .body
                .node
                .statements
                .iter()
                .any(|stmt| matches!(stmt, Stmt::Return(_)))
            {
                self.unify(fun_decl.node.return_type.node.clone(), Type::Nil, fun_decl.node.return_type.span)?;
            }

            self.current_function_return_ty = old_ret_ty;
            self.var_env.exit_scope()
        }
        Ok(())
    }

    fn infer_stmts(&mut self, stmts: &Vec<Stmt>) -> Result<(), TypeInferrerError> {
        self.var_env.enter_scope();

        for stmt in stmts {
            self.infer_stmt(stmt)?;
        }

        self.var_env.exit_scope();

        Ok(())
    }

    fn infer_block_expr(&mut self, block: &BlockExpr) -> Result<Type, TypeInferrerError> {
        self.var_env.enter_scope();

        for stmt in &block.statements {
            self.infer_stmt(stmt)?;
        }

        let return_ty = if let Some(expr) = &block.expr {
            Ok(self.infer_expr(expr)?)
        } else {
            Ok(Type::Nil)
        };

        self.var_env.exit_scope();
        return_ty
    }

    fn infer_while_stmt(&mut self, while_stmt: &Typed<WhileStmt>) -> Result<(), TypeInferrerError> {
        let condition_ty = self.infer_expr(&while_stmt.node.condition)?;

        match self.lookup_type(&condition_ty) {
            Type::Bool => Ok(()),
            found => Err(NonBooleanCondition {
                src: self.source.clone(),
                span: while_stmt.node.condition.span,
                found,
            }),
        }?;
        self.infer_stmts(&while_stmt.node.body.node.statements)?;

        Ok(())
    }

    fn infer_return_stmt(&mut self, return_stmt: &Typed<ReturnStmt>) -> Result<(), TypeInferrerError> {
        if let Some(ret_expr) = &return_stmt.node.expr {
            let ret_id = self.infer_expr(ret_expr)?;
            let ret_ty = self.lookup_type(&ret_id);

            if let Some(expected_ty) = &self.current_function_return_ty {
                self.unify(ret_ty, expected_ty.clone(), ret_expr.span)?;
            }
        } else {
            let ret_ty = Type::Nil;
            if let Some(expected_ty) = &self.current_function_return_ty {
                self.unify(ret_ty, expected_ty.clone(), return_stmt.span)?;
            }
        }

        Ok(())
    }

    fn collect_substitutions(&self, param_ty: &Type, arg_ty: &Type, substitutions: &mut HashMap<String, Type>) {
        match (param_ty, arg_ty) {
            (Type::Vec(param_elem), Type::Vec(arg_elem)) => {
                self.collect_substitutions(param_elem, arg_elem, substitutions);
            }
            (Type::Vec(elem_ty), _) => {
                if let Type::Generic(name) = elem_ty.deref() {
                    substitutions.insert(name.clone(), arg_ty.clone());
                }
            }
            (Type::Generic(name), _) => {
                substitutions.insert(name.clone(), arg_ty.clone());
            }
            _ => {}
        }
    }

    fn handle_parameters(
        &mut self,
        params: &Vec<Type>,
        args: &Vec<Typed<Expr>>,
        span: SourceSpan,
    ) -> Result<HashMap<String, Type>, TypeInferrerError> {
        if params.len() != args.len() {
            return Err(WrongArgumentCount {
                src: self.source.clone(),
                span,
                expected: params.len(),
                found: args.len(),
            });
        }

        let mut substitutions: HashMap<String, Type> = HashMap::new();

        for (arg, param_ty) in args.iter().zip(params.iter()) {
            let arg_ty = self.infer_expr(arg)?;
            let arg_ty = self.lookup_type(&arg_ty);
            self.collect_substitutions(param_ty, &arg_ty, &mut substitutions);
        }

        for (arg, param_ty) in args.iter().zip(params.iter()) {
            let arg_ty = self.infer_expr(arg)?;
            let arg_ty = self.lookup_type(&arg_ty);
            let substituted = self.substitute(param_ty, &substitutions);
            self.unify(substituted, arg_ty, arg.span)?;
        }

        Ok(substitutions)
    }

    fn infer_expr(&mut self, expr: &Typed<Expr>) -> Result<Type, TypeInferrerError> {
        match &expr.node {
            Expr::Literal(literal_expr) => {
                let ty = match literal_expr {
                    LiteralExpr::Int(_) => Type::Int,
                    LiteralExpr::Float(_) => Type::Float,
                    LiteralExpr::String(_) => Type::String,
                    LiteralExpr::Bool(_) => Type::Bool,
                    LiteralExpr::Nil => Type::Nil,
                    LiteralExpr::VecLiteral(vec) => {
                        if vec.is_empty() {
                            return Err(TypeInferrerError::CannotInferType {
                                src: self.source.clone(),
                                span: expr.span,
                                name: "Vec".to_string(),
                            });
                        }

                        let first_elem_ty = self.infer_expr(&vec[0])?;
                        for elem in vec.iter().skip(1) {
                            let elem_ty = self.infer_expr(elem)?;
                            self.unify(elem_ty, first_elem_ty.clone(), elem.span)?;
                        }

                        Type::Vec(Box::new(first_elem_ty))
                    }
                };

                self.type_env.insert(expr.type_id, ty);
                Ok(TypeVar(expr.type_id))
            }

            Expr::Block(block) => self.infer_block_expr(block),

            Expr::If(if_expr) => {
                let condition_ty = self.infer_expr(&if_expr.condition)?;

                match self.lookup_type(&condition_ty) {
                    Type::Bool => Ok(()),
                    found => Err(NonBooleanCondition {
                        src: self.source.clone(),
                        span: if_expr.condition.span,
                        found,
                    }),
                }?;

                let then_return_ty = self.infer_block_expr(&if_expr.then_branch.node)?;
                let else_return_ty = if let Some(else_branch) = &if_expr.else_branch {
                    self.infer_block_expr(&else_branch.node)?
                } else {
                    Type::Nil
                };

                let return_ty = self.unify(then_return_ty, else_return_ty, if_expr.then_branch.span)?;
                Ok(return_ty)
            }
            Expr::MethodCall(method_call) => {
                let receiver_ty = self.infer_expr(&method_call.receiver)?;
                let receiver_ty = self.lookup_type(&receiver_ty);
                self.type_env.insert(method_call.receiver.type_id, receiver_ty.clone());

                if let Some((method_ty, _)) = self.method_registry.lookup_method(&receiver_ty, &method_call.method.node).cloned() {
                    match method_ty {
                        Type::Function { params, return_ty } => {
                            if params.len() != method_call.arguments.len() {
                                return Err(TypeMismatch {
                                    src: self.source.clone(),
                                    span: method_call.method.span,
                                    expected: Type::Function {
                                        params: params.clone(),
                                        return_ty: return_ty.clone(),
                                    },
                                    found: Type::Function {
                                        params: method_call.arguments.iter().map(|_| TypeVar(0)).collect(),
                                        return_ty: Box::new(TypeVar(0)),
                                    },
                                });
                            }
                            let mut substitutions = HashMap::new();

                            if let Type::Vec(elem_ty) = &receiver_ty {
                                substitutions.insert("T".to_string(), elem_ty.as_ref().clone());
                            }

                            for (param, arg) in params.iter().zip(&method_call.arguments) {
                                let arg_ty = self.infer_expr(arg)?;
                                let arg_ty = self.lookup_type(&arg_ty);
                                let substituted_param = self.substitute(param, &substitutions);
                                self.unify(arg_ty, substituted_param, arg.span)?;
                            }

                            let return_ty = self.substitute(&return_ty, &substitutions);
                            self.type_env.insert(expr.type_id, return_ty);
                            Ok(TypeVar(expr.type_id))
                        }
                        _ => unreachable!(),
                    }
                } else {
                    Err(UnknownMethod {
                        src: self.source.clone(),
                        span: expr.span,
                        method: method_call.method.node.clone(),
                        base_type: receiver_ty,
                    })
                }
            }
            Expr::Unary(unary_expr) => {
                let right_ty = self.infer_expr(unary_expr.expr.deref())?;
                let result_ty = match unary_expr.op.node {
                    UnaryOp::Bang => self.unify(right_ty, Type::Bool, unary_expr.expr.span)?,
                    UnaryOp::Minus => self.unify(right_ty, Type::Float, unary_expr.expr.span)?,
                };

                self.type_env.insert(unary_expr.expr.type_id, result_ty.clone());
                Ok(TypeVar(unary_expr.expr.type_id))
            }
            Expr::Binary(binary_expr) => {
                let left = self.infer_expr(binary_expr.left.deref())?;
                let right = self.infer_expr(binary_expr.right.deref())?;

                let result_ty = match binary_expr.op.node {
                    BinaryOp::Plus => {
                        let left_ty = self.lookup_type(&left);
                        let right_ty = self.lookup_type(&right);
                        match (left_ty.clone(), right_ty.clone()) {
                            (Type::Int, Type::Int) => Type::Int,
                            (Type::Float, Type::Float) => Type::Float,
                            (Type::String, Type::String) => Type::String,
                            _ => {
                                return Err(TypeMismatch {
                                    src: self.source.clone(),
                                    span: binary_expr.right.span,
                                    expected: left_ty,
                                    found: right_ty,
                                });
                            }
                        }
                    }
                    BinaryOp::Minus => {
                        let left_ty = self.lookup_type(&left);
                        let right_ty = self.lookup_type(&right);
                        match (left_ty.clone(), right_ty.clone()) {
                            (Type::Int, Type::Int) => Type::Int,
                            (Type::Float, Type::Float) => Type::Float,
                            _ => {
                                return Err(TypeMismatch {
                                    src: self.source.clone(),
                                    span: binary_expr.right.span,
                                    expected: left_ty,
                                    found: right_ty,
                                });
                            }
                        }
                    }
                    BinaryOp::Star | BinaryOp::Slash => {
                        let left_ty = self.lookup_type(&left);
                        let right_ty = self.lookup_type(&right);
                        match (left_ty.clone(), right_ty.clone()) {
                            (Type::Int, Type::Int) => Type::Int,
                            (Type::Float, Type::Float) => Type::Float,
                            _ => {
                                return Err(TypeMismatch {
                                    src: self.source.clone(),
                                    span: binary_expr.right.span,
                                    expected: left_ty,
                                    found: right_ty,
                                });
                            }
                        }
                    }
                    BinaryOp::Greater | BinaryOp::GreaterEqual | BinaryOp::Less | BinaryOp::LessEqual => {
                        let left_ty = self.lookup_type(&left);
                        let right_ty = self.lookup_type(&right);
                        match (left_ty.clone(), right_ty.clone()) {
                            (Type::Int, Type::Int) => Type::Bool,
                            (Type::Float, Type::Float) => Type::Bool,
                            _ => {
                                return Err(TypeMismatch {
                                    src: self.source.clone(),
                                    span: binary_expr.right.span,
                                    expected: left_ty,
                                    found: right_ty,
                                });
                            }
                        }
                    }
                    BinaryOp::EqualEqual | BinaryOp::BangEqual => {
                        self.unify(left, right, binary_expr.right.span)?;
                        Type::Bool
                    }
                };

                self.type_env.insert(expr.type_id, result_ty);
                Ok(TypeVar(expr.type_id))
            }
            Expr::Grouping(grouping) => self.infer_expr(grouping.deref()),
            Expr::Variable(variable_expr) => {
                let var_id = self.var_env.lookup(variable_expr.node.as_str()).unwrap();

                Ok(TypeVar(var_id.clone()))
            }
            Expr::Assign(assign_expr) => {
                let right_ty = self.infer_expr(assign_expr.value.deref())?;
                let left_var = self.var_env.lookup(assign_expr.target.node.as_str()).unwrap();

                self.unify(TypeVar(left_var.clone()), right_ty.clone(), assign_expr.value.deref().span)?;

                self.type_env.insert(expr.type_id, right_ty);
                Ok(TypeVar(expr.type_id))
            }
            Expr::Logical(logical_expr) => {
                let left = self.infer_expr(logical_expr.left.deref())?;
                let right = self.infer_expr(logical_expr.right.deref())?;

                self.unify(left, Type::Bool, logical_expr.left.span)?;
                self.unify(right, Type::Bool, logical_expr.right.span)?;

                self.type_env.insert(expr.type_id, Type::Bool);
                Ok(TypeVar(expr.type_id))
            }
            Expr::Call(call_expr) => {
                let callee_ty = self.infer_expr(call_expr.callee.deref())?;
                let callee_ty = self.lookup_type(&callee_ty);

                match callee_ty {
                    Type::Function { params, return_ty } => {
                        let substitutions = self.handle_parameters(&params, &call_expr.arguments, call_expr.callee.span)?;

                        self.var_env.enter_scope();

                        if let Expr::Variable(var) = &call_expr.callee.node {
                            if let Some(fn_decl) = self.program.statements.iter().find(|stmt| {
                                if let Stmt::FunDecl(fd) = stmt {
                                    fd.node.ident.node == var.node
                                } else {
                                    false
                                }
                            }) {
                                if let Stmt::FunDecl(fd) = fn_decl {
                                    for (param, param_ty) in fd.node.params.iter().zip(params.iter()) {
                                        let substituted_ty = self.substitute(param_ty, &substitutions);
                                        self.type_env.insert(param.name.type_id, substituted_ty);
                                        self.var_env.insert(param.name.node.clone(), param.name.type_id);
                                    }

                                    let substituted_return = self.substitute(&fd.node.return_type.node, &substitutions);
                                    let old_return_ty = self.current_function_return_ty.clone();
                                    self.current_function_return_ty = Some(substituted_return.clone());

                                    self.infer_stmts(&fd.node.body.node.statements)?;

                                    if let Some(expr) = &fd.node.body.node.expr {
                                        let body_ty = self.infer_expr(expr)?;
                                        self.unify(fd.node.return_type.node.clone(), body_ty, fd.node.ident.span)?;
                                    } else if !fd.node.body.node.statements.iter().any(|stmt| matches!(stmt, Stmt::Return(_))) {
                                        self.unify(Type::Nil, fd.node.return_type.node.clone(), fd.node.return_type.span)?;
                                    }
                                    self.current_function_return_ty = old_return_ty;
                                }
                            }
                        }

                        self.var_env.exit_scope();

                        let concrete_return = self.substitute(&return_ty, &substitutions);
                        self.type_env.insert(expr.type_id, concrete_return.clone());
                        Ok(TypeVar(expr.type_id))
                    }
                    found => Err(NotCallable {
                        src: self.source.clone(),
                        span: expr.span,
                        found,
                    }),
                }
            }
            Expr::Lambda(lambda) => {
                self.var_env.enter_scope();

                let param_types: Vec<Type> = lambda.parameters.iter().map(|p| p.type_annotation.node.clone()).collect();

                let fn_type = Type::Function {
                    params: param_types.clone(),
                    return_ty: Box::new(lambda.return_type.node.clone()),
                };

                self.type_env.insert(expr.type_id, fn_type.clone());

                for param in &lambda.parameters {
                    let param_id = param.name.type_id;
                    self.type_env.insert(param_id, param.type_annotation.node.clone());
                    self.var_env.insert(param.name.node.clone(), param_id);
                }

                let old_ret_ty = self.current_function_return_ty.clone();
                self.current_function_return_ty = Some(lambda.return_type.node.clone());

                self.infer_stmts(&lambda.body.node.statements)?;

                if let Some(expr) = &lambda.body.node.expr {
                    let body_ty = self.infer_expr(expr)?;
                    self.unify(lambda.return_type.node.clone(), body_ty, expr.span)?;
                } else if !lambda.body.node.statements.iter().any(|stmt| matches!(stmt, Stmt::Return(_))) {
                    self.unify(Type::Nil, lambda.return_type.node.clone(), lambda.return_type.span)?;
                }

                self.current_function_return_ty = old_ret_ty;
                self.var_env.exit_scope();
                Ok(TypeVar(expr.type_id))
            }
        }
    }
}
