use crate::ast::{
    BinaryOp, BlockStmt, Expr, ExprStmt, FunDeclStmt, IfStmt, LiteralExpr, LogicalOp, Program, ReturnStmt, Stmt, Typed, UnaryOp,
    VarDeclStmt, WhileStmt,
};

use crate::error::TypeInferrerError;
use crate::error::TypeInferrerError::TypeMismatch;
use crate::type_inferrer::Type::TypeVar;
use miette::{Report, SourceOffset, SourceSpan};
use std::collections::{HashMap, HashSet};
use std::ops::Deref;
use std::vec;

pub type TypeVarId = usize;

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Float,
    Bool,
    String,
    Nil,
    Function { params: Vec<Box<Type>>, return_ty: Box<Type> },
    TypeVar(TypeVarId),
    Generic(String),
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeScheme {
    Mono(Type),
    Poly(Vec<TypeVarId>, Type),
}

#[derive(Debug, Clone, PartialEq)]
pub struct VarEnv {
    scopes: Vec<HashMap<String, TypeScheme>>,
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

    pub fn insert(&mut self, name: String, ty: TypeScheme) {
        self.scopes.last_mut().unwrap().insert(name, ty);
    }

    pub fn lookup(&mut self, name: &str) -> Option<TypeScheme> {
        for scope in self.scopes.iter().rev() {
            if let Some(scheme) = scope.get(name) {
                return Some(scheme.clone());
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
}

pub struct TypeInferenceResult<'a> {
    pub errors: &'a Vec<Report>,
    pub type_env: &'a HashMap<TypeVarId, Type>,
}

impl<'a> TypeInferrer<'a> {
    pub fn new(ast: &'a Program, source: String) -> Self {
        Self {
            program: ast,
            source,
            errors: vec![],
            current_function_return_ty: None,
            var_env: VarEnv::new(),
            type_env: HashMap::new(),
        }
    }

    fn report(&mut self, error: TypeInferrerError) {
        self.errors.push(error.into());
    }

    fn fresh_type_var(&mut self) -> TypeVarId {
        let typed = Typed::new(
            LiteralExpr::String("if you see this something is wrong".to_string()),
            SourceSpan::new(SourceOffset::from(0), 0),
        );
        typed.type_id
    }

    fn generalize(&mut self, ty: &Type) -> TypeScheme {
        let free_vars = self.free_vars(ty);

        if free_vars.is_empty() {
            return TypeScheme::Mono(ty.clone());
        }

        TypeScheme::Poly(free_vars, ty.clone())
    }

    fn bound_vars(&mut self, ty: &Type) -> Vec<TypeVarId> {
        match ty {
            Type::Float | Type::Bool | Type::String | Type::Nil | Type::Generic(_) => vec![],
            Type::Function { params, return_ty } => {
                let mut vars = vec![];
                for param in params {
                    vars.append(&mut self.bound_vars(param));
                }
                vars.append(&mut self.bound_vars(return_ty));
                vars
            }
            TypeVar(id) => vec![*id],
        }
    }

    fn free_vars(&mut self, ty: &Type) -> Vec<TypeVarId> {
        match ty {
            Type::Float | Type::Bool | Type::String | Type::Nil | Type::Generic(_) => vec![],
            Type::Function { params, return_ty } => {
                let mut vars = vec![];
                for param in params {
                    vars.append(&mut self.free_vars(param));
                }
                vars.append(&mut self.free_vars(return_ty));
                vars
            }
            TypeVar(id) => {
                // First get the bound type (if any) to avoid multiple borrows
                let bound_ty = self.type_env.get(id).cloned();

                match bound_ty {
                    Some(ty) => {
                        if let TypeVar(bound_id) = ty {
                            if bound_id == *id { vec![*id] } else { self.free_vars(&ty) }
                        } else {
                            self.free_vars(&ty)
                        }
                    }
                    None => vec![*id],
                }
            }
        }
    }

    fn instantiate(&mut self, scheme: &TypeScheme) -> Type {
        match scheme {
            TypeScheme::Mono(ty) => ty.clone(),
            TypeScheme::Poly(type_vars, ty) => {
                let mut substitutions = HashMap::new();

                for &var_id in type_vars {
                    substitutions.insert(var_id, TypeVar(self.fresh_type_var()));
                }

                self.substitute(ty, &substitutions)
            }
        }
    }

    fn substitute(&self, ty: &Type, substitutions: &HashMap<TypeVarId, Type>) -> Type {
        match ty {
            Type::Float | Type::Bool | Type::String | Type::Nil | Type::Generic(_) => ty.clone(),
            Type::Function { params, return_ty } => {
                let new_params = params.iter().map(|p| Box::new(self.substitute(p, substitutions))).collect();
                let new_return = self.substitute(return_ty, substitutions);

                Type::Function {
                    params: new_params,
                    return_ty: Box::new(new_return),
                }
            }
            TypeVar(id) => {
                if let Some(new_ty) = substitutions.get(id) {
                    new_ty.clone()
                } else {
                    ty.clone()
                }
            }
        }
    }

    fn unify(&mut self, left_ty: Type, right_ty: Type, span: SourceSpan) -> Result<Type, TypeInferrerError> {
        match (left_ty, right_ty) {
            (Type::Float, Type::Float) => Ok(Type::Float),
            (Type::String, Type::String) => Ok(Type::String),
            (Type::Bool, Type::Bool) => Ok(Type::Bool),
            (Type::Nil, Type::Nil) => Ok(Type::Nil),
            (Type::Generic(name1), Type::Generic(name2)) if name1 == name2 => Ok(Type::Generic(name1)),
            (Type::Generic(name1), t2) | (t2, Type::Generic(name1)) => Ok(t2),
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
                    self.unify(*param1.clone(), *param2.clone(), span)?;
                }

                self.unify(*r1.clone(), *r2, span)?;
                Ok(Type::Function { params: p1, return_ty: r1 })
            }

            (ty, TypeVar(id)) | (TypeVar(id), ty) => {
                // Check for recursive types
                if let Type::TypeVar(_) = ty {
                    // Allow unifying two type variables
                } else if self.occurs_check(id, &ty) {
                    return Err(TypeMismatch {
                        src: self.source.clone(),
                        span,
                        expected: TypeVar(id),
                        found: ty,
                    });
                }

                self.type_env.insert(id, ty.clone());
                Ok(TypeVar(id))
            }

            (t1, t2) => Err(TypeMismatch {
                src: self.source.clone(),
                span,
                expected: t1,
                found: t2,
            }),
        }
    }

    fn occurs_check(&self, id: TypeVarId, ty: &Type) -> bool {
        match ty {
            Type::Float | Type::Bool | Type::String | Type::Nil | Type::Generic(_) => false,
            Type::Function { params, return_ty } => params.iter().any(|p| self.occurs_check(id, p)) || self.occurs_check(id, return_ty),
            TypeVar(check_id) => *check_id == id,
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

    fn declare_native_functions(&mut self) {
        let clock_type = Type::Function {
            params: vec![],
            return_ty: Box::new(Type::Float),
        };
        self.var_env.insert("clock".to_string(), TypeScheme::Mono(clock_type));

        let print_type = Type::Function {
            params: vec![Box::new(Type::String)],
            return_ty: Box::new(Type::Nil),
        };
        self.var_env.insert("print".to_string(), TypeScheme::Mono(print_type));
    }

    fn declare_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::FunDecl(fun_decl) => {
                let name = &fun_decl.node.ident.node;

                let fn_type = Type::Function {
                    params: fun_decl
                        .node
                        .params
                        .iter()
                        .map(|p| Box::new(p.node.type_annotation.clone()))
                        .collect(),
                    return_ty: Box::new(fun_decl.node.return_type.clone()),
                };

                // Create a type scheme based on whether the function has generic parameters
                let type_scheme = if fun_decl.node.generics.is_empty() {
                    TypeScheme::Mono(fn_type)
                } else {
                    // Collect generic type variables
                    let generic_vars = fun_decl.node.generics.iter().map(|_| self.fresh_type_var()).collect();
                    TypeScheme::Poly(generic_vars, fn_type)
                };

                self.var_env.insert(name.clone(), type_scheme);
            }
            _ => {}
        }
    }

    fn lookup_var(&mut self, name: &str) -> Option<Type> {
        if let Some(scheme) = self.var_env.lookup(name) {
            return Some(self.instantiate(&scheme));
        }
        None
    }

    // Update the lookup_type method to handle recursive lookups better
    fn lookup_type(&self, type_var: &Type) -> Type {
        let mut visited = HashSet::new();
        self.lookup_type_internal(type_var, &mut visited)
    }

    fn lookup_type_internal(&self, type_var: &Type, visited: &mut HashSet<TypeVarId>) -> Type {
        match type_var {
            TypeVar(id) => {
                if visited.contains(id) {
                    // Prevent infinite recursion
                    return type_var.clone();
                }

                visited.insert(*id);

                if let Some(ty) = self.type_env.get(id) {
                    let resolved = self.lookup_type_internal(ty, visited);
                    visited.remove(id);
                    resolved
                } else {
                    type_var.clone()
                }
            }
            Type::Function { params, return_ty } => {
                let new_params = params.iter().map(|p| Box::new(self.lookup_type_internal(p, visited))).collect();

                let new_return = self.lookup_type_internal(return_ty, visited);

                Type::Function {
                    params: new_params,
                    return_ty: Box::new(new_return),
                }
            }
            _ => type_var.clone(),
        }
    }

    fn infer_stmt(&mut self, stmt: &Stmt) -> Result<(), TypeInferrerError> {
        match stmt {
            Stmt::ExprStmtNode(expr_stmt) => self.infer_expr_stmt(expr_stmt),
            Stmt::VarDecl(var_decl) => self.infer_var_decl(var_decl),
            Stmt::FunDecl(fun_decl) => self.infer_fun_decl(fun_decl),
            Stmt::Block(block) => self.infer_block(block),
            Stmt::If(if_stmt) => self.infer_if_stmt(if_stmt),
            Stmt::While(while_stmt) => self.infer_while_stmt(while_stmt),
            Stmt::Return(return_stmt) => self.infer_return_stmt(return_stmt),
        }
    }

    fn infer_expr_stmt(&mut self, expr_stmt: &Typed<ExprStmt>) -> Result<(), TypeInferrerError> {
        self.infer_expr(&expr_stmt.node.expr)?;
        Ok(())
    }

    fn infer_var_decl(&mut self, var_decl: &Typed<VarDeclStmt>) -> Result<(), TypeInferrerError> {
        let var_id = self.fresh_type_var();
        self.type_env.insert(var_decl.node.ident.type_id, TypeVar(var_id));
        self.var_env
            .insert(var_decl.node.ident.node.clone(), TypeScheme::Mono(TypeVar(var_id)));

        if let Some(init) = &var_decl.node.initializer {
            let init_type = self.infer_expr(init)?;
            self.unify(TypeVar(var_id), init_type, var_decl.node.ident.span)?;
        }

        Ok(())
    }

    fn infer_fun_decl(&mut self, fun_decl: &Typed<FunDeclStmt>) -> Result<(), TypeInferrerError> {
        // Create a mapping of generic parameter names to type variables
        let mut generic_map = HashMap::new();
        for generic in &fun_decl.node.generics {
            let var_id = self.fresh_type_var();
            generic_map.insert(generic.node.clone(), Type::Generic(generic.node.clone()));
        }

        self.var_env.enter_scope();

        // Process parameters with improved generic handling
        let mut param_types = vec![];
        for param in &fun_decl.node.params {
            let param_type = match &param.node.type_annotation {
                Type::Generic(name) => generic_map.get(name).cloned().unwrap_or_else(|| {
                    let var_id = self.fresh_type_var();
                    Type::TypeVar(var_id)
                }),
                _ => param.node.type_annotation.clone(),
            };

            param_types.push(Box::new(param_type.clone()));
            self.var_env.insert(param.node.name.node.clone(), TypeScheme::Mono(param_type));
        }

        // Handle return type
        let return_type = match &fun_decl.node.return_type {
            Type::Generic(name) => generic_map.get(name).cloned().unwrap_or_else(|| {
                let var_id = self.fresh_type_var();
                Type::TypeVar(var_id)
            }),
            _ => fun_decl.node.return_type.clone(),
        };

        let old_ret_ty = self.current_function_return_ty.take();
        self.current_function_return_ty = Some(return_type.clone());

        // Process body
        for stmt in &fun_decl.node.body.node.statements {
            self.infer_stmt(stmt)?;
        }

        // Create function type with proper generic handling
        let fn_type = Type::Function {
            params: param_types,
            return_ty: Box::new(return_type),
        };

        // Create appropriate type scheme
        let type_scheme = if !fun_decl.node.generics.is_empty() {
            let generic_vars: Vec<TypeVarId> = generic_map
                .values()
                .filter_map(|t| match t {
                    Type::TypeVar(id) => Some(*id),
                    _ => None,
                })
                .collect();
            TypeScheme::Poly(generic_vars, fn_type.clone())
        } else {
            TypeScheme::Mono(fn_type.clone())
        };

        self.type_env.insert(fun_decl.node.ident.type_id, fn_type);
        self.var_env.insert(fun_decl.node.ident.node.clone(), type_scheme);

        self.current_function_return_ty = old_ret_ty;
        self.var_env.exit_scope();

        Ok(())
    }

    fn infer_block(&mut self, block: &Typed<BlockStmt>) -> Result<(), TypeInferrerError> {
        self.var_env.enter_scope();

        for stmt in &block.node.statements {
            self.infer_stmt(stmt)?;
        }

        self.var_env.exit_scope();
        Ok(())
    }

    fn infer_if_stmt(&mut self, if_stmt: &Typed<IfStmt>) -> Result<(), TypeInferrerError> {
        let cond_type = self.infer_expr(&if_stmt.node.condition)?;
        self.unify(cond_type, Type::Bool, if_stmt.node.condition.span)?;

        self.infer_block(&if_stmt.node.then_branch)?;

        if let Some(else_branch) = &if_stmt.node.else_branch {
            self.infer_block(else_branch)?;
        }
        Ok(())
    }

    fn infer_while_stmt(&mut self, while_stmt: &Typed<WhileStmt>) -> Result<(), TypeInferrerError> {
        let cond_type = self.infer_expr(&while_stmt.node.condition)?;
        self.unify(cond_type, Type::Bool, while_stmt.node.condition.span)?;

        self.infer_block(&while_stmt.node.body)?;

        Ok(())
    }

    fn infer_return_stmt(&mut self, return_stmt: &Typed<ReturnStmt>) -> Result<(), TypeInferrerError> {
        if let Some(ret_expr) = &return_stmt.node.expr {
            let ret_type = self.infer_expr(ret_expr)?;

            if let Some(expected_ty) = &self.current_function_return_ty {
                self.unify(ret_type, expected_ty.clone(), ret_expr.span)?;
            }
        } else {
            if let Some(expected_ty) = &self.current_function_return_ty {
                self.unify(Type::Nil, expected_ty.clone(), return_stmt.span)?;
            }
        }

        Ok(())
    }

    fn infer_expr(&mut self, expr: &Typed<Expr>) -> Result<Type, TypeInferrerError> {
        match &expr.node {
            Expr::Literal(literal_expr) => {
                let ty = match literal_expr {
                    LiteralExpr::Number(_) => Type::Float,
                    LiteralExpr::String(_) => Type::String,
                    LiteralExpr::Bool(_) => Type::Bool,
                    LiteralExpr::Nil => Type::Nil,
                };

                self.type_env.insert(expr.type_id, ty.clone());
                Ok(ty)
            }
            Expr::Unary(unary_expr) => {
                let right_ty = self.infer_expr(unary_expr.expr.deref())?;
                let result_ty = match unary_expr.op.node {
                    UnaryOp::Bang => {
                        self.unify(right_ty, Type::Bool, unary_expr.expr.span)?;
                        Type::Bool
                    }
                    UnaryOp::Minus => {
                        self.unify(right_ty, Type::Float, unary_expr.expr.span)?;
                        Type::Float
                    }
                };

                self.type_env.insert(expr.type_id, result_ty.clone());
                Ok(result_ty)
            }
            Expr::Binary(binary_expr) => {
                let left = self.infer_expr(binary_expr.left.deref())?;
                let right = self.infer_expr(binary_expr.right.deref())?;

                let result_ty = match binary_expr.op.node {
                    BinaryOp::Plus => {
                        let left_ty = self.lookup_type(&left);
                        let right_ty = self.lookup_type(&right);

                        match (&left_ty, &right_ty) {
                            (Type::Float, Type::Float) => Type::Float,
                            (Type::String, Type::String) => Type::String,
                            (Type::Generic(name1), Type::Generic(name2)) if name1 == name2 => {
                                // Return the same generic type for matching generics
                                left_ty
                            }
                            _ => {
                                // Try to unify the types
                                self.unify(left.clone(), right.clone(), binary_expr.right.span)?
                            }
                        }
                    }
                    BinaryOp::Star | BinaryOp::Minus | BinaryOp::Slash => {
                        let left_ty = self.lookup_type(&left);
                        let right_ty = self.lookup_type(&right);

                        match (&left_ty, &right_ty) {
                            (Type::Float, Type::Float) => Type::Float,
                            (Type::Generic(name1), Type::Generic(name2)) if name1 == name2 => {
                                // Return the same generic type for matching generics
                                left_ty
                            }
                            _ => {
                                // Try to unify the types
                                self.unify(left.clone(), right.clone(), binary_expr.right.span)?
                            }
                        }
                    }
                    // Rest of binary operators remain unchanged
                    BinaryOp::Greater | BinaryOp::GreaterEqual | BinaryOp::Less | BinaryOp::LessEqual => {
                        self.unify(left.clone(), right.clone(), binary_expr.right.span)?;
                        Type::Bool
                    }
                    BinaryOp::EqualEqual | BinaryOp::BangEqual => {
                        self.unify(left.clone(), right.clone(), binary_expr.right.span)?;
                        Type::Bool
                    }
                };

                self.type_env.insert(expr.type_id, result_ty.clone());
                Ok(result_ty)
            }
            Expr::Grouping(grouping) => self.infer_expr(grouping.deref()),
            Expr::Variable(variable_expr) => {
                if let Some(var_type) = self.lookup_var(variable_expr.node.as_str()) {
                    self.type_env.insert(expr.type_id, var_type.clone());
                    Ok(var_type)
                } else {
                    // Error case should be handled elsewhere in resolution
                    let var_type = TypeVar(self.fresh_type_var());
                    self.type_env.insert(expr.type_id, var_type.clone());
                    Ok(var_type)
                }
            }
            Expr::Assign(assign_expr) => {
                let right_ty = self.infer_expr(assign_expr.value.deref())?;

                if let Some(left_ty) = self.lookup_var(assign_expr.target.node.as_str()) {
                    let unified = self.unify(left_ty, right_ty.clone(), assign_expr.value.deref().span)?;
                    self.type_env.insert(expr.type_id, unified.clone());
                    Ok(unified)
                } else {
                    // Error case should be handled elsewhere in resolution
                    self.type_env.insert(expr.type_id, right_ty.clone());
                    Ok(right_ty)
                }
            }
            Expr::Logical(logical_expr) => {
                let left = self.infer_expr(logical_expr.left.deref())?;
                let right = self.infer_expr(logical_expr.right.deref())?;

                self.unify(left.clone(), Type::Bool, logical_expr.left.span)?;
                self.unify(right.clone(), Type::Bool, logical_expr.right.span)?;

                self.type_env.insert(expr.type_id, Type::Bool);
                Ok(Type::Bool)
            }
            Expr::Call(call_expr) => {
                let callee_ty = self.infer_expr(call_expr.callee.deref())?;
                let callee_ty = self.lookup_type(&callee_ty);

                match callee_ty {
                    Type::Function { params, return_ty } => {
                        if params.len() != call_expr.arguments.len() {
                            return Err(TypeMismatch {
                                src: self.source.clone(),
                                span: expr.span,
                                expected: Type::Function {
                                    params: params.clone(),
                                    return_ty: return_ty.clone(),
                                },
                                found: Type::Function {
                                    params: call_expr.arguments.iter().map(|_| Box::new(TypeVar(0))).collect(),
                                    return_ty: Box::new(TypeVar(0)),
                                },
                            });
                        }

                        let mut generic_substitutions: HashMap<String, Type> = HashMap::new();

                        // Process arguments and collect type substitutions for generics
                        for (arg, param_ty) in call_expr.arguments.iter().zip(params.iter()) {
                            let arg_ty = self.infer_expr(arg)?;

                            // Handle generic type parameters
                            match &**param_ty {
                                Type::Generic(name) => {
                                    if let Some(existing) = generic_substitutions.get(name) {
                                        // If we've seen this generic before, ensure consistent types
                                        self.unify(arg_ty.clone(), existing.clone(), arg.span)?;
                                    } else {
                                        // First time seeing this generic, record the concrete type
                                        generic_substitutions.insert(name.clone(), arg_ty.clone());
                                    }
                                }
                                _ => {
                                    // Non-generic parameter, proceed with normal unification
                                    self.unify(arg_ty, *param_ty.clone(), arg.span)?;
                                }
                            }
                        }

                        // Apply substitutions to the return type
                        let mut return_type = *return_ty.clone();
                        if let Type::Generic(name) = &return_type {
                            if let Some(concrete_type) = generic_substitutions.get(name) {
                                return_type = concrete_type.clone();
                            }
                        }

                        self.type_env.insert(expr.type_id, return_type.clone());
                        Ok(return_type)
                    }
                    found => Err(TypeMismatch {
                        src: self.source.clone(),
                        span: call_expr.callee.span,
                        expected: Type::Function {
                            params: vec![],
                            return_ty: Box::new(TypeVar(0)),
                        },
                        found,
                    }),
                }
            }
            Expr::Lambda(lambda) => {
                self.var_env.enter_scope();

                let param_types: Vec<Box<Type>> = lambda.parameters.iter().map(|p| Box::new(p.node.type_annotation.clone())).collect();

                let fn_type = Type::Function {
                    params: param_types.clone(),
                    return_ty: Box::new(lambda.return_type.clone()),
                };

                self.type_env.insert(expr.type_id, fn_type.clone());

                for param in &lambda.parameters {
                    self.var_env
                        .insert(param.node.name.node.clone(), TypeScheme::Mono(param.node.type_annotation.clone()));
                }

                let old_ret_ty = self.current_function_return_ty.clone();
                self.current_function_return_ty = Some(lambda.return_type.clone());

                for stmt in &lambda.body.node.statements {
                    self.infer_stmt(stmt)?;
                }

                self.current_function_return_ty = old_ret_ty;
                self.var_env.exit_scope();
                Ok(fn_type)
            }
        }
    }
}
