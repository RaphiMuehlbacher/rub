use crate::MethodRegistry;
use crate::ast_lowerer::FunctionBodies;
use crate::error::TypeInferrerError;
use crate::error::TypeInferrerError::{NonBooleanCondition, NotCallable, TypeMismatch, UnknownMethod, WrongArgumentCount};
use crate::ir::{BinaryOp, BlockExpr, DefId, DefMap, Definition, Expr, IrId, IrNode, IrProgram, LiteralExpr, ResolvedType, Stmt, UnaryOp};
use miette::{Report, SourceSpan};
use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Formatter};
use std::ops::Deref;

#[derive(Debug, Clone, PartialEq)]
pub struct TypeDatabase {
    pub expr_types: HashMap<IrId, Type>,
    pub def_types: HashMap<DefId, Type>,
}
impl TypeDatabase {
    pub fn new() -> Self {
        Self {
            expr_types: HashMap::new(),
            def_types: HashMap::new(),
        }
    }
    pub fn with_builtins() -> Self {
        let mut def_types = HashMap::new();
        def_types.insert(
            7,
            Type::Function {
                params: vec![],
                return_type: Box::new(Type::Float),
            },
        );
        //TODO generic params
        def_types.insert(
            9,
            Type::Function {
                params: vec![Type::Int],
                return_type: Box::new(Type::Nil),
            },
        );
        Self {
            expr_types: HashMap::new(),
            def_types,
        }
    }
}

pub type TypeVarId = usize;
pub type TypeParamId = usize;

#[derive(Debug, Clone, PartialEq)]
pub struct TypeVarContext {
    next_var: TypeVarId,
    solutions: HashMap<TypeVarId, Type>,
    source: String,
}

impl TypeVarContext {
    pub fn new(source: String) -> Self {
        Self {
            next_var: 0,
            solutions: HashMap::new(),
            source,
        }
    }

    pub fn fresh_var(&mut self) -> Type {
        let id = self.next_var;
        self.next_var += 1;
        Type::TypeVar(id)
    }

    pub fn unify(&mut self, found: &Type, expected: &Type, found_span: &SourceSpan) -> Result<(), TypeInferrerError> {
        let found = self.resolve(found);
        let expected = self.resolve(expected);

        match (found, expected) {
            (Type::Int, Type::Int) => Ok(()),
            (Type::Float, Type::Float) => Ok(()),
            (Type::String, Type::String) => Ok(()),
            (Type::Bool, Type::Bool) => Ok(()),
            (Type::Nil, Type::Nil) => Ok(()),
            (Type::TypeVar(id), ty) | (ty, Type::TypeVar(id)) => {
                if let Type::TypeVar(other_var) = ty {
                    if id == other_var {
                        return Ok(());
                    }
                }
                if self.occurs_in(id, &ty) {
                    panic!("You need to implement the Error type for this")
                }
                self.solutions.insert(id, ty);
                Ok(())
            }
            (
                Type::Struct {
                    def_id: found_id,
                    generic_args: found_args,
                },
                Type::Struct {
                    def_id: expected_id,
                    generic_args: expected_args,
                },
            ) if found_id == expected_id => {
                for (found_arg, expected_arg) in found_args.iter().zip(expected_args.iter()) {
                    self.unify(found_arg, expected_arg, found_span)?;
                }
                Ok(())
            }
            (
                Type::Function {
                    params: found_params,
                    return_type: found_return,
                },
                Type::Function {
                    params: expected_params,
                    return_type: expected_return,
                },
            ) if found_params.len() == expected_params.len() => {
                for (found_param, expected_param) in found_params.iter().zip(expected_params.iter()) {
                    self.unify(found_param, expected_param, found_span)?;
                }
                self.unify(&found_return, &expected_return, found_span)?;
                Ok(())
            }
            (Type::Vec { ty: found }, Type::Vec { ty: expected }) => {
                self.unify(&found, &expected, found_span)?;
                Ok(())
            }
            (f, e) => Err(TypeMismatch {
                src: self.source.clone(),
                span: found_span.clone(),
                expected: e.to_string(),
                found: f.to_string(),
            }),
        }
    }

    fn resolve(&self, ty: &Type) -> Type {
        match ty {
            Type::TypeVar(var_id) => {
                if let Some(resolved) = self.solutions.get(var_id) {
                    self.resolve(resolved)
                } else {
                    ty.clone()
                }
            }
            _ => ty.clone(),
        }
    }

    fn occurs_in(&self, var: TypeVarId, ty: &Type) -> bool {
        match self.resolve(ty) {
            Type::Int | Type::Float | Type::String | Type::Bool | Type::Nil | Type::TypeParam(_) | Type::Error => false,
            Type::Vec { ty } => self.occurs_in(var, &ty),
            Type::Struct { generic_args, .. } => generic_args.iter().any(|arg| self.occurs_in(var, arg)),
            Type::Function { params, return_type } => {
                params.iter().any(|param| self.occurs_in(var, param)) || self.occurs_in(var, &return_type)
            }
            Type::TypeVar(id) => id == var,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub enum Type {
    Int,
    Float,
    String,
    Bool,
    Nil,
    TypeParam(TypeParamId),
    Vec {
        ty: Box<Type>,
    },
    Struct {
        def_id: DefId,
        generic_args: Vec<Type>, // Vec<Person<Int>>
    },
    Function {
        params: Vec<Type>,
        return_type: Box<Type>,
    },
    TypeVar(TypeVarId),
    Error,
}

impl Type {
    pub fn from_resolved_type(ty: &ResolvedType, def_map: &DefMap) -> Type {
        match ty {
            ResolvedType::Named(def_id) => {
                let def = def_map.get(*def_id).unwrap();

                match def {
                    Definition::Struct { def_id, .. } => Type::Struct {
                        def_id: *def_id,
                        generic_args: vec![],
                    },
                    Definition::TypeParam { .. } => Type::TypeParam(todo!()),
                    Definition::Builtin { name, .. } => match name.as_str() {
                        "Int" => Type::Int,
                        "Float" => Type::Float,
                        "String" => Type::String,
                        "Nil" => Type::Nil,
                        "Bool" => Type::Bool,
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                }
            }
            ResolvedType::Function { params, return_type } => Type::Function {
                params: params.iter().map(|p| Type::from_resolved_type(p, def_map)).collect(),
                return_type: Box::new(Type::from_resolved_type(return_type, def_map)),
            },
            ResolvedType::Generic { base, args } => {
                let def = def_map.get(*base).unwrap();
                if let Definition::Builtin { name, .. } = def
                    && name == "Vec"
                {
                    return Type::Vec {
                        ty: Box::new(Type::from_resolved_type(args.first().unwrap(), def_map)),
                    };
                }

                Type::Struct {
                    def_id: def.def_id(),
                    generic_args: args.iter().map(|a| Type::from_resolved_type(a, def_map)).collect(),
                }
            }
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Int => write!(f, "Int"),
            Type::Float => write!(f, "Float"),
            Type::String => write!(f, "String"),
            Type::Bool => write!(f, "Bool"),
            Type::Nil => write!(f, "Nil"),
            Type::TypeParam(id) => write!(f, "T{}", id),
            Type::Vec { ty } => write!(f, "Vec<{}>", ty),
            Type::Struct { def_id, generic_args } => {
                if generic_args.is_empty() {
                    write!(f, "Struct{}", def_id)
                } else {
                    write!(
                        f,
                        "Struct{}<{}>",
                        def_id,
                        generic_args.iter().map(|arg| arg.to_string()).collect::<Vec<_>>().join(", ")
                    )
                }
            }
            Type::Function { params, return_type } => {
                write!(
                    f,
                    "fn({}) -> {}",
                    params.iter().map(|param| param.to_string()).collect::<Vec<_>>().join(", "),
                    return_type
                )
            }
            Type::TypeVar(id) => write!(f, "?{}", id),
            Type::Error => write!(f, "err"),
        }
    }
}

pub struct TypeInferrer<'a> {
    program: &'a IrProgram,
    source: String,
    errors: Vec<Report>,

    type_db: TypeDatabase,
    method_registry: &'a MethodRegistry<'a>,
    def_map: &'a DefMap,
    function_bodies: &'a FunctionBodies,
    infer_ctx: TypeVarContext,

    current_function_return_ty: Option<Type>,
}

pub struct TypeInferenceResult<'a> {
    pub errors: &'a Vec<Report>,
    pub type_env: &'a TypeDatabase,
}

impl<'a> TypeInferrer<'a> {
    pub fn new(
        ast: &'a IrProgram,
        defs: &'a DefMap,
        function_bodies: &'a FunctionBodies,
        method_registry: &'a MethodRegistry,
        source: String,
    ) -> Self {
        Self {
            program: ast,
            infer_ctx: TypeVarContext::new(source.clone()),
            source,
            errors: vec![],
            current_function_return_ty: None,
            type_db: TypeDatabase::with_builtins(),
            function_bodies,
            method_registry,
            def_map: defs,
        }
    }

    fn report(&mut self, error: TypeInferrerError) {
        self.errors.push(error.into());
    }

    pub fn infer(&mut self) -> TypeInferenceResult {
        for stmt in &self.program.statements {
            if let Err(err) = self.infer_stmt(stmt) {
                self.report(err);
            }
        }

        TypeInferenceResult {
            errors: &self.errors,
            type_env: &self.type_db,
        }
    }

    fn is_type_ambiguous(&self, expr: &Expr) -> bool {
        match expr {
            Expr::Literal(LiteralExpr::VecLiteral(elements)) if elements.is_empty() => true,
            _ => false,
        }
    }

    fn infer_stmt(&mut self, stmt: &IrNode<Stmt>) -> Result<(), TypeInferrerError> {
        match &stmt.node {
            Stmt::ExprStmtNode(expr_stmt) => {
                self.infer_expr(&expr_stmt.expr)?;
                Ok(())
            }
            Stmt::VarDecl(var_decl) => {
                let def_id = var_decl.ident.def_id;

                let annotated_ty = var_decl.type_annotation.as_ref().map(|t| Type::from_resolved_type(t, self.def_map));
                let init_ty = if let Some(init) = &var_decl.initializer {
                    match self.infer_expr(init) {
                        Ok(ty) => Some(ty),
                        Err(_) => None,
                    }
                } else {
                    None
                };
                let is_ambiguous = var_decl
                    .initializer
                    .as_ref()
                    .map(|expr| self.is_type_ambiguous(&expr.node))
                    .unwrap_or(false);

                match (annotated_ty, init_ty) {
                    (Some(annot), Some(init)) => {
                        self.infer_ctx.unify(&annot, &init, &var_decl.clone().initializer.unwrap().span)?;
                        let final_ty = self.infer_ctx.resolve(&annot);
                        self.type_db.def_types.insert(def_id, final_ty);
                    }
                    (Some(annot), None) => {
                        let final_ty = self.infer_ctx.resolve(&annot);
                        self.type_db.def_types.insert(def_id, final_ty);
                    }
                    (None, Some(_)) if is_ambiguous => {
                        panic!("Create a new Error")
                    }
                    (None, Some(init)) => {
                        let final_ty = self.infer_ctx.resolve(&init);
                        self.type_db.def_types.insert(def_id, final_ty);
                    }
                    (None, None) => {
                        self.type_db.def_types.insert(def_id, Type::Error);
                        return Err(TypeInferrerError::CannotInferType {
                            src: self.source.clone(),
                            span: var_decl.ident.name.span,
                            name: var_decl.ident.name.node.clone(),
                        });
                    }
                }
                Ok(())
            }

            Stmt::FunDecl(fun_decl) => {
                let def_id = fun_decl.ident.def_id;

                let param_types = fun_decl
                    .params
                    .iter()
                    .map(|p| Type::from_resolved_type(&p.type_annotation, self.def_map))
                    .collect();

                let function_ty = Type::Function {
                    params: param_types,
                    return_type: Box::new(Type::from_resolved_type(&fun_decl.return_type, self.def_map)),
                };

                self.type_db.def_types.insert(def_id, function_ty);
                Ok(())

                // if fun_decl.generics.is_empty() {
                //     for param in &fun_decl.params {
                //         let param_id = param.name.name.ir_id;
                //         self.type_db.insert(param_id, param.type_annotation.node.clone());
                //         self.var_env.insert(param.name.node.clone(), param_id);
                //     }
                //
                //     let old_ret_ty = self.current_function_return_ty.clone();
                //     self.current_function_return_ty = Some(fun_decl.return_type.node.clone());
                //
                //     self.infer_stmts(&fun_decl.body.node.statements)?;
                //
                //     if let Some(expr) = &fun_decl.body.node.expr {
                //         let body_ty = self.infer_expr(expr)?;
                //         self.unify(fun_decl.return_type.node.clone(), body_ty, fun_decl.ident.span)?;
                //     } else if !fun_decl
                //         .body
                //         .node
                //         .statements
                //         .iter()
                //         .any(|stmt| matches!(stmt.node, Stmt::Return(_)))
                //     {
                //         self.unify(fun_decl.return_type.node.clone(), Type::Nil, fun_decl.return_type.span)?;
                //     }
                //
                //     self.current_function_return_ty = old_ret_ty;
                // }
                // Ok(())
            }
            Stmt::StructDecl(struct_decl) => {
                let def_id = struct_decl.ident.def_id;

                let mut seen_fields = HashSet::new();

                for field in &struct_decl.fields {
                    if !seen_fields.insert(field.name.name.node.clone()) {
                        self.report(TypeInferrerError::DuplicateFieldDeclaration {
                            src: self.source.clone(),
                            name: field.name.name.node.clone(),
                            span: field.name.name.span,
                        });
                    }
                    self.type_db
                        .def_types
                        .insert(field.name.def_id, Type::from_resolved_type(&field.type_annotation, self.def_map));
                }

                let struct_type = Type::Struct {
                    def_id,
                    generic_args: vec![],
                };

                self.type_db.def_types.insert(def_id, struct_type);

                Ok(())
            }
            Stmt::While(while_stmt) => {
                let condition_ty = self.infer_expr(&while_stmt.condition)?;

                match condition_ty {
                    Type::Bool => Ok(()),
                    found => Err(NonBooleanCondition {
                        src: self.source.clone(),
                        span: while_stmt.condition.span,
                        found: found.to_string(),
                    }),
                }?;
                self.infer_stmts(&while_stmt.body.node.statements)?;

                Ok(())
            }
            Stmt::Return(return_stmt) => {
                if let Some(ret_expr) = &return_stmt.expr {
                    let ret_ty = self.infer_expr(ret_expr)?;

                    if let Some(expected_ty) = &self.current_function_return_ty {
                        self.infer_ctx.unify(&ret_ty, &expected_ty, &ret_expr.span)?;
                    }
                } else {
                    let ret_ty = Type::Nil;
                    if let Some(expected_ty) = &self.current_function_return_ty {
                        self.infer_ctx.unify(&ret_ty, &expected_ty, &stmt.span)?;
                    }
                }

                Ok(())
            }
        }
    }

    fn infer_stmts(&mut self, stmts: &Vec<IrNode<Stmt>>) -> Result<(), TypeInferrerError> {
        for stmt in stmts {
            self.infer_stmt(stmt)?;
        }
        Ok(())
    }

    fn infer_block_expr(&mut self, block: &BlockExpr) -> Result<Type, TypeInferrerError> {
        for stmt in &block.statements {
            self.infer_stmt(stmt)?;
        }

        let return_ty = if let Some(expr) = &block.expr {
            Ok(self.infer_expr(expr)?)
        } else {
            Ok(Type::Nil)
        };

        return_ty
    }

    fn infer_expr(&mut self, expr: &IrNode<Expr>) -> Result<Type, TypeInferrerError> {
        match &expr.node {
            Expr::FieldAssign(field_assign) => {
                let receiver_ty = self.infer_expr(&field_assign.receiver)?;
                let value_ty = self.infer_expr(&field_assign.value)?;

                match receiver_ty {
                    Type::Struct { def_id, generic_args: _ } => {
                        let struct_def = self.def_map.get(def_id).unwrap();
                        let field_def_ids = struct_def.fields();

                        if let Some(field_def_id) = field_def_ids
                            .iter()
                            .find(|def_id| self.def_map.get(**def_id).unwrap().name() == field_assign.field.node)
                        {
                            let field_ty = self.type_db.def_types.get(&field_def_id).unwrap().clone();
                            self.infer_ctx.unify(&value_ty, &field_ty, &field_assign.value.span)?;

                            self.type_db.expr_types.insert(expr.ir_id, field_ty.clone());
                            Ok(field_ty)
                        } else {
                            Err(TypeInferrerError::UnknownField {
                                src: self.source.clone(),
                                span: field_assign.field.span,
                                field: field_assign.field.node.clone(),
                                struct_name: struct_def.name().to_string(),
                            })
                        }
                    }
                    found => Err(TypeMismatch {
                        src: self.source.clone(),
                        span: field_assign.receiver.span,
                        found: found.to_string(),
                        expected: "Struct".to_string(),
                    }),
                }
            }
            Expr::FieldAccess(field_access) => {
                let receiver_ty = self.infer_expr(&field_access.receiver)?;

                match receiver_ty {
                    Type::Struct { def_id, generic_args: _ } => {
                        let struct_def = self.def_map.get(def_id).unwrap();
                        let field_def_ids = struct_def.fields();

                        if let Some(field_def_id) = field_def_ids
                            .iter()
                            .find(|def_id| self.def_map.get(**def_id).unwrap().name() == field_access.field.node)
                        {
                            let field_ty = self.type_db.def_types.get(&field_def_id).unwrap().clone();
                            self.type_db.expr_types.insert(expr.ir_id, field_ty.clone());
                            Ok(field_ty)
                        } else {
                            Err(TypeInferrerError::UnknownField {
                                src: self.source.clone(),
                                span: field_access.field.span,
                                field: field_access.field.node.clone(),
                                struct_name: struct_def.name().to_string(),
                            })
                        }
                    }

                    found => Err(TypeMismatch {
                        src: self.source.clone(),
                        span: field_access.receiver.span,
                        expected: "Struct".to_string(),
                        found: found.to_string(),
                    }),
                }
            }
            Expr::StructInit(struct_init) => {
                let struct_type = self.type_db.def_types.get(&struct_init.name.def_id).unwrap().clone();

                if let Type::Struct { def_id, generic_args: _ } = struct_type {
                    let struct_def = self.def_map.get(def_id).unwrap();
                    let field_def_ids = struct_def.fields();

                    let struct_fields: HashMap<String, Type> = field_def_ids
                        .iter()
                        .map(|def_id| self.def_map.get(*def_id).unwrap())
                        .map(|def| (def.name().to_string(), self.type_db.def_types.get(&def.def_id()).unwrap().clone()))
                        .collect();

                    let mut seen_fields = HashSet::new();

                    for (field_name, _) in &struct_init.fields {
                        if !seen_fields.insert(field_name.name.node.clone()) {
                            self.report(TypeInferrerError::DuplicateFieldInstantiation {
                                src: self.source.clone(),
                                span: field_name.name.span,
                                name: field_name.name.node.clone(),
                            });
                        }
                    }

                    for (field_name, field_value) in &struct_init.fields {
                        if !struct_fields.contains_key(&field_name.name.node) {
                            self.report(TypeInferrerError::UnknownField {
                                src: self.source.clone(),
                                span: field_name.name.span,
                                field: field_name.name.node.clone(),
                                struct_name: struct_init.name.name.node.clone(),
                            });
                            continue;
                        }
                        let expected_type = struct_fields.get(&field_name.name.node).unwrap();
                        let actual_type = self.infer_expr(field_value)?;
                        self.infer_ctx.unify(&actual_type, &expected_type.clone(), &field_value.span)?;
                    }

                    for (field_name, _) in struct_fields {
                        if !seen_fields.contains(&field_name) {
                            self.report(TypeInferrerError::MissingField {
                                src: self.source.clone(),
                                span: struct_init.name.name.span,
                                field: field_name,
                                struct_name: struct_init.name.name.node.clone(),
                            });
                        }
                    }
                }

                self.type_db.expr_types.insert(expr.ir_id, struct_type.clone());
                Ok(struct_type.clone())
            }
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
                            self.infer_ctx.unify(&elem_ty, &first_elem_ty, &elem.span)?;
                        }

                        Type::Vec {
                            ty: Box::new(first_elem_ty),
                        }
                    }
                };

                self.type_db.expr_types.insert(expr.ir_id, ty.clone());
                Ok(ty)
            }

            Expr::Block(block) => self.infer_block_expr(block),

            Expr::If(if_expr) => {
                let condition_ty = self.infer_expr(&if_expr.condition)?;

                match condition_ty {
                    Type::Bool => Ok(()),
                    found => Err(NonBooleanCondition {
                        src: self.source.clone(),
                        span: if_expr.condition.span,
                        found: found.to_string(),
                    }),
                }?;

                let then_return_ty = self.infer_block_expr(&if_expr.then_branch.node)?;
                let else_return_ty = if let Some(else_branch) = &if_expr.else_branch {
                    self.infer_block_expr(&else_branch.node)?
                } else {
                    Type::Nil
                };

                self.infer_ctx.unify(&then_return_ty, &else_return_ty, &if_expr.then_branch.span)?;
                Ok(then_return_ty)
            }
            Expr::MethodCall(method_call) => {
                let receiver_ty = self.infer_expr(&method_call.receiver)?;
                self.type_db.expr_types.insert(method_call.receiver.ir_id, receiver_ty.clone());

                if let Some((method_ty, _)) = self
                    .method_registry
                    .lookup_method(&receiver_ty, &method_call.method.name.node)
                    .cloned()
                {
                    match method_ty {
                        Type::Function { params, return_type } => {
                            if params.len() != method_call.arguments.len() {
                                return Err(WrongArgumentCount {
                                    src: self.source.clone(),
                                    span: method_call.method.name.span,
                                    expected: params.len(),
                                    found: method_call.arguments.len(),
                                });
                            }

                            for (param, arg) in params.iter().zip(&method_call.arguments) {
                                let arg_ty = self.infer_expr(arg)?;
                                self.infer_ctx.unify(&arg_ty, &param, &arg.span)?;
                            }

                            self.type_db.expr_types.insert(expr.ir_id, *return_type.clone());
                            Ok(*return_type)
                        }
                        _ => unreachable!(),
                    }
                } else {
                    Err(UnknownMethod {
                        src: self.source.clone(),
                        span: expr.span,
                        method: method_call.method.name.node.clone(),
                        base_type: receiver_ty.to_string(),
                    })
                }
            }
            Expr::Unary(unary_expr) => {
                let right_ty = self.infer_expr(unary_expr.expr.deref())?;
                let result_ty = match unary_expr.op.node {
                    UnaryOp::Bang => {
                        self.infer_ctx.unify(&right_ty, &Type::Bool, &unary_expr.expr.span)?;
                        Type::Bool
                    }
                    UnaryOp::Minus => {
                        self.infer_ctx.unify(&right_ty, &Type::Float, &unary_expr.expr.span)?;
                        Type::Float
                    }
                };

                self.type_db.expr_types.insert(expr.ir_id, result_ty.clone());
                Ok(result_ty)
            }
            Expr::Binary(binary_expr) => {
                let left_ty = self.infer_expr(&binary_expr.left)?;
                let right_ty = self.infer_expr(&binary_expr.right)?;

                let result_ty = match binary_expr.op.node {
                    BinaryOp::Plus => match (left_ty.clone(), right_ty.clone()) {
                        (Type::Int, Type::Int) => Type::Int,
                        (Type::Float, Type::Float) => Type::Float,
                        (Type::String, Type::String) => Type::String,
                        _ => {
                            return Err(TypeMismatch {
                                src: self.source.clone(),
                                span: binary_expr.right.span,
                                expected: left_ty.to_string(),
                                found: right_ty.to_string(),
                            });
                        }
                    },
                    BinaryOp::Minus => match (left_ty.clone(), right_ty.clone()) {
                        (Type::Int, Type::Int) => Type::Int,
                        (Type::Float, Type::Float) => Type::Float,
                        _ => {
                            return Err(TypeMismatch {
                                src: self.source.clone(),
                                span: binary_expr.right.span,
                                expected: left_ty.to_string(),
                                found: right_ty.to_string(),
                            });
                        }
                    },
                    BinaryOp::Star | BinaryOp::Slash => match (left_ty.clone(), right_ty.clone()) {
                        (Type::Int, Type::Int) => Type::Int,
                        (Type::Float, Type::Float) => Type::Float,
                        _ => {
                            return Err(TypeMismatch {
                                src: self.source.clone(),
                                span: binary_expr.right.span,
                                expected: left_ty.to_string(),
                                found: right_ty.to_string(),
                            });
                        }
                    },
                    BinaryOp::Greater | BinaryOp::GreaterEqual | BinaryOp::Less | BinaryOp::LessEqual => {
                        match (left_ty.clone(), right_ty.clone()) {
                            (Type::Int, Type::Int) => Type::Bool,
                            (Type::Float, Type::Float) => Type::Bool,
                            _ => {
                                return Err(TypeMismatch {
                                    src: self.source.clone(),
                                    span: binary_expr.right.span,
                                    expected: left_ty.to_string(),
                                    found: right_ty.to_string(),
                                });
                            }
                        }
                    }
                    BinaryOp::EqualEqual | BinaryOp::BangEqual => {
                        self.infer_ctx.unify(&left_ty, &right_ty, &binary_expr.right.span)?;
                        Type::Bool
                    }
                };

                self.type_db.expr_types.insert(expr.ir_id, result_ty.clone());
                Ok(result_ty)
            }
            Expr::Grouping(grouping) => self.infer_expr(grouping.deref()),
            Expr::Variable(variable_expr) => {
                let def_id = variable_expr.def_id;
                Ok(self.type_db.def_types.get(&def_id).unwrap().clone())
            }
            Expr::Assign(assign_expr) => {
                let target_ty = self.type_db.def_types.get(&assign_expr.target.def_id).unwrap().clone();
                let right_ty = self.infer_expr(&assign_expr.value)?;

                self.infer_ctx.unify(&target_ty, &right_ty, &assign_expr.value.span)?;

                self.type_db.expr_types.insert(expr.ir_id, right_ty.clone());
                Ok(right_ty)
            }
            Expr::Logical(logical_expr) => {
                let left = self.infer_expr(&logical_expr.left)?;
                let right = self.infer_expr(&logical_expr.right)?;

                self.infer_ctx.unify(&left, &Type::Bool, &logical_expr.left.span)?;
                self.infer_ctx.unify(&right, &Type::Bool, &logical_expr.right.span)?;

                self.type_db.expr_types.insert(expr.ir_id, Type::Bool);
                Ok(Type::Bool)
            }
            Expr::Call(call_expr) => {
                let callee_ty = self.infer_expr(call_expr.callee.deref())?;

                match callee_ty {
                    Type::Function { params, return_type } => {
                        if call_expr.arguments.len() != params.len() {
                            return Err(WrongArgumentCount {
                                src: self.source.clone(),
                                span: call_expr.callee.span,
                                expected: params.len(),
                                found: call_expr.arguments.len(),
                            });
                        }
                        for (arg_expr, param_ty) in call_expr.arguments.iter().zip(params.iter()) {
                            let arg_ty = self.infer_expr(arg_expr)?;
                            self.infer_ctx.unify(&arg_ty, &param_ty, &arg_expr.span)?;
                        }

                        if let Expr::Variable(ident) = &call_expr.callee.node {
                            if let Some(definition) = self.def_map.get(ident.def_id) {
                                match definition {
                                    Definition::Function {
                                        def_id,
                                        span,
                                        params: param_def_ids,
                                        ..
                                    } => {
                                        let old_return_ty = self.current_function_return_ty.clone();
                                        self.current_function_return_ty = Some(*return_type.clone());

                                        let param_defs: Vec<&Definition> =
                                            param_def_ids.iter().map(|def_id| self.def_map.get(*def_id).unwrap()).collect();

                                        for (param_def, param_ty) in param_defs.iter().zip(params.iter()) {
                                            self.type_db.def_types.insert(param_def.def_id(), param_ty.clone());
                                        }
                                        let body = self.function_bodies.get(*def_id);
                                        self.infer_stmts(&body.node.statements)?;

                                        if let Some(expr) = &body.node.expr {
                                            let body_ty = self.infer_expr(expr)?;
                                            self.infer_ctx.unify(&body_ty, &return_type, &span)?;
                                        }

                                        self.current_function_return_ty = old_return_ty;
                                    }
                                    Definition::NativeFunction { .. } => {}
                                    _ => panic!(),
                                }
                            }
                        }

                        self.type_db.expr_types.insert(expr.ir_id, *return_type.clone());
                        Ok(*return_type)
                    }
                    found => Err(NotCallable {
                        src: self.source.clone(),
                        span: expr.span,
                        found: found.to_string(),
                    }),
                }
            }
            Expr::Lambda(lambda) => {
                // self.var_env.enter_scope();
                //
                // let param_types: Vec<Type> = lambda.parameters.iter().map(|p| p.type_annotation.node.clone()).collect();
                //
                // let fn_type = Type::Function {
                //     params: param_types.clone(),
                //     return_ty: Box::new(lambda.return_type.node.clone()),
                // };
                //
                // self.type_env.insert(expr.ir_id, fn_type.clone());
                //
                // for param in &lambda.parameters {
                //     let param_id = param.name.ir_id;
                //     self.type_env.insert(param_id, param.type_annotation.node.clone());
                //     self.var_env.insert(param.name.node.clone(), param_id);
                // }
                //
                // let old_ret_ty = self.current_function_return_ty.clone();
                // self.current_function_return_ty = Some(lambda.return_type.node.clone());
                //
                // self.infer_stmts(&lambda.body.node.statements)?;
                //
                // if let Some(expr) = &lambda.body.node.expr {
                //     let body_ty = self.infer_expr(expr)?;
                //     self.unify(lambda.return_type.node.clone(), body_ty, expr.span)?;
                // } else if !lambda.body.node.statements.iter().any(|stmt| matches!(stmt.node, Stmt::Return(_))) {
                //     self.unify(Type::Nil, lambda.return_type.node.clone(), lambda.return_type.span)?;
                // }
                //
                // self.current_function_return_ty = old_ret_ty;
                // self.var_env.exit_scope();
                // Ok(TypeVar(expr.ir_id))
                todo!()
            }
        }
    }
}
