use crate::ast::{AstNode, AstProgram, Expr, Ident, Stmt, TypedIdent, UnresolvedType};
use crate::error::ResolverError;
use crate::error::ResolverError::{
    DuplicateLambdaParameter, DuplicateParameter, ReturnOutsideFunction, UndefinedFunction, UndefinedType, UndefinedVariable,
    UninitializedVariable,
};

use crate::ir::ResolvedType;
use miette::Report;
use std::collections::{HashMap, HashSet};
use std::ops::Deref;

#[derive(Debug, Clone, PartialEq)]
pub enum Symbol {
    Variable { initialized: bool },
    Function { params: Vec<TypedIdent>, generics: Vec<Ident> },
    Struct { fields: Vec<TypedIdent> },
}

pub struct ResolverResult<'a> {
    pub errors: &'a Vec<Report>,
    pub resolution_map: &'a HashMap<usize, ResolvedType>,
}

pub struct Resolver<'a> {
    source: String,
    program: &'a AstProgram,
    errors: Vec<Report>,
    scopes: Vec<HashMap<String, Symbol>>,
    resolution_map: HashMap<usize, ResolvedType>,
    inside_fn: bool,
}

impl<'a> Resolver<'a> {
    pub fn new(program: &'a AstProgram, source: String) -> Self {
        let mut var_env = HashMap::new();
        var_env.insert(
            "clock".to_string(),
            Symbol::Function {
                params: vec![],
                generics: vec![],
            },
        );
        var_env.insert(
            "print".to_string(),
            Symbol::Function {
                params: vec![],
                generics: vec![],
            },
        );

        Self {
            source,
            program,
            errors: vec![],
            scopes: vec![var_env],
            resolution_map: HashMap::new(),
            inside_fn: false,
        }
    }

    pub fn resolve(&mut self) -> ResolverResult {
        for stmt in &self.program.statements {
            self.declare_stmt(&stmt.node);
        }

        for stmt in &self.program.statements {
            self.resolve_stmt(stmt);
        }

        ResolverResult {
            errors: &self.errors,
            resolution_map: &self.resolution_map,
        }
    }

    fn report(&mut self, error: ResolverError) {
        self.errors.push(error.into());
    }

    fn lookup_symbol(&self, key: &str) -> Option<&Symbol> {
        for scope in self.scopes.iter().rev() {
            if let Some(symbol) = scope.get(key) {
                return Some(symbol);
            }
        }
        None
    }

    fn curr_scope(&mut self) -> &mut HashMap<String, Symbol> {
        self.scopes.last_mut().unwrap()
    }

    fn declare_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::FunDecl(fun_decl) => {
                let name = &fun_decl.ident.node;
                if self.curr_scope().get(name).is_some() {
                    self.report(ResolverError::DuplicateFunction {
                        src: self.source.to_string(),
                        span: fun_decl.ident.span,
                        name: name.clone(),
                    });
                    return;
                }
                self.curr_scope().insert(
                    name.clone(),
                    Symbol::Function {
                        params: fun_decl.params.clone(),
                        generics: fun_decl.generics.clone(),
                    },
                );
            }
            Stmt::StructDecl(struct_decl) => {
                let name = &struct_decl.ident.node;
                if self.curr_scope().get(name).is_some() {
                    self.report(ResolverError::DuplicateStruct {
                        src: self.source.clone(),
                        span: struct_decl.ident.span,
                        name: name.clone(),
                    })
                }
                self.curr_scope().insert(
                    name.clone(),
                    Symbol::Struct {
                        fields: struct_decl.fields.clone(),
                    },
                );
            }
            _ => {}
        }
    }

    fn resolve_unresolved_type(
        &mut self,
        unresolved_type: &AstNode<UnresolvedType>,
        generic_params: &HashSet<String>,
    ) -> Result<ResolvedType, ResolverError> {
        let ty = match &unresolved_type.node {
            UnresolvedType::Named(ident) => match ident.node.as_str() {
                "Int" => ResolvedType::Int,
                "Float" => ResolvedType::Float,
                "String" => ResolvedType::String,
                "Bool" => ResolvedType::Bool,
                name if generic_params.contains(name) => ResolvedType::Generic(name.to_string()),
                name => match self.lookup_symbol(name) {
                    Some(Symbol::Struct { fields }) => ResolvedType::Struct {
                        name: name.to_string(),
                        fields: fields
                            .clone()
                            .iter()
                            .map(|f| {
                                let resolved = self.resolve_unresolved_type(&f.type_annotation, generic_params)?;
                                Ok((f.name.node.clone(), resolved))
                            })
                            .collect::<Result<Vec<_>, ResolverError>>()?,
                    },
                    _ => {
                        return Err(UndefinedType {
                            src: self.source.to_string(),
                            span: unresolved_type.span,
                            name: name.to_string(),
                        });
                    }
                },
            },
            UnresolvedType::Function { params, return_type } => {
                let resolved_params = params
                    .iter()
                    .map(|p| self.resolve_unresolved_type(p, generic_params))
                    .collect::<Result<Vec<_>, ResolverError>>()?;
                let resolved_return = Box::new(self.resolve_unresolved_type(return_type, generic_params)?);
                ResolvedType::Function {
                    params: resolved_params,
                    return_ty: resolved_return,
                }
            }
            UnresolvedType::Generic { base, args } => match &base.node {
                UnresolvedType::Named(ident) if ident.node == "Vec" => {
                    if let Some(first_arg) = args.first() {
                        let element_type = self.resolve_unresolved_type(first_arg, generic_params)?;
                        ResolvedType::Vec(Box::new(element_type))
                    } else {
                        return Err(UndefinedType {
                            src: self.source.clone(),
                            span: base.span,
                            name: "Vec".to_string(),
                        });
                    }
                }
                _ => {
                    let base_type = self.resolve_unresolved_type(base, generic_params)?;
                    return Err(UndefinedType {
                        src: self.source.clone(),
                        span: base.span,
                        name: format!("{:?}", base_type),
                    });
                }
            },
        };
        Ok(ty)
    }

    fn resolve_stmt(&mut self, stmt: &AstNode<Stmt>) {
        match &stmt.node {
            Stmt::ExprStmtNode(expr_stmt) => self.resolve_expr(&expr_stmt.expr),
            Stmt::VarDecl(var_decl) => {
                if let Some(init) = &var_decl.initializer {
                    self.resolve_expr(init);
                }

                if let Some(annotation) = &var_decl.type_annotation {
                    match self.resolve_unresolved_type(annotation, &HashSet::new()) {
                        Ok(resolved_type) => {
                            self.resolution_map.insert(var_decl.ident.node_id, resolved_type);
                        }
                        Err(err) => self.report(err),
                    }
                }

                self.curr_scope().insert(
                    var_decl.ident.node.clone(),
                    Symbol::Variable {
                        initialized: var_decl.initializer.is_some(),
                    },
                );
            }
            Stmt::FunDecl(fun_decl) => {
                self.curr_scope().insert(
                    fun_decl.ident.node.clone(),
                    Symbol::Function {
                        params: fun_decl.params.clone(),
                        generics: fun_decl.generics.clone(),
                    },
                );

                self.scopes.push(HashMap::new());

                let generic_params: HashSet<String> = fun_decl.generics.iter().map(|g| g.node.clone()).collect();
                let mut seen_params = HashSet::new();

                for param in &fun_decl.params {
                    let param_name = &param.name.node;
                    if !seen_params.insert(param_name.clone()) {
                        self.report(DuplicateParameter {
                            src: self.source.to_string(),
                            span: param.name.span,
                            function_name: fun_decl.ident.node.clone(),
                        });
                        continue;
                    }

                    match self.resolve_unresolved_type(&param.type_annotation, &generic_params) {
                        Ok(resolved_type) => {
                            self.resolution_map.insert(param.type_annotation.node_id, resolved_type);
                        }
                        Err(err) => self.report(err),
                    }

                    self.curr_scope()
                        .insert(param.name.node.clone(), Symbol::Variable { initialized: true });
                }

                match self.resolve_unresolved_type(&fun_decl.return_type, &generic_params) {
                    Ok(resolved_type) => {
                        self.resolution_map.insert(fun_decl.return_type.node_id, resolved_type);
                    }
                    Err(err) => self.report(err),
                }

                let prev_inside_fn = self.inside_fn;
                self.inside_fn = true;
                for stmt in &fun_decl.body.node.statements {
                    self.resolve_stmt(stmt);
                }
                self.inside_fn = prev_inside_fn;
                self.scopes.pop();
            }
            Stmt::StructDecl(struct_decl) => {
                let name = struct_decl.ident.node.clone();
                self.curr_scope().insert(
                    name.clone(),
                    Symbol::Struct {
                        fields: struct_decl.fields.clone(),
                    },
                );
            }
            Stmt::While(while_stmt) => {
                self.resolve_expr(&while_stmt.condition);
                self.resolve_stmts(&while_stmt.body.node.statements);
            }
            Stmt::For(for_stmt) => {
                if let Some(init) = &for_stmt.initializer {
                    self.resolve_stmt(init);
                }
                self.resolve_expr(&for_stmt.condition);

                if let Some(incr) = &for_stmt.increment {
                    self.resolve_expr(incr);
                }
                self.resolve_stmts(&for_stmt.body.node.statements);
            }
            Stmt::Return(return_stmt) => {
                if !self.inside_fn {
                    self.report(ReturnOutsideFunction {
                        src: self.source.clone(),
                        span: stmt.span,
                    });
                } else if let Some(return_expr) = &return_stmt.expr {
                    self.resolve_expr(return_expr);
                }
            }
        }
    }

    fn resolve_stmts(&mut self, stmts: &Vec<AstNode<Stmt>>) {
        self.scopes.push(HashMap::new());
        for stmt in stmts {
            self.resolve_stmt(stmt);
        }
        self.scopes.pop();
    }

    fn resolve_expr(&mut self, expr: &AstNode<Expr>) {
        match &expr.node {
            Expr::FieldAssign(field_assign) => {
                self.resolve_expr(&field_assign.receiver);
                self.resolve_expr(&field_assign.value);
            }
            Expr::FieldAccess(field_access) => {
                self.resolve_expr(&field_access.receiver);
            }
            Expr::StructInit(struct_init) => match self.lookup_symbol(&struct_init.name.node).cloned() {
                None => {
                    self.report(UndefinedVariable {
                        src: self.source.clone(),
                        span: struct_init.name.span,
                        name: struct_init.name.node.clone(),
                    });
                }
                Some(Symbol::Struct { fields: _ }) => {
                    for (_, value) in &struct_init.fields {
                        self.resolve_expr(value);
                    }
                }
                Some(_) => {
                    self.report(ResolverError::NotAStruct {
                        src: self.source.clone(),
                        span: struct_init.name.span,
                        name: struct_init.name.node.clone(),
                    });
                }
            },
            Expr::Literal(_) => {}
            Expr::Block(block) => {
                self.scopes.push(HashMap::new());
                for stmt in &block.statements {
                    self.resolve_stmt(stmt);
                }
                if let Some(expr) = &block.expr {
                    self.resolve_expr(expr)
                }

                self.scopes.pop();
            }
            Expr::If(if_expr) => {
                self.resolve_expr(&if_expr.condition);
                self.resolve_stmts(&if_expr.then_branch.node.statements);
                if let Some(else_branch) = &if_expr.else_branch {
                    self.resolve_stmts(&else_branch.node.statements);
                }
            }
            Expr::MethodCall(method_call) => {
                self.resolve_expr(&method_call.receiver);

                for arg in &method_call.arguments {
                    self.resolve_expr(arg);
                }
            }
            Expr::Unary(unary_expr) => {
                self.resolve_expr(unary_expr.expr.deref());
            }
            Expr::Binary(binary_expr) => {
                self.resolve_expr(binary_expr.left.deref());
                self.resolve_expr(binary_expr.right.deref());
            }
            Expr::Grouping(grouping) => {
                self.resolve_expr(grouping.deref());
            }
            Expr::Variable(variable_expr) => match self.lookup_symbol(variable_expr.node.as_str()) {
                Some(Symbol::Variable { initialized: false }) => self.report(UninitializedVariable {
                    src: self.source.clone(),
                    span: variable_expr.span,
                    name: variable_expr.node.clone(),
                }),
                None => self.report(UndefinedVariable {
                    src: self.source.clone(),
                    span: variable_expr.span,
                    name: variable_expr.node.clone(),
                }),
                _ => {}
            },
            Expr::Assign(assign) => {
                match self.lookup_symbol(assign.target.node.as_str()) {
                    None => self.report(UndefinedVariable {
                        src: self.source.clone(),
                        span: assign.target.span,
                        name: assign.target.node.clone(),
                    }),
                    Some(_) => {
                        for scope in self.scopes.iter_mut().rev() {
                            if let Some(symbol) = scope.get_mut(&assign.target.node) {
                                *symbol = Symbol::Variable { initialized: true };
                                break;
                            }
                        }
                    }
                }

                self.resolve_expr(&assign.value);
            }
            Expr::Logical(logical_expr) => {
                self.resolve_expr(logical_expr.left.deref());
                self.resolve_expr(logical_expr.right.deref());
            }
            Expr::Call(call) => {
                if let Expr::Variable(ident) = &call.callee.deref().node {
                    if self.lookup_symbol(&ident.node).is_none() {
                        self.report(UndefinedFunction {
                            src: self.source.clone(),
                            span: ident.span,
                            name: ident.node.clone(),
                        })
                    }
                }
                for argument in &call.arguments {
                    self.resolve_expr(argument);
                }
            }
            Expr::Lambda(lambda) => {
                self.scopes.push(HashMap::new());
                for param in &lambda.parameters {
                    if self.curr_scope().get(param.name.node.as_str()).is_some() {
                        self.report(DuplicateLambdaParameter {
                            src: self.source.to_string(),
                            span: param.name.span,
                        })
                    } else {
                        self.curr_scope()
                            .insert(param.name.node.clone(), Symbol::Variable { initialized: true });
                    }
                }

                let prev_inside_fn = self.inside_fn;
                self.inside_fn = true;
                for stmt in &lambda.body.node.statements {
                    self.resolve_stmt(stmt);
                }
                self.inside_fn = prev_inside_fn;
                self.scopes.pop();
            }
        }
    }
}
