use crate::ast::{
    AssignExpr, BinaryExpr, BinaryOp, BlockStmt, CallExpr, Expr, FunDeclStmt, Ident, IfStmt,
    LambdaExpr, LiteralExpr, LogicalExpr, Program, Stmt, Typed, UnaryExpr, UnaryOp, VarDeclStmt,
    WhileStmt,
};
use crate::error::TypeInferrerError;
use crate::error::TypeInferrerError::TypeMismatch;
use crate::type_inferrer::Type::TypeVar;
use miette::{Report, SourceSpan};
use std::collections::HashMap;
use std::ops::Deref;

pub type TypeVarId = usize;

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Float,
    Bool,
    String,
    Nil,
    TypeVar(TypeVarId),
}

pub struct TypeInferrer<'a> {
    program: &'a Program,
    source: String,
    errors: Vec<Report>,
    pub type_env: HashMap<TypeVarId, Type>,
    pub var_env: HashMap<String, TypeVarId>,
}

impl<'a> TypeInferrer<'a> {
    pub fn new(ast: &'a Program, source: String) -> Self {
        Self {
            program: ast,
            source,
            errors: vec![],
            type_env: HashMap::new(),
            var_env: HashMap::new(),
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
            _ => ty.clone(),
        }
    }

    fn unify(
        &mut self,
        left: Type,
        right: Type,
        span: SourceSpan,
    ) -> Result<Type, TypeInferrerError> {
        let left_ty = self.lookup_type(&left);
        let right_ty = self.lookup_type(&right);

        match (left_ty, right_ty) {
            (Type::Float, Type::Float) => Ok(Type::Float),
            (Type::String, Type::String) => Ok(Type::String),
            (Type::Bool, Type::Bool) => Ok(Type::Bool),
            (Type::Nil, Type::Nil) => Ok(Type::Nil),

            (ty, TypeVar(id)) | (TypeVar(id), ty) => {
                self.type_env.insert(id, ty);
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

    pub fn infer(&mut self) -> &Vec<Report> {
        for stmt in &self.program.statements {
            if let Err(err) = self.infer_stmt(stmt) {
                self.report(err);
            }
        }
        &self.errors
    }

    fn infer_stmt(&mut self, stmt: &Stmt) -> Result<(), TypeInferrerError> {
        match stmt {
            Stmt::ExprStmt(expr_stmt) => self.infer_expr_stmt(expr_stmt),
            Stmt::PrintStmt(print_stmt) => self.infer_print_stmt(print_stmt),
            Stmt::VarDecl(var_decl) => self.infer_var_decl(var_decl),
            Stmt::FunDecl(fun_decl) => self.infer_fun_decl(fun_decl),
            Stmt::Block(block) => self.infer_block(block),
            Stmt::If(if_stmt) => self.infer_if_stmt(if_stmt),
            Stmt::While(while_stmt) => self.infer_while_stmt(while_stmt),
            Stmt::Return(return_stmt) => self.infer_return_stmt(return_stmt),
        }
    }

    fn infer_expr_stmt(&mut self, expr_stmt: &Typed<Expr>) -> Result<(), TypeInferrerError> {
        self.infer_expr(&expr_stmt.node);
        Ok(())
    }

    fn infer_print_stmt(&mut self, print_stmt: &Typed<Expr>) -> Result<(), TypeInferrerError> {
        todo!()
    }

    fn infer_var_decl(&mut self, var_decl: &Typed<VarDeclStmt>) -> Result<(), TypeInferrerError> {
        self.var_env.insert(
            var_decl.node.ident.node.clone(),
            var_decl.node.ident.type_id,
        );
        if let Some(init) = &var_decl.node.initializer {
            let init_type = self.infer_expr(init)?;

            self.unify(
                TypeVar(var_decl.node.ident.type_id),
                init_type,
                var_decl.node.ident.span,
            )?;
        }

        Ok(())
    }

    fn infer_fun_decl(&mut self, fun_decl: &Typed<FunDeclStmt>) -> Result<(), TypeInferrerError> {
        todo!()
    }

    fn infer_block(&mut self, block: &Typed<BlockStmt>) -> Result<(), TypeInferrerError> {
        todo!()
    }

    fn infer_if_stmt(&mut self, if_stmt: &Typed<IfStmt>) -> Result<(), TypeInferrerError> {
        todo!()
    }

    fn infer_while_stmt(&mut self, while_stmt: &Typed<WhileStmt>) -> Result<(), TypeInferrerError> {
        todo!()
    }

    fn infer_return_stmt(
        &mut self,
        return_stmt: &Typed<Option<Expr>>,
    ) -> Result<(), TypeInferrerError> {
        todo!()
    }

    fn infer_expr(&mut self, expr: &Expr) -> Result<Type, TypeInferrerError> {
        match expr {
            Expr::Literal(literal_expr) => self.infer_literal_expr(literal_expr),
            Expr::Unary(unary_expr) => self.infer_unary_expr(unary_expr),
            Expr::Binary(binary_expr) => self.infer_binary_expr(binary_expr),
            Expr::Grouping(grouping) => self.infer_grouping_expr(grouping),
            Expr::Variable(variable_expr) => self.infer_variable_expr(variable_expr),
            Expr::Assign(assign) => self.infer_assign_expr(assign),
            Expr::Logical(logical_expr) => self.infer_logical_expr(logical_expr),
            Expr::Call(call) => self.infer_call_expr(call),
            Expr::Lambda(lambda) => self.lambda_expr(lambda),
        }
    }

    fn infer_literal_expr(
        &mut self,
        literal_expr: &Typed<LiteralExpr>,
    ) -> Result<Type, TypeInferrerError> {
        let ty = match literal_expr.node {
            LiteralExpr::Number(_) => Type::Float,
            LiteralExpr::String(_) => Type::String,
            LiteralExpr::Bool(_) => Type::Bool,
            LiteralExpr::Nil => Type::Nil,
        };

        self.type_env.insert(literal_expr.type_id, ty);
        Ok(TypeVar(literal_expr.type_id))
    }

    fn infer_unary_expr(
        &mut self,
        unary_expr: &Typed<UnaryExpr>,
    ) -> Result<Type, TypeInferrerError> {
        let right_ty = self.infer_expr(unary_expr.node.expr.deref())?;
        let result_ty = match unary_expr.node.op {
            UnaryOp::Bang => self.unify(right_ty, Type::Bool, unary_expr.node.expr.span())?,
            UnaryOp::Minus => self.unify(right_ty, Type::Float, unary_expr.node.expr.span())?,
        };

        self.type_env.insert(unary_expr.type_id, result_ty.clone());
        Ok(TypeVar(unary_expr.type_id))
    }

    fn infer_binary_expr(
        &mut self,
        binary_expr: &Typed<BinaryExpr>,
    ) -> Result<Type, TypeInferrerError> {
        let left = self.infer_expr(binary_expr.node.left.deref())?;
        let right = self.infer_expr(binary_expr.node.right.deref())?;

        let result_ty = match binary_expr.node.op {
            BinaryOp::Plus => {
                let left_ty = self.lookup_type(&left);
                let right_ty = self.lookup_type(&right);
                match (left_ty, right_ty) {
                    (Type::Float, Type::Float) => Type::Float,
                    (Type::String, Type::String) => Type::String,
                    _ => {
                        return Err(TypeMismatch {
                            src: self.source.clone(),
                            span: binary_expr.node.right.span(),
                            expected: left,
                            found: right,
                        })
                    }
                }
            }
            BinaryOp::Star | BinaryOp::Minus | BinaryOp::Slash => {
                self.unify(left, Type::Float, binary_expr.node.left.span())?;
                self.unify(right, Type::Float, binary_expr.node.right.span())?
            }
            BinaryOp::Greater | BinaryOp::GreaterEqual | BinaryOp::Less | BinaryOp::LessEqual => {
                self.unify(left, Type::Float, binary_expr.node.left.span())?;
                self.unify(right, Type::Float, binary_expr.node.right.span())?
            }
            BinaryOp::EqualEqual | BinaryOp::BangEqual => {
                self.unify(left, right, binary_expr.node.right.span())?
            }
        };

        self.type_env.insert(binary_expr.type_id, result_ty);
        Ok(TypeVar(binary_expr.type_id))
    }

    fn infer_grouping_expr(
        &mut self,
        grouping_expr: &Typed<Box<Expr>>,
    ) -> Result<Type, TypeInferrerError> {
        todo!()
    }

    fn infer_variable_expr(&mut self, variable_expr: &Ident) -> Result<Type, TypeInferrerError> {
        let var_id = self.var_env.get(variable_expr.node.as_str()).unwrap();
        Ok(TypeVar(var_id.clone()))
    }

    fn infer_assign_expr(
        &mut self,
        assign_expr: &Typed<AssignExpr>,
    ) -> Result<Type, TypeInferrerError> {
        let right_ty = self.infer_expr(assign_expr.node.value.deref())?;
        let left_var = self
            .var_env
            .get(assign_expr.node.target.node.as_str())
            .unwrap();

        self.unify(
            TypeVar(left_var.clone()),
            right_ty.clone(),
            assign_expr.node.value.deref().span(),
        )?;

        self.type_env.insert(assign_expr.type_id, right_ty);
        Ok(TypeVar(assign_expr.type_id))
    }

    fn infer_logical_expr(
        &mut self,
        logical_expr: &Typed<LogicalExpr>,
    ) -> Result<Type, TypeInferrerError> {
        todo!()
    }

    fn infer_call_expr(&mut self, call_expr: &Typed<CallExpr>) -> Result<Type, TypeInferrerError> {
        todo!()
    }

    fn lambda_expr(&mut self, lambda: &Typed<LambdaExpr>) -> Result<Type, TypeInferrerError> {
        todo!()
    }
}
