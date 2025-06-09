use crate::ast::{AstNode, AstProgram, UnresolvedType};
use crate::ir::{IrNode, IrProgram, ResolvedType};
use crate::{ast, ir};
use miette::Report;
use std::collections::HashMap;

pub struct AstLowererResult<'a> {
    pub errors: &'a Vec<Report>,
    pub ir_program: IrProgram,
}
pub struct AstLowerer<'a> {
    source: String,
    ast_program: &'a AstProgram,
    errors: Vec<Report>,
    resolution_map: HashMap<usize, ResolvedType>,
}

impl<'a> AstLowerer<'a> {
    pub fn new(ast_program: &'a AstProgram, source: String, resolution_map: HashMap<usize, ResolvedType>) -> Self {
        Self {
            source,
            errors: vec![],
            ast_program,
            resolution_map,
        }
    }

    pub fn lower(&mut self) -> AstLowererResult {
        let mut statements = vec![];
        for stmt in &self.ast_program.statements {
            statements.push(self.lower_stmt(&stmt));
        }

        AstLowererResult {
            errors: &self.errors,
            ir_program: IrProgram {
                statements,
                span: self.ast_program.span,
            },
        }
    }

    fn lower_stmt(&mut self, stmt: &AstNode<ast::Stmt>) -> IrNode<ir::Stmt> {
        match &stmt.node {
            ast::Stmt::ExprStmtNode(expr_stmt) => IrNode::new(
                ir::Stmt::ExprStmtNode(ir::ExprStmt {
                    expr: self.lower_expr(&expr_stmt.expr),
                }),
                stmt.span,
            ),
            ast::Stmt::VarDecl(var_decl) => {
                let name = IrNode::new(var_decl.ident.node.clone(), var_decl.ident.span);
                let initializer = var_decl.initializer.as_ref().map(|init| self.lower_expr(init));
                let type_annotation = var_decl.type_annotation.as_ref().map(|ty| self.lower_type(ty));
                IrNode::new(
                    ir::Stmt::VarDecl(ir::VarDeclStmt {
                        ident: name,
                        initializer,
                        type_annotation,
                    }),
                    stmt.span,
                )
            }
            ast::Stmt::FunDecl(fun_decl) => {
                let name = IrNode::new(fun_decl.ident.node.clone(), fun_decl.ident.span);
                let params = fun_decl
                    .params
                    .iter()
                    .map(|p| ir::TypedIdent {
                        name: ir::Ident::new(p.name.node.clone(), p.name.span),
                        type_annotation: self.lower_type(&p.type_annotation),
                    })
                    .collect();
                let generics = fun_decl.generics.iter().map(|g| IrNode::new(g.node.clone(), g.span)).collect();
                let body = self.lower_block_expr(&fun_decl.body);
                let return_type = self.lower_type(&fun_decl.return_type);

                IrNode::new(
                    ir::Stmt::FunDecl(ir::FunDeclStmt {
                        ident: name,
                        params,
                        body,
                        generics,
                        return_type,
                    }),
                    stmt.span,
                )
            }
            ast::Stmt::StructDecl(struct_decl) => {
                let name = IrNode::new(struct_decl.ident.node.clone(), struct_decl.ident.span);
                let fields = struct_decl
                    .fields
                    .iter()
                    .map(|f| ir::TypedIdent {
                        name: IrNode::new(f.name.node.clone(), f.name.span),
                        type_annotation: self.lower_type(&f.type_annotation),
                    })
                    .collect();

                IrNode::new(ir::Stmt::StructDecl(ir::StructDeclStmt { ident: name, fields }), stmt.span)
            }
            ast::Stmt::While(while_stmt) => IrNode::new(
                ir::Stmt::While(ir::WhileStmt {
                    condition: self.lower_expr(&while_stmt.condition),
                    body: self.lower_block_expr(&while_stmt.body),
                }),
                stmt.span,
            ),
            ast::Stmt::For(for_stmt) => {
                let mut block_stmts = vec![];

                if let Some(init) = &for_stmt.initializer {
                    block_stmts.push(self.lower_stmt(&init));
                }

                let mut while_body_stmts = vec![];
                for stmt in &for_stmt.body.node.statements {
                    while_body_stmts.push(self.lower_stmt(stmt));
                }
                if let Some(incr) = &for_stmt.increment {
                    while_body_stmts.push(IrNode::new(
                        ir::Stmt::ExprStmtNode(ir::ExprStmt {
                            expr: self.lower_expr(incr),
                        }),
                        incr.span,
                    ))
                }
                let while_stmt = ir::Stmt::While(ir::WhileStmt {
                    condition: self.lower_expr(&for_stmt.condition),
                    body: IrNode::new(
                        ir::BlockExpr {
                            statements: while_body_stmts,
                            expr: None,
                        },
                        for_stmt.body.span,
                    ),
                });

                block_stmts.push(IrNode::new(while_stmt, stmt.span));
                IrNode::new(
                    ir::Stmt::ExprStmtNode(ir::ExprStmt {
                        expr: IrNode::new(
                            ir::Expr::Block(ir::BlockExpr {
                                statements: block_stmts,
                                expr: None,
                            }),
                            stmt.span,
                        ),
                    }),
                    stmt.span,
                )
            }

            ast::Stmt::Return(return_stmt) => IrNode::new(
                ir::Stmt::Return(ir::ReturnStmt {
                    expr: return_stmt.expr.as_ref().map(|e| self.lower_expr(e)),
                }),
                stmt.span,
            ),
        }
    }

    fn lower_expr(&mut self, expr: &AstNode<ast::Expr>) -> IrNode<ir::Expr> {
        match &expr.node {
            ast::Expr::Literal(literal_expr) => {}
            ast::Expr::Unary(unary_expr) => {}
            ast::Expr::Binary(binary_expr) => {}
            ast::Expr::Grouping(grouping) => {}
            ast::Expr::Variable(variable) => {}
            ast::Expr::Assign(assign_expr) => {}
            ast::Expr::Logical(logical_expr) => {}
            ast::Expr::Call(call_expr) => {}
            ast::Expr::Lambda(lambda_expr) => {}
            ast::Expr::Block(block) => {}
            ast::Expr::If(if_expr) => {}
            ast::Expr::MethodCall(method_call) => {}
            ast::Expr::StructInit(struct_init) => {}
            ast::Expr::FieldAccess(field_access) => {}
            ast::Expr::FieldAssign(field_assign) => {}
        }
    }

    fn lower_block_expr(&mut self, block: &AstNode<ast::BlockExpr>) -> IrNode<ir::BlockExpr> {
        IrNode::new(
            ir::BlockExpr {
                statements: block.node.statements.iter().map(|s| self.lower_stmt(s)).collect(),
                expr: block.node.expr.as_ref().map(|e| Box::new(self.lower_expr(e))),
            },
            block.span,
        )
    }

    fn lower_type(&mut self, ty: &AstNode<UnresolvedType>) -> IrNode<ResolvedType> {
        IrNode::new(self.resolution_map.get(&ty.node_id).unwrap().clone(), ty.span)
    }
}
