use crate::ast::{AstNode, AstProgram, UnresolvedType};
use crate::ir::{DefMap, IrNode, IrProgram, ResolutionMap};
use crate::{ast, ir};
use miette::Report;

pub struct AstLowererResult<'a> {
    pub errors: &'a Vec<Report>,
    pub ir_program: IrProgram,
}

pub struct AstLowerer<'a> {
    ast_program: &'a AstProgram,
    errors: Vec<Report>,
    resolution_map: &'a ResolutionMap,
    def_map: &'a DefMap,
}

impl<'a> AstLowerer<'a> {
    pub fn new(ast_program: &'a AstProgram, resolution_map: &'a ResolutionMap, def_map: &'a DefMap) -> Self {
        Self {
            errors: vec![],
            ast_program,
            resolution_map,
            def_map,
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
                let type_annotation = var_decl.type_annotation.as_ref().map(|ty| self.resolution_map.get(ty.node_id));

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
                        type_annotation: self.resolution_map.get(p.type_annotation.node_id),
                    })
                    .collect();
                let generics = fun_decl.generics.iter().map(|g| IrNode::new(g.node.clone(), g.span)).collect();
                let body = self.lower_block_expr(&fun_decl.body);
                let return_type = self.resolution_map.get(fun_decl.return_type.node_id);

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
                    .map(|f| {
                        let annotation_def_id = self.resolution_map.get(f.type_annotation.node_id);

                        ir::TypedIdent {
                            name: IrNode::new(f.name.node.clone(), f.name.span),
                            type_annotation: annotation_def_id,
                        }
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
            ast::Expr::Literal(literal_expr) => {
                let lit = match literal_expr {
                    ast::LiteralExpr::Nil => ir::LiteralExpr::Nil,
                    ast::LiteralExpr::Float(f) => ir::LiteralExpr::Float(*f),
                    ast::LiteralExpr::Int(i) => ir::LiteralExpr::Int(*i),
                    ast::LiteralExpr::String(s) => ir::LiteralExpr::String(s.clone()),
                    ast::LiteralExpr::Bool(b) => ir::LiteralExpr::Bool(*b),
                    ast::LiteralExpr::VecLiteral(v) => ir::LiteralExpr::VecLiteral(v.iter().map(|e| self.lower_expr(e)).collect()),
                };
                IrNode::new(ir::Expr::Literal(lit), expr.span)
            }
            ast::Expr::Unary(unary_expr) => {
                let op = match unary_expr.op.node {
                    ast::UnaryOp::Minus => ir::UnaryOp::Minus,
                    ast::UnaryOp::Bang => ir::UnaryOp::Bang,
                };
                IrNode::new(
                    ir::Expr::Unary(ir::UnaryExpr {
                        op: IrNode::new(op, unary_expr.op.span),
                        expr: Box::from(self.lower_expr(&unary_expr.expr)),
                    }),
                    expr.span,
                )
            }
            ast::Expr::Binary(binary_expr) => {
                let op = match binary_expr.op.node {
                    ast::BinaryOp::Minus => ir::BinaryOp::Minus,
                    ast::BinaryOp::Plus => ir::BinaryOp::Plus,
                    ast::BinaryOp::Star => ir::BinaryOp::Star,
                    ast::BinaryOp::Slash => ir::BinaryOp::Slash,
                    ast::BinaryOp::Greater => ir::BinaryOp::Greater,
                    ast::BinaryOp::GreaterEqual => ir::BinaryOp::GreaterEqual,
                    ast::BinaryOp::Less => ir::BinaryOp::Less,
                    ast::BinaryOp::LessEqual => ir::BinaryOp::LessEqual,
                    ast::BinaryOp::EqualEqual => ir::BinaryOp::EqualEqual,
                    ast::BinaryOp::BangEqual => ir::BinaryOp::BangEqual,
                };

                IrNode::new(
                    ir::Expr::Binary(ir::BinaryExpr {
                        op: IrNode::new(op, binary_expr.op.span),
                        left: Box::new(self.lower_expr(&binary_expr.left)),
                        right: Box::new(self.lower_expr(&binary_expr.right)),
                    }),
                    expr.span,
                )
            }
            ast::Expr::Grouping(grouping) => IrNode::new(ir::Expr::Grouping(Box::new(self.lower_expr(grouping))), expr.span),
            ast::Expr::Variable(variable) => IrNode::new(ir::Expr::Variable(IrNode::new(variable.node.clone(), variable.span)), expr.span),
            ast::Expr::Assign(assign_expr) => IrNode::new(
                ir::Expr::Assign(ir::AssignExpr {
                    target: IrNode::new(assign_expr.target.node.clone(), assign_expr.target.span),
                    value: Box::new(self.lower_expr(&assign_expr.value)),
                }),
                expr.span,
            ),
            ast::Expr::Logical(logical_expr) => {
                let op = match logical_expr.op.node {
                    ast::LogicalOp::And => ir::LogicalOp::And,
                    ast::LogicalOp::Or => ir::LogicalOp::Or,
                };
                IrNode::new(
                    ir::Expr::Logical(ir::LogicalExpr {
                        op: IrNode::new(op, logical_expr.op.span),
                        left: Box::new(self.lower_expr(&logical_expr.left)),
                        right: Box::new(self.lower_expr(&logical_expr.right)),
                    }),
                    expr.span,
                )
            }
            ast::Expr::Call(call_expr) => IrNode::new(
                ir::Expr::Call(ir::CallExpr {
                    callee: Box::new(self.lower_expr(&call_expr.callee)),
                    arguments: call_expr.arguments.iter().map(|arg| self.lower_expr(arg)).collect(),
                }),
                expr.span,
            ),
            ast::Expr::Lambda(lambda_expr) => IrNode::new(
                ir::Expr::Lambda(ir::LambdaExpr {
                    parameters: lambda_expr
                        .parameters
                        .iter()
                        .map(|p| ir::TypedIdent {
                            name: IrNode::new(p.name.node.clone(), p.name.span),
                            type_annotation: self.resolution_map.get(p.type_annotation.node_id),
                        })
                        .collect(),
                    body: Box::new(self.lower_block_expr(&lambda_expr.body)),
                    return_type: self.resolution_map.get(lambda_expr.return_type.node_id),
                }),
                expr.span,
            ),
            ast::Expr::Block(block) => IrNode::new(
                ir::Expr::Block(self.lower_block_expr(&AstNode::new(block.clone(), expr.span)).node),
                expr.span,
            ),
            ast::Expr::If(if_expr) => IrNode::new(
                ir::Expr::If(ir::IfExpr {
                    condition: Box::new(self.lower_expr(&if_expr.condition)),
                    then_branch: self.lower_block_expr(&if_expr.then_branch),
                    else_branch: if_expr.else_branch.as_ref().map(|else_branch| self.lower_block_expr(else_branch)),
                }),
                expr.span,
            ),
            ast::Expr::MethodCall(method_call) => IrNode::new(
                ir::Expr::MethodCall(ir::MethodCallExpr {
                    receiver: Box::new(self.lower_expr(&method_call.receiver)),
                    method: IrNode::new(method_call.method.node.clone(), method_call.method.span),
                    arguments: method_call.arguments.iter().map(|arg| self.lower_expr(arg)).collect(),
                }),
                expr.span,
            ),
            ast::Expr::StructInit(struct_init) => IrNode::new(
                ir::Expr::StructInit(ir::StructInitExpr {
                    name: IrNode::new(struct_init.name.node.clone(), struct_init.name.span),
                    fields: struct_init
                        .fields
                        .iter()
                        .map(|(name, value)| (IrNode::new(name.node.clone(), name.span), self.lower_expr(value)))
                        .collect(),
                }),
                expr.span,
            ),
            ast::Expr::FieldAccess(field_access) => IrNode::new(
                ir::Expr::FieldAccess(ir::FieldAccessExpr {
                    receiver: Box::new(self.lower_expr(&field_access.receiver)),
                    field: IrNode::new(field_access.field.node.clone(), field_access.field.span),
                }),
                expr.span,
            ),
            ast::Expr::FieldAssign(field_assign) => IrNode::new(
                ir::Expr::FieldAssign(ir::FieldAssignExpr {
                    receiver: Box::new(self.lower_expr(&field_assign.receiver)),
                    field: IrNode::new(field_assign.field.node.clone(), field_assign.field.span),
                    value: Box::new(self.lower_expr(&field_assign.value)),
                }),
                expr.span,
            ),
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
}
