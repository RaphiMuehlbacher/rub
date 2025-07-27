use crate::hir::{DefMap, HirNode, HirProgram, LiteralExpr, ResolvedType};
use crate::mir::{MirNode, MirProgram, VarDeclStmt};
use crate::type_inferrer::{Type, TypeDatabase};
use crate::{hir, mir};

pub struct HirLowerer<'a> {
    pub hir_program: &'a HirProgram,
    pub def_map: &'a DefMap,
    pub type_db: &'a TypeDatabase,
}

pub struct HirLowererResult {
    pub mir_program: MirProgram,
}
impl<'a> HirLowerer<'a> {
    pub fn new(hir_program: &'a HirProgram, def_map: &'a DefMap, type_db: &'a TypeDatabase) -> Self {
        Self {
            hir_program,
            def_map,
            type_db,
        }
    }

    pub fn lower(&mut self) -> HirLowererResult {
        let mut statements = vec![];
        for stmt in &self.hir_program.statements {
            statements.push(self.lower_stmt(&stmt));
        }

        HirLowererResult {
            mir_program: MirProgram {
                statements,
                span: self.hir_program.span,
            },
        }
    }

    pub fn lower_stmt(&mut self, stmt: &HirNode<hir::Stmt>) -> MirNode<mir::Stmt> {
        match &stmt.node {
            hir::Stmt::ExprStmtNode(expr_stmt) => MirNode::new(
                mir::Stmt::ExprStmtNode(mir::ExprStmt {
                    expr: self.lower_expr(&expr_stmt.expr),
                }),
                stmt.span,
            ),
            hir::Stmt::VarDecl(var_decl) => {
                let initializer = var_decl.initializer.as_ref().map(|init| self.lower_expr(init));
                let type_annotation = var_decl.type_annotation.as_ref().map(|ty| self.lower_type(ty));

                MirNode::new(
                    mir::Stmt::VarDecl(VarDeclStmt {
                        ident: mir::Ident::from_ir(&var_decl.ident),
                        initializer,
                        type_annotation,
                    }),
                    stmt.span,
                )
            }
            hir::Stmt::FunDecl(fun_decl) => {
                let params = fun_decl
                    .params
                    .iter()
                    .map(|p| {
                        let annotation = self.lower_type(&p.type_annotation);
                        mir::TypedIdent {
                            name: mir::Ident::from_ir(&p.name),
                            type_annotation: annotation,
                        }
                    })
                    .collect();
                let generics = fun_decl.generics.iter().map(|g| mir::Ident::from_ir(&g)).collect();
                MirNode::new(
                    mir::Stmt::FunDecl(mir::FunDeclStmt {
                        ident: mir::Ident::from_ir(&fun_decl.ident),
                        params,
                        generics,
                        return_type: self.lower_type(&fun_decl.return_type),
                        body: MirNode::new(
                            mir::BlockExpr {
                                statements: fun_decl.body.node.statements.iter().map(|s| self.lower_stmt(s)).collect(),
                                expr: fun_decl.body.node.expr.as_ref().map(|b| Box::new(self.lower_expr(b))),
                            },
                            fun_decl.body.span,
                        ),
                    }),
                    stmt.span,
                )
            }
            hir::Stmt::StructDecl(struct_decl) => {
                let fields = struct_decl
                    .fields
                    .iter()
                    .map(|f| {
                        let annotation = self.lower_type(&f.type_annotation);
                        mir::TypedIdent {
                            name: mir::Ident::from_ir(&f.name),
                            type_annotation: annotation,
                        }
                    })
                    .collect();

                MirNode::new(
                    mir::Stmt::StructDecl(mir::StructDeclStmt {
                        ident: mir::Ident::from_ir(&struct_decl.ident),
                        fields,
                    }),
                    stmt.span,
                )
            }
            hir::Stmt::While(while_stmt) => MirNode::new(
                mir::Stmt::While(mir::WhileStmt {
                    condition: self.lower_expr(&while_stmt.condition),
                    body: self.lower_block_expr(&while_stmt.body),
                }),
                stmt.span,
            ),
            hir::Stmt::Return(return_stmt) => MirNode::new(
                mir::Stmt::Return(mir::ReturnStmt {
                    expr: return_stmt.expr.as_ref().map(|e| self.lower_expr(e)),
                }),
                stmt.span,
            ),
        }
    }

    pub fn lower_expr(&mut self, expr: &HirNode<hir::Expr>) -> MirNode<mir::Expr> {
        match &expr.node {
            hir::Expr::Literal(literal_expr) => {
                let lit = match literal_expr {
                    LiteralExpr::Int(i) => mir::LiteralExpr::Int(*i),
                    LiteralExpr::Float(f) => mir::LiteralExpr::Float(*f),
                    LiteralExpr::String(s) => mir::LiteralExpr::String(s.clone()),
                    LiteralExpr::Bool(b) => mir::LiteralExpr::Bool(*b),
                    LiteralExpr::VecLiteral(v) => mir::LiteralExpr::VecLiteral(v.iter().map(|e| self.lower_expr(e)).collect()),
                    LiteralExpr::Nil => mir::LiteralExpr::Nil,
                };
                MirNode::new(mir::Expr::Literal(lit), expr.span)
            }
            hir::Expr::Unary(unary_expr) => {
                let op = match unary_expr.op.node {
                    hir::UnaryOp::Minus => mir::UnaryOp::Minus,
                    hir::UnaryOp::Bang => mir::UnaryOp::Bang,
                };
                MirNode::new(
                    mir::Expr::Unary(mir::UnaryExpr {
                        op: MirNode::new(op, unary_expr.op.span),
                        expr: Box::from(self.lower_expr(&unary_expr.expr)),
                    }),
                    expr.span,
                )
            }
            hir::Expr::Binary(binary_expr) => {
                let op = match binary_expr.op.node {
                    hir::BinaryOp::Minus => mir::BinaryOp::Minus,
                    hir::BinaryOp::Plus => mir::BinaryOp::Plus,
                    hir::BinaryOp::Star => mir::BinaryOp::Star,
                    hir::BinaryOp::Slash => mir::BinaryOp::Slash,
                    hir::BinaryOp::Greater => mir::BinaryOp::Greater,
                    hir::BinaryOp::GreaterEqual => mir::BinaryOp::GreaterEqual,
                    hir::BinaryOp::Less => mir::BinaryOp::Less,
                    hir::BinaryOp::LessEqual => mir::BinaryOp::LessEqual,
                    hir::BinaryOp::EqualEqual => mir::BinaryOp::EqualEqual,
                    hir::BinaryOp::BangEqual => mir::BinaryOp::BangEqual,
                };

                MirNode::new(
                    mir::Expr::Binary(mir::BinaryExpr {
                        op: MirNode::new(op, binary_expr.op.span),
                        left: Box::new(self.lower_expr(&binary_expr.left)),
                        right: Box::new(self.lower_expr(&binary_expr.right)),
                    }),
                    expr.span,
                )
            }

            hir::Expr::Grouping(grouping) => MirNode::new(mir::Expr::Grouping(Box::new(self.lower_expr(grouping))), expr.span),
            hir::Expr::Variable(variable) => MirNode::new(mir::Expr::Variable(mir::Ident::from_ir(variable)), expr.span),
            hir::Expr::Assign(assign_expr) => MirNode::new(
                mir::Expr::Assign(mir::AssignExpr {
                    target: mir::Ident::from_ir(&assign_expr.target),
                    value: Box::new(self.lower_expr(&assign_expr.value)),
                }),
                expr.span,
            ),
            hir::Expr::Logical(logical_expr) => {
                let op = match logical_expr.op.node {
                    hir::LogicalOp::And => mir::LogicalOp::And,
                    hir::LogicalOp::Or => mir::LogicalOp::Or,
                };
                MirNode::new(
                    mir::Expr::Logical(mir::LogicalExpr {
                        op: MirNode::new(op, logical_expr.op.span),
                        left: Box::new(self.lower_expr(&logical_expr.left)),
                        right: Box::new(self.lower_expr(&logical_expr.right)),
                    }),
                    expr.span,
                )
            }
            hir::Expr::Call(call_expr) => MirNode::new(
                mir::Expr::Call(mir::CallExpr {
                    callee: Box::new(self.lower_expr(&call_expr.callee)),
                    arguments: call_expr.arguments.iter().map(|a| self.lower_expr(a)).collect(),
                }),
                expr.span,
            ),
            hir::Expr::Lambda(lambda_expr) => {
                todo!()
            }
            hir::Expr::Block(block) => MirNode::new(
                mir::Expr::Block(self.lower_block_expr(&HirNode::new(block.clone(), expr.span)).node),
                expr.span,
            ),
            hir::Expr::If(if_expr) => MirNode::new(
                mir::Expr::If(mir::IfExpr {
                    condition: Box::new(self.lower_expr(&if_expr.condition)),
                    then_branch: self.lower_block_expr(&if_expr.then_branch),
                    else_branch: if_expr.else_branch.as_ref().map(|else_branch| self.lower_block_expr(else_branch)),
                }),
                expr.span,
            ),
            hir::Expr::MethodCall(method_call) => {
                // let a = AStruct
                // a.show() -> AStruct::show(a)
                let mut arguments = vec![self.lower_expr(&method_call.receiver)];
                arguments.extend(method_call.arguments.iter().map(|a| self.lower_expr(a)));

                let def_id = match &method_call.receiver.node {
                    hir::Expr::Variable(ident) => ident.def_id,
                    _ => panic!(),
                };
                let callee_ty = self.type_db.def_types.get(&def_id).unwrap();
                let callee = Box::new(MirNode::new(
                    mir::Expr::Variable(mir::Ident::new(
                        &format!("{}__{}", callee_ty.to_string(), method_call.method.name.node),
                        method_call.method.name.span,
                        method_call.method.def_id,
                    )),
                    method_call.receiver.span,
                ));

                MirNode::new(mir::Expr::Call(mir::CallExpr { callee, arguments }), expr.span)
            }
            hir::Expr::StructInit(struct_init) => MirNode::new(
                mir::Expr::StructInit(mir::StructInitExpr {
                    name: mir::Ident::from_ir(&struct_init.name),
                    fields: struct_init
                        .fields
                        .iter()
                        .map(|(name, expr)| (mir::Ident::from_ir(name), self.lower_expr(expr)))
                        .collect(),
                }),
                expr.span,
            ),
            hir::Expr::FieldAccess(field_access) => MirNode::new(
                mir::Expr::FieldAccess(mir::FieldAccessExpr {
                    receiver: Box::new(self.lower_expr(&field_access.receiver)),
                    field: MirNode::new(field_access.field.node.clone(), field_access.field.span),
                }),
                expr.span,
            ),
            hir::Expr::FieldAssign(field_assign) => MirNode::new(
                mir::Expr::FieldAssign(mir::FieldAssignExpr {
                    receiver: Box::new(self.lower_expr(&field_assign.receiver)),
                    field: MirNode::new(field_assign.field.node.clone(), field_assign.field.span),
                    value: Box::new(self.lower_expr(&field_assign.value)),
                }),
                expr.span,
            ),
        }
    }

    pub fn lower_block_expr(&mut self, block: &HirNode<hir::BlockExpr>) -> MirNode<mir::BlockExpr> {
        MirNode::new(
            mir::BlockExpr {
                statements: block.node.statements.iter().map(|s| self.lower_stmt(s)).collect(),
                expr: block.node.expr.as_ref().map(|e| Box::new(self.lower_expr(e))),
            },
            block.span,
        )
    }
    pub fn lower_type(&mut self, ty: &ResolvedType) -> Type {
        match ty {
            ResolvedType::Named(def_id) => self.type_db.def_types.get(def_id).unwrap().clone(),
            ResolvedType::Function { params, return_type } => {
                todo!()
            }
            ResolvedType::Generic { base, args } => {
                todo!()
            }
        }
    }
}
