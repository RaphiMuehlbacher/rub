use crate::ast::{AstNode, AstProgram};
use crate::hir::{DefId, DefMap, HirNode, HirProgram, ResolutionMap, ResolvedType, ScopeId, ScopeTree};
use crate::{ast, hir};
use miette::Report;
use std::collections::HashMap;

pub struct AstLowererResult<'a> {
    pub errors: &'a Vec<Report>,
    pub hir_program: HirProgram,
    pub function_bodies: &'a FunctionBodies,
}

pub struct FunctionBodies {
    map: HashMap<DefId, HirNode<hir::BlockExpr>>,
}

impl FunctionBodies {
    pub fn new() -> Self {
        Self { map: HashMap::new() }
    }

    pub fn insert(&mut self, def_id: DefId, body: HirNode<hir::BlockExpr>) {
        self.map.insert(def_id, body);
    }

    pub fn get(&self, def_id: DefId) -> &HirNode<hir::BlockExpr> {
        self.map.get(&def_id).unwrap()
    }
}

pub struct AstLowerer<'a> {
    ast_program: &'a AstProgram,
    errors: Vec<Report>,
    resolution_map: &'a ResolutionMap,
    scope_tree: &'a mut ScopeTree,
    def_map: &'a DefMap,
    current_scope: ScopeId,
    function_bodies: FunctionBodies,
}

impl<'a> AstLowerer<'a> {
    pub fn new(ast_program: &'a AstProgram, resolution_map: &'a ResolutionMap, scope_tree: &'a mut ScopeTree, def_map: &'a DefMap) -> Self {
        Self {
            errors: vec![],
            ast_program,
            resolution_map,
            scope_tree,
            def_map,
            current_scope: 1,
            function_bodies: FunctionBodies::new(),
        }
    }

    pub fn lower(&mut self) -> AstLowererResult {
        let mut statements = vec![];
        for stmt in &self.ast_program.statements {
            statements.push(self.lower_stmt(&stmt));
        }

        AstLowererResult {
            errors: &self.errors,
            hir_program: HirProgram {
                statements,
                span: self.ast_program.span,
            },
            function_bodies: &self.function_bodies,
        }
    }

    fn lower_stmt(&mut self, stmt: &AstNode<ast::Stmt>) -> HirNode<hir::Stmt> {
        match &stmt.node {
            ast::Stmt::ExprStmtNode(expr_stmt) => HirNode::new(
                hir::Stmt::ExprStmtNode(hir::ExprStmt {
                    expr: self.lower_expr(&expr_stmt.expr),
                }),
                stmt.span,
            ),
            ast::Stmt::VarDecl(var_decl) => {
                let initializer = var_decl.initializer.as_ref().map(|init| self.lower_expr(init));
                let type_annotation = var_decl.type_annotation.as_ref().map(|ty| self.lower_type(ty));

                HirNode::new(
                    hir::Stmt::VarDecl(hir::VarDeclStmt {
                        ident: hir::Ident::from_ast(&var_decl.ident, self.scope_tree, self.current_scope),
                        initializer,
                        type_annotation,
                    }),
                    stmt.span,
                )
            }
            ast::Stmt::FunDecl(fun_decl) => {
                let def_id = self.scope_tree.resolve_name(self.current_scope, &fun_decl.ident.node).unwrap();
                let def = self.def_map.get(def_id).unwrap();

                let old_scope = self.current_scope;
                self.current_scope = def.scope() + 1;

                let params = fun_decl
                    .params
                    .iter()
                    .map(|p| hir::TypedIdent {
                        name: hir::Ident::from_ast(&p.name, self.scope_tree, self.current_scope),
                        type_annotation: self.lower_type(&p.type_annotation),
                    })
                    .collect();

                let generics = fun_decl
                    .generics
                    .iter()
                    .map(|g| hir::Ident::from_ast(&g, self.scope_tree, self.current_scope))
                    .collect();

                let body = self.lower_block_expr(&fun_decl.body);
                self.function_bodies.insert(def_id, body.clone());

                let return_type = self.lower_type(&fun_decl.return_type);

                self.current_scope = old_scope;

                HirNode::new(
                    hir::Stmt::FunDecl(hir::FunDeclStmt {
                        ident: hir::Ident::from_ast(&fun_decl.ident, self.scope_tree, self.current_scope),
                        params,
                        generics,
                        return_type,
                        body,
                    }),
                    stmt.span,
                )
            }
            ast::Stmt::StructDecl(struct_decl) => {
                let def_id = self.scope_tree.resolve_name(self.current_scope, &struct_decl.ident.node).unwrap();
                let def = self.def_map.get(def_id).unwrap();

                let old_scope = self.current_scope;
                self.current_scope = def.scope();

                let field_def_ids = def.fields();

                let fields = struct_decl
                    .fields
                    .iter()
                    .map(|f| {
                        let annotation = self.lower_type(&f.type_annotation);
                        let field_def_id = field_def_ids
                            .iter()
                            .find(|def_id| f.name.node == self.def_map.get(**def_id).unwrap().name())
                            .unwrap();

                        hir::TypedIdent {
                            name: hir::Ident::new(&f.name.node, f.name.span, *field_def_id),
                            type_annotation: annotation,
                        }
                    })
                    .collect();

                self.current_scope = old_scope;
                HirNode::new(
                    hir::Stmt::StructDecl(hir::StructDeclStmt {
                        ident: hir::Ident::from_ast(&struct_decl.ident, self.scope_tree, self.current_scope),
                        fields,
                    }),
                    stmt.span,
                )
            }
            ast::Stmt::While(while_stmt) => HirNode::new(
                hir::Stmt::While(hir::WhileStmt {
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
                    while_body_stmts.push(HirNode::new(
                        hir::Stmt::ExprStmtNode(hir::ExprStmt {
                            expr: self.lower_expr(incr),
                        }),
                        incr.span,
                    ))
                }
                let while_stmt = hir::Stmt::While(hir::WhileStmt {
                    condition: self.lower_expr(&for_stmt.condition),
                    body: HirNode::new(
                        hir::BlockExpr {
                            statements: while_body_stmts,
                            expr: None,
                        },
                        for_stmt.body.span,
                    ),
                });

                block_stmts.push(HirNode::new(while_stmt, stmt.span));
                HirNode::new(
                    hir::Stmt::ExprStmtNode(hir::ExprStmt {
                        expr: HirNode::new(
                            hir::Expr::Block(hir::BlockExpr {
                                statements: block_stmts,
                                expr: None,
                            }),
                            stmt.span,
                        ),
                    }),
                    stmt.span,
                )
            }

            ast::Stmt::Return(return_stmt) => HirNode::new(
                hir::Stmt::Return(hir::ReturnStmt {
                    expr: return_stmt.expr.as_ref().map(|e| self.lower_expr(e)),
                }),
                stmt.span,
            ),
        }
    }

    fn lower_expr(&mut self, expr: &AstNode<ast::Expr>) -> HirNode<hir::Expr> {
        match &expr.node {
            ast::Expr::Literal(literal_expr) => {
                let lit = match literal_expr {
                    ast::LiteralExpr::Nil => hir::LiteralExpr::Nil,
                    ast::LiteralExpr::Float(f) => hir::LiteralExpr::Float(*f),
                    ast::LiteralExpr::Int(i) => hir::LiteralExpr::Int(*i),
                    ast::LiteralExpr::String(s) => hir::LiteralExpr::String(s.clone()),
                    ast::LiteralExpr::Bool(b) => hir::LiteralExpr::Bool(*b),
                    ast::LiteralExpr::VecLiteral(v) => hir::LiteralExpr::VecLiteral(v.iter().map(|e| self.lower_expr(e)).collect()),
                };
                HirNode::new(hir::Expr::Literal(lit), expr.span)
            }
            ast::Expr::Unary(unary_expr) => {
                let op = match unary_expr.op.node {
                    ast::UnaryOp::Minus => hir::UnaryOp::Minus,
                    ast::UnaryOp::Bang => hir::UnaryOp::Bang,
                };
                HirNode::new(
                    hir::Expr::Unary(hir::UnaryExpr {
                        op: HirNode::new(op, unary_expr.op.span),
                        expr: Box::from(self.lower_expr(&unary_expr.expr)),
                    }),
                    expr.span,
                )
            }
            ast::Expr::Binary(binary_expr) => {
                let op = match binary_expr.op.node {
                    ast::BinaryOp::Minus => hir::BinaryOp::Minus,
                    ast::BinaryOp::Plus => hir::BinaryOp::Plus,
                    ast::BinaryOp::Star => hir::BinaryOp::Star,
                    ast::BinaryOp::Slash => hir::BinaryOp::Slash,
                    ast::BinaryOp::Greater => hir::BinaryOp::Greater,
                    ast::BinaryOp::GreaterEqual => hir::BinaryOp::GreaterEqual,
                    ast::BinaryOp::Less => hir::BinaryOp::Less,
                    ast::BinaryOp::LessEqual => hir::BinaryOp::LessEqual,
                    ast::BinaryOp::EqualEqual => hir::BinaryOp::EqualEqual,
                    ast::BinaryOp::BangEqual => hir::BinaryOp::BangEqual,
                };

                HirNode::new(
                    hir::Expr::Binary(hir::BinaryExpr {
                        op: HirNode::new(op, binary_expr.op.span),
                        left: Box::new(self.lower_expr(&binary_expr.left)),
                        right: Box::new(self.lower_expr(&binary_expr.right)),
                    }),
                    expr.span,
                )
            }
            ast::Expr::Grouping(grouping) => HirNode::new(hir::Expr::Grouping(Box::new(self.lower_expr(grouping))), expr.span),
            ast::Expr::Variable(variable) => HirNode::new(
                hir::Expr::Variable(hir::Ident::from_ast(variable, self.scope_tree, self.current_scope)),
                expr.span,
            ),
            ast::Expr::Assign(assign_expr) => HirNode::new(
                hir::Expr::Assign(hir::AssignExpr {
                    target: hir::Ident::from_ast(&assign_expr.target, self.scope_tree, self.current_scope),
                    value: Box::new(self.lower_expr(&assign_expr.value)),
                }),
                expr.span,
            ),
            ast::Expr::Logical(logical_expr) => {
                let op = match logical_expr.op.node {
                    ast::LogicalOp::And => hir::LogicalOp::And,
                    ast::LogicalOp::Or => hir::LogicalOp::Or,
                };
                HirNode::new(
                    hir::Expr::Logical(hir::LogicalExpr {
                        op: HirNode::new(op, logical_expr.op.span),
                        left: Box::new(self.lower_expr(&logical_expr.left)),
                        right: Box::new(self.lower_expr(&logical_expr.right)),
                    }),
                    expr.span,
                )
            }
            ast::Expr::Call(call_expr) => HirNode::new(
                hir::Expr::Call(hir::CallExpr {
                    callee: Box::new(self.lower_expr(&call_expr.callee)),
                    arguments: call_expr.arguments.iter().map(|arg| self.lower_expr(arg)).collect(),
                }),
                expr.span,
            ),
            ast::Expr::Lambda(lambda_expr) => HirNode::new(
                hir::Expr::Lambda(hir::LambdaExpr {
                    parameters: lambda_expr
                        .parameters
                        .iter()
                        .map(|p| hir::TypedIdent {
                            name: hir::Ident::from_ast(&p.name, self.scope_tree, self.current_scope),
                            type_annotation: self.lower_type(&p.type_annotation),
                        })
                        .collect(),
                    body: Box::new(self.lower_block_expr(&lambda_expr.body)),
                    return_type: self.lower_type(&lambda_expr.return_type),
                }),
                expr.span,
            ),
            ast::Expr::Block(block) => HirNode::new(
                hir::Expr::Block(self.lower_block_expr(&AstNode::new(block.clone(), expr.span)).node),
                expr.span,
            ),
            ast::Expr::If(if_expr) => HirNode::new(
                hir::Expr::If(hir::IfExpr {
                    condition: Box::new(self.lower_expr(&if_expr.condition)),
                    then_branch: self.lower_block_expr(&if_expr.then_branch),
                    else_branch: if_expr.else_branch.as_ref().map(|else_branch| self.lower_block_expr(else_branch)),
                }),
                expr.span,
            ),
            ast::Expr::MethodCall(method_call) => HirNode::new(
                hir::Expr::MethodCall(hir::MethodCallExpr {
                    receiver: Box::new(self.lower_expr(&method_call.receiver)),
                    method: hir::Ident::from_ast(&method_call.method, self.scope_tree, self.current_scope),
                    arguments: method_call.arguments.iter().map(|arg| self.lower_expr(arg)).collect(),
                }),
                expr.span,
            ),
            ast::Expr::StructInit(struct_init) => {
                let struct_def_id = self.scope_tree.resolve_name(self.current_scope, &struct_init.name.node).unwrap();
                let def = self.def_map.get(struct_def_id).unwrap();
                let field_def_ids = def.fields();

                let mut lowered_fields: Vec<(hir::Ident, HirNode<hir::Expr>)> = vec![];

                for field in &struct_init.fields {
                    let field_def_id = field_def_ids
                        .iter()
                        .find(|def_id| self.def_map.get(**def_id).unwrap().name() == field.0.node)
                        .unwrap();

                    let field_def = self.def_map.get(*field_def_id).unwrap();
                    let ident = hir::Ident::new(&field_def.name(), field_def.span(), field_def.def_id());
                    let lowered_expr = self.lower_expr(&field.1);
                    lowered_fields.push((ident, lowered_expr));
                }
                HirNode::new(
                    hir::Expr::StructInit(hir::StructInitExpr {
                        name: hir::Ident::from_ast(&struct_init.name, self.scope_tree, self.current_scope),
                        fields: lowered_fields,
                    }),
                    expr.span,
                )
            }
            ast::Expr::FieldAccess(field_access) => HirNode::new(
                hir::Expr::FieldAccess(hir::FieldAccessExpr {
                    receiver: Box::new(self.lower_expr(&field_access.receiver)),
                    field: HirNode::new(field_access.field.node.clone(), field_access.field.span),
                }),
                expr.span,
            ),
            ast::Expr::FieldAssign(field_assign) => HirNode::new(
                hir::Expr::FieldAssign(hir::FieldAssignExpr {
                    receiver: Box::new(self.lower_expr(&field_assign.receiver)),
                    field: HirNode::new(field_assign.field.node.clone(), field_assign.field.span),
                    value: Box::new(self.lower_expr(&field_assign.value)),
                }),
                expr.span,
            ),
        }
    }

    fn lower_block_expr(&mut self, block: &AstNode<ast::BlockExpr>) -> HirNode<hir::BlockExpr> {
        HirNode::new(
            hir::BlockExpr {
                statements: block.node.statements.iter().map(|s| self.lower_stmt(s)).collect(),
                expr: block.node.expr.as_ref().map(|e| Box::new(self.lower_expr(e))),
            },
            block.span,
        )
    }

    fn lower_type(&mut self, ty: &AstNode<ast::UnresolvedType>) -> ResolvedType {
        match &ty.node {
            ast::UnresolvedType::Named(_) => {
                let def_id = self.resolution_map.get(ty.node_id);
                ResolvedType::Named(def_id)
            }
            ast::UnresolvedType::Function { params, return_type } => {
                let param_types = params.iter().map(|p| self.lower_type(p)).collect();
                let return_type = Box::new(self.lower_type(return_type));
                ResolvedType::Function {
                    params: param_types,
                    return_type,
                }
            }
            ast::UnresolvedType::Generic { base, args } => {
                let base_type = self.lower_type(base);
                let arg_types = args.iter().map(|a| self.lower_type(a)).collect();
                match base_type {
                    ResolvedType::Named(def_id) => ResolvedType::Generic {
                        base: def_id,
                        args: arg_types,
                    },
                    _ => panic!(),
                }
            }
        }
    }
}
