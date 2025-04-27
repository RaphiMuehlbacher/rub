use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::values::{BasicValue, IntValue};
use inkwell::{builder::Builder, values::BasicValueEnum};

use crate::ast::{
    AssignExpr, BinaryExpr, CallExpr, Expr, LambdaExpr, LiteralExpr, LogicalExpr, Typed, UnaryExpr,
};

pub struct CodeGen<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
}

impl<'ctx> CodeGen<'ctx> {
    pub fn new(context: &'ctx Context, module_name: &str) -> Self {
        let builder = context.create_builder();
        let module = context.create_module(module_name);

        Self {
            context,
            module,
            builder,
        }
    }

    fn codegen_expr(&self, expr: &Expr) -> IntValue<'ctx> {
        match expr {
            Expr::Literal(lit) => self.literal(lit),
            Expr::Lambda(lambda) => self.lambda(lambda),
            Expr::Unary(unary) => self.unary(unary),
            Expr::Grouping(grouping) => self.grouping(grouping),
            Expr::Assign(assign) => self.assign(assign),
            Expr::Variable(variable) => self.variable(variable),
            Expr::Binary(binary) => self.binary(binary),
            Expr::Call(call) => self.call(call),
            Expr::Logical(logical) => self.logical(logical),
        }
    }

    fn literal(&self, lit: &Typed<LiteralExpr>) -> BasicValueEnum<'ctx> {
        match &lit.node {
            LiteralExpr::Number(num) => {
                let f32_type = self.context.f32_type();
                f32_type.const_float(*num).as_basic_value_enum()
            }
            LiteralExpr::String(s) => {
                let string = self.context.const_string(s.as_bytes(), true);
                string.as_basic_value_enum()
            }
            LiteralExpr::Bool(bool_lit) => {
                let bool_type = self.context.bool_type();
                bool_type
                    .const_int(*bool_lit as u64, false)
                    .as_basic_value_enum()
            }
            LiteralExpr::Nil => {
                todo!()
            }
        }
    }

    fn lambda(&self, lambda: &Typed<LambdaExpr>) -> IntValue<'ctx> {
        todo!()
    }

    fn unary(&self, unary: &Typed<UnaryExpr>) -> IntValue<'ctx> {
        todo!()
    }

    fn grouping(&self, expr: &Typed<Box<Expr>>) -> IntValue<'ctx> {
        todo!()
    }

    fn assign(&self, assign: &Typed<AssignExpr>) -> IntValue<'ctx> {
        todo!()
    }

    fn variable(&self, variable: &Typed<String>) -> IntValue<'ctx> {
        todo!()
    }

    fn binary(&self, binary: &Typed<BinaryExpr>) -> IntValue<'ctx> {
        todo!()
    }

    fn call(&self, call: &Typed<CallExpr>) -> IntValue<'ctx> {
        todo!()
    }

    fn logical(&self, logical: &Typed<LogicalExpr>) -> IntValue<'ctx> {
        todo!()
    }
}
